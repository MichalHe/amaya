/*
 * Browser API for the WebAssembly build of Amaya.
 *
 *   import { Amaya } from './amaya.js';
 *   const amaya = new Amaya();                 // files are looked up next to amaya.js
 *   await amaya.init();                        // downloads Pyodide (CDN) and the Amaya wheel, ~2-5 s
 *   const result = await amaya.solve(smt2Text, { args: ['--fast'], timeoutMs: 30000 });
 *   console.log(result.answer);                // 'sat' | 'unsat' | 'unknown' | null (see result.error)
 *
 * Amaya runs in a Web Worker, so the page stays responsive. A timeout terminates the worker (the only way
 * to stop a running WebAssembly computation) and the next call starts a fresh one. No SharedArrayBuffer
 * is used, so any static file server works (no COOP/COEP headers needed).
 */

export const DEFAULT_PYODIDE_VERSION = '0.29.5';

export class AmayaTimeoutError extends Error {
  constructor(timeoutMs) {
    super(`Amaya did not finish within ${timeoutMs} ms`);
    this.name = 'AmayaTimeoutError';
  }
}

export class Amaya {
  /**
   * @param {object} [options]
   * @param {string} [options.baseURL]          directory with amaya-worker.js, amaya-build.json and the wheel
   * @param {string} [options.pyodideIndexURL]  Pyodide distribution; must be the release the wheel was built for
   * @param {number} [options.memoryMB]         upper bound for the MTBDD node table and cache (default 256)
   * @param {(stream: string, text: string) => void} [options.onOutput]  output printed by the C/C++ backend
   */
  constructor(options = {}) {
    this.baseURL = options.baseURL ?? new URL('.', import.meta.url).href;
    this.pyodideIndexURL = options.pyodideIndexURL;
    this.memoryMB = options.memoryMB;
    this.onOutput = options.onOutput ?? (() => {});
    this.worker = null;
    this.ready = null;
    this.pending = new Map();
    this.nextId = 1;
    this.build = null;
    this.versions = null;
  }

  /** Start the worker and load Pyodide and the Amaya wheel. Safe to call repeatedly. */
  init() {
    if (!this.ready) {
      this.ready = this._start().catch((error) => {
        this._stopWorker();
        throw error;
      });
    }
    return this.ready;
  }

  async _start() {
    if (!this.build) {
      const response = await fetch(new URL('amaya-build.json', this.baseURL));
      if (!response.ok) throw new Error(`cannot load amaya-build.json: HTTP ${response.status}`);
      this.build = await response.json();
    }
    const pyodideVersion = this.build.pyodideVersion ?? DEFAULT_PYODIDE_VERSION;
    const indexURL = this.pyodideIndexURL ?? `https://cdn.jsdelivr.net/pyodide/v${pyodideVersion}/full/`;
    const env = {};
    if (this.memoryMB) env.AMAYA_SYLVAN_MEMORY_MB = String(this.memoryMB);

    this.worker = new Worker(new URL('amaya-worker.js', this.baseURL));
    this.worker.onmessage = (event) => this._onMessage(event.data);
    this.worker.onerror = (event) => this._failAll(new Error(event.message || 'Amaya worker failed'));

    const ready = new Promise((resolve, reject) => this.pending.set(0, { resolve, reject }));
    const visualizationWheelURLs = (this.build.visualizationWheels ?? []).map((wheel) => new URL(wheel, this.baseURL).href);
    this.worker.postMessage({ type: 'init', id: 0, pyodideIndexURL: indexURL,
                              wheelURL: new URL(this.build.wheel, this.baseURL).href, visualizationWheelURLs, env });
    this.versions = await ready;
    return this.versions;
  }

  _onMessage(message) {
    if (message.type === 'output') {
      this.onOutput(message.stream, message.text);
      return;
    }
    const id = message.type === 'ready' ? 0 : message.id ?? 0;
    const entry = this.pending.get(id);
    if (!entry) return;
    this.pending.delete(id);
    if (message.type === 'error') entry.reject(new Error(message.message));
    else entry.resolve(message.type === 'ready' ? message.versions : message.result);
  }

  _failAll(error) {
    for (const entry of this.pending.values()) entry.reject(error);
    this.pending.clear();
    this._stopWorker();
  }

  _stopWorker() {
    if (this.worker) this.worker.terminate();
    this.worker = null;
    this.ready = null;
  }

  /**
   * Run Amaya on SMT-LIB2 text.
   * @param {string} smt2
   * @param {object} [options]
   * @param {string[]} [options.args]      CLI options before the mode (default ['--fast'])
   * @param {string} [options.mode]        'get-sat' (default) or 'convert'
   * @param {string[]} [options.modeArgs]  options after the mode, e.g. ['-p'] to print a model, ['-f', 'smt2'] for convert
   * @param {number} [options.timeoutMs]   terminate the worker after this time (default: no limit)
   * @param {'dot'|'vtf'|'mata'} [options.exportAutomata]  also return every automaton built by the decision
   *        procedure, in this format (as `get-sat -o DIR --output-format FORMAT`). The first such call
   *        downloads the Python packages graphviz and dd (about 160 kB).
   * @returns {Promise<{answer: string|null, error: string|null, exit_code: number, stdout: string, stderr: string,
   *          seconds: number, automata?: Array<{id: number, operation: string, format: string, name: string,
   *          text: string, states: number, transitions: number}>, trace?: string|null,
   *          variables?: Object<string, string>}>}
   *          `automata` is ordered by operation id; the last one belongs to the whole formula. `trace` is the
   *          graph of the operations in DOT. `variables` maps variable ids (the track labels) to SMT names.
   */
  async solve(smt2, options = {}) {
    await this.init();
    const id = this.nextId++;
    const result = new Promise((resolve, reject) => this.pending.set(id, { resolve, reject }));
    this.worker.postMessage({ type: 'solve', id, smt2, args: options.args ?? ['--fast'],
                              mode: options.mode ?? 'get-sat', modeArgs: options.modeArgs ?? [],
                              exportAutomata: options.exportAutomata ?? null });
    if (!options.timeoutMs) return result;

    let timer;
    const timeout = new Promise((_, reject) => {
      timer = setTimeout(() => {
        this.pending.delete(id);
        this._failAll(new AmayaTimeoutError(options.timeoutMs));
        reject(new AmayaTimeoutError(options.timeoutMs));
      }, options.timeoutMs);
    });
    try {
      return await Promise.race([result, timeout]);
    } finally {
      clearTimeout(timer);
    }
  }

  /** Stop the worker; a later init()/solve() starts a new one. */
  terminate() {
    this._failAll(new Error('Amaya worker terminated'));
  }
}
