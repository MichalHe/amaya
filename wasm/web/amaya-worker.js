/*
 * Web Worker running Amaya (Python + the sylvan-based MTBDD backend compiled to WebAssembly) on Pyodide.
 * Use it through amaya.js; the message protocol is:
 *
 *   -> {type: 'init', pyodideIndexURL, wheelURL, env}
 *   <- {type: 'ready', versions}                      or {type: 'error', message}
 *   -> {type: 'solve', id, smt2, args, mode, modeArgs}
 *   <- {type: 'result', id, result}                   or {type: 'error', id, message}
 *   <- {type: 'output', stream, text}                 output written directly by C/C++ code (bypasses Python)
 *
 * `result` is the dictionary returned by amaya.web.solve: {answer, error, exit_code, stdout, stderr, seconds, argv}.
 */
/* global importScripts, loadPyodide */
let pyodide = null;
let amayaWeb = null;

function toJs(proxy) {
  const value = proxy.toJs({ dict_converter: Object.fromEntries });
  proxy.destroy();
  return value;
}

self.onmessage = async (event) => {
  const message = event.data;
  try {
    if (message.type === 'init') {
      importScripts(`${message.pyodideIndexURL}pyodide.js`);
      pyodide = await loadPyodide({
        indexURL: message.pyodideIndexURL,
        env: message.env || {},
        stdout: (text) => self.postMessage({ type: 'output', stream: 'stdout', text }),
        stderr: (text) => self.postMessage({ type: 'output', stream: 'stderr', text }),
      });
      await pyodide.loadPackage(message.wheelURL, { messageCallback: () => {} });
      amayaWeb = pyodide.pyimport('amaya.web');
      self.postMessage({ type: 'ready', versions: toJs(amayaWeb.version_info()) });
    } else if (message.type === 'solve') {
      if (!amayaWeb) throw new Error('worker is not initialised');
      const result = amayaWeb.solve(message.smt2, pyodide.toPy(message.args || []), message.mode || 'get-sat',
                                    pyodide.toPy(message.modeArgs || []));
      self.postMessage({ type: 'result', id: message.id, result: toJs(result) });
    }
  } catch (error) {
    self.postMessage({ type: 'error', id: message.id, message: String((error && error.message) || error) });
  }
};
