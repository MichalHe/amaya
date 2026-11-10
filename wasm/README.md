# WebAssembly build (Pyodide)

This directory builds Amaya for WebAssembly so that it runs on a static web page. Python runs on
[Pyodide](https://pyodide.org) (CPython compiled to WebAssembly). The MTBDD backend
(`mtbdd-backend/`) and sylvan are compiled with Emscripten into the Python extension module
`amaya.libamaya`, so `--fast` (MTBDD backend + Hopcroft minimisation) and the native backend both work.

| Artefact (in `wasm/dist/`) | Purpose |
|---|---|
| `amaya-<version>-cp313-cp313-pyemscripten_2025_0_wasm32.whl` | Amaya package with the compiled backend (about 400 kB) |
| `amaya.js` | ES module with the browser API (`Amaya` class) |
| `amaya-worker.js` | Web Worker that runs Pyodide and Amaya off the main thread |
| `graphviz-*.whl`, `dd-*.whl`, `astutils-*.whl`, `ply-*.whl` | Pure-Python packages for exporting automata (about 160 kB), loaded on first use |
| `amaya-build.json` | Names of the wheels and the Pyodide/sylvan versions they were built for |
| `index.html` | Demo page |

## Building

Requirements: `git`, `rsync`, a Python 3.13 interpreter with `pyodide-build` installed, and a Python with
`pip` (any version; it builds the pure-Python wheels for exporting automata). The build script installs the
matching Pyodide cross-build environment and Emscripten SDK on first use (into `wasm/build/xbuildenv` unless
`PYODIDE_XBUILDENV_PATH` is set).

```sh
uv venv -p 3.13 .venv-wasm && uv pip install -p .venv-wasm/bin/python pyodide-build
PYODIDE_CLI=.venv-wasm/bin/pyodide ./wasm/build.sh
```

| Variable | Default | Meaning |
|---|---|---|
| `PYODIDE_VERSION` | `0.29.5` | Pyodide release to build for; the page loads the same release (recorded in `amaya-build.json`) |
| `PYODIDE_CLI` | `pyodide` | the `pyodide-build` CLI |
| `PYODIDE_XBUILDENV_PATH` | `wasm/build/xbuildenv` | location of the cross-build environment and Emscripten SDK |
| `SYLVAN_VERSION` | `v1.5.0` | sylvan tag, cloned into `wasm/build/` |
| `HOST_PYTHON` | `python3` | Python with `pip` used to build the graphviz/dd wheels (cached in `wasm/build/wheels`) |
| `AMAYA_WASM_DEBUG` | unset | if set, compile with `-g2 -O1` |

The build stages a source tree in `wasm/build/stage` (the `amaya` package, `run-amaya.py` as
`amaya/_cli.py`, the backend sources and sylvan's `src/`) and runs `pyodide build` on it with
`wasm/packaging/setup.py`. `wasm/packaging/amaya_wasm_compat.h` is force-included into every translation
unit; it replaces x86 inline assembly in Lace and makes sylvan use `__thread` thread-locals (its
pthread-key fallback truncates 64-bit values on 32-bit targets).

## Using it on a page

Serve `wasm/dist/` (or copy its files next to your page) with any static file server. No special headers
are needed: Amaya runs single-threaded and does not use `SharedArrayBuffer`. Pyodide itself is loaded from
the jsDelivr CDN unless `pyodideIndexURL` points to a self-hosted copy of the same release.

```js
import { Amaya, AmayaTimeoutError } from './amaya.js';

const amaya = new Amaya({ memoryMB: 256 });       // memoryMB: sylvan node table + cache, default 256
await amaya.init();                                // downloads Pyodide and the wheel (a few seconds)
const result = await amaya.solve(smt2Text, {
  args: ['--fast'],                                // CLI options before the mode, as for run-amaya.py
  modeArgs: ['-p'],                                // options after `get-sat`, e.g. -p prints a model
  timeoutMs: 30000,                                // stops the worker; the next call starts a new one
});
// result = {answer: 'sat'|'unsat'|'unknown'|null, error, exit_code, stdout, stderr, seconds, argv}
```

`mode: 'convert', modeArgs: ['-f', 'smt2']` runs `convert` instead of `get-sat`.

From Python inside Pyodide the same entry point is `amaya.web.solve(smt2_text, args, mode, mode_args)`.

**Updating a deployment.** Static hosts let browsers cache files (GitHub Pages for 10 minutes), and a page
must not mix files of two builds. The wheel's version carries a hash of its sources
(`amaya-0.0.0+wasm.<hash>-….whl`), `amaya-build.json` is revalidated on every load, and `amaya.js` loads
the worker as `amaya-worker.js?v=<buildId>`. The demo page imports `amaya.js?v=<buildId>` (stamped by
`build.sh`); a page of your own should do the same, e.g. read `buildId` from `amaya-build.json` and import
`amaya.js?v=${buildId}`, or be served with headers that make browsers revalidate `amaya.js`.

### Exporting automata

`exportAutomata: 'dot' | 'vtf' | 'mata'` returns every automaton built by the decision procedure, exactly as
`run-amaya.py get-sat -o DIR --output-format FORMAT` writes them:

```js
const result = await amaya.solve(smt2Text, { args: ['--fast'], exportAutomata: 'dot' });
result.automata   // [{id, operation, format, name, text, states, transitions}, ...] ordered by operation id;
                  // the last one is the automaton of the whole formula. `transitions` counts edges for dot.
result.trace      // DOT graph of the operations (an edge leads from a result to its operands)
result.variables  // {variable id: SMT name}; tracks are labelled with variable ids, in increasing order
```

The first such call installs `graphviz` and `dd` into the worker (they are pure Python and are only needed
for exporting). The demo page lays the DOT output out with [viz.js](https://github.com/mdaines/viz-js)
(Graphviz compiled to WebAssembly, loaded from jsDelivr when the first graph is shown); automata with more
than 150 states or 600 edges are only laid out on request because Graphviz runs on the main thread. VTF and
Mata are shown as text; every automaton can be downloaded. The other export options of `get-sat`
(`--colorize-dot`, `--vis-only-free-vars`) can be passed in `modeArgs`.

## Tests

```sh
npm install pyodide@0.29.5 puppeteer-core
node wasm/test/node-smoke.mjs wasm/dist                       # Pyodide under Node.js
python3 -m http.server -d wasm/dist 8000 &
CHROME=/usr/bin/google-chrome node wasm/test/browser-smoke.mjs http://localhost:8000/   # headless Chrome
```

`node-smoke.mjs` also exports automata in all three formats, installing the export packages only after
Amaya has been used without them (as the worker does). `browser-smoke.mjs` solves the demo examples, checks
that a timeout stops the solver and that the page recovers, and that exported automata and the operation trace
are drawn.

## Limitations

- `--use-dpllt-automata` and `--use-toplevel-sat` need `python-sat`, which is not available for Pyodide;
  they report an import error.
- sylvan's tables are allocated up front (in WebAssembly `mmap` allocates eagerly), so `memoryMB` is the
  amount of memory reserved, not an upper bound reached gradually. Inputs that need more report
  `MemoryError: std::bad_alloc`.
- A WebAssembly computation cannot be interrupted; `timeoutMs` terminates the worker, so the next call
  pays the start-up cost (about 2 s) again.
- Options that change process-wide backend state (for example `--use-bit-sets`) stay in effect for the
  lifetime of the worker.
