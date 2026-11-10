// Smoke test of the WebAssembly build under Node.js.
//
//   npm install pyodide@<version from wasm/dist/amaya-build.json>
//   node wasm/test/node-smoke.mjs wasm/dist [case-file.json]
//
// Without a case file, a few built-in formulas are solved. A case file is a JSON list of
// {"name": ..., "smt2": ..., "args": [...], "expected": "sat"|"unsat"} objects.
import { loadPyodide } from 'pyodide';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const dist = resolve(process.argv[2] ?? 'wasm/dist');
const build = JSON.parse(readFileSync(`${dist}/amaya-build.json`, 'utf8'));
const { dotWithVariableNames } = await import(pathToFileURL(`${dist}/amaya.js`).href);

const builtinCases = [
  { name: 'sat interval', args: ['--fast'], expected: 'sat',
    smt2: '(set-logic LIA)\n(declare-fun x () Int)\n(assert (and (> x 3) (< x 5)))\n(check-sat)\n' },
  { name: 'unsat parity', args: ['--fast'], expected: 'unsat',
    smt2: '(set-logic LIA)\n(declare-fun x () Int)\n(assert (= (* 2 x) 7))\n(check-sat)\n' },
  { name: 'quantified', args: ['--fast'], expected: 'sat',
    smt2: '(set-logic LIA)\n(declare-fun y () Int)\n(assert (exists ((x Int)) (and (= y (* 3 x)) (> y 10))))\n(check-sat)\n' },
  // Log output of --verbose goes to result.stderr, like everything else Amaya prints.
  { name: 'verbose log captured', args: ['--fast', '--verbose'], expected: 'sat', stderrIncludes: '(INFO)',
    smt2: '(set-logic LIA)\n(declare-fun x () Int)\n(assert (> x 3))\n(check-sat)\n' },
  { name: 'native backend', args: ['--backend', 'native'], expected: 'unsat',
    smt2: '(set-logic LIA)\n(declare-fun x () Int)\n(assert (and (> x 3) (< x 4)))\n(check-sat)\n' },
  ...['dot', 'vtf', 'mata'].map((format) => ({
    name: `export automata (${format})`, args: ['--fast'], expected: 'sat', exportAutomata: format,
    smt2: '(set-logic LIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n(assert (and (> x 3) (< x 5) (= (+ x y) 10)))\n(check-sat)\n',
  })),
  { name: 'export automata (native backend)', args: ['--backend', 'native'], expected: 'unsat', exportAutomata: 'dot',
    smt2: '(set-logic LIA)\n(declare-fun x () Int)\n(assert (and (> x 3) (< x 4)))\n(check-sat)\n' },
  // Track labels with names: a shadowed x gets its id appended, a quoted name is escaped for the HTML label.
  { name: 'export automata (variable names)', args: ['--fast'], expected: 'sat', exportAutomata: 'dot',
    checkLabels: (labels) => labels.has('a&lt;b &amp; c') && [...labels].filter((l) => /^x#\d+$/.test(l)).length === 2,
    smt2: '(set-logic LIA)\n(declare-fun x () Int)\n(declare-fun |a<b & c| () Int)\n' +
          '(assert (and (> x 0) (= (+ x |a<b & c|) 5) (exists ((x Int)) (and (< x 0) (> (+ x |a<b & c|) 0)))))\n(check-sat)\n' },
];
const header = { dot: 'digraph automaton', vtf: '@NFA', mata: '@NFA-explicit' };

// Checks of an exported run: automata ordered by id, in the requested format, the trace, and variable names.
function exportProblems(c, result) {
  const problems = [];
  const automata = result.automata ?? [];
  if (!automata.length) problems.push('no automata');
  if (automata.some((a, i) => i && a.id <= automata[i - 1].id)) problems.push('not ordered by id');
  if (automata.some((a) => a.format !== c.exportAutomata || !a.text.includes(header[c.exportAutomata]))) problems.push('wrong format');
  // An automaton may be empty (e.g. the intersection of contradicting constraints), but not all of them.
  if (automata.some((a) => !Number.isInteger(a.states)) || !automata.some((a) => a.states > 0)) problems.push('state count');
  if (!result.trace?.includes('digraph traceviz')) problems.push('no trace');
  if (!Object.values(result.variables ?? {}).includes('x')) problems.push('no variable names');
  const withEdges = automata.filter((a) => a.transitions > 0).at(-1);  // the last one may be empty
  if (c.exportAutomata === 'dot' && withEdges) {
    const named = dotWithVariableNames(withEdges.text, result.variables);
    const labels = new Set([...named.matchAll(/BGCOLOR="gray">(.*?):<\/TD>/g)].map((m) => m[1]));
    if (!labels.size || [...labels].some((label) => /^(Var\(id=)?\d+\)?$/.test(label))) problems.push(`track labels ${[...labels]}`);
    if (c.checkLabels && !c.checkLabels(labels)) problems.push(`unexpected labels ${[...labels]}`);
  }
  return problems;
}
const cases = process.argv[3] ? JSON.parse(readFileSync(process.argv[3], 'utf8')) : builtinCases;

const t0 = performance.now();
const pyodide = await loadPyodide();
await pyodide.loadPackage(`${dist}/${build.wheel}`, { messageCallback: () => {} });
// Like the web worker, install the packages for exporting automata only when the first export is requested,
// i.e. after amaya has been imported and used without them.
let visualizationLoaded = false;
const solve = pyodide.pyimport('amaya.web').solve;
console.log(`boot+install: ${((performance.now() - t0) / 1000).toFixed(2)} s, wheel ${build.wheel}`);

let failures = 0;
for (const c of cases) {
  if (c.exportAutomata && !visualizationLoaded) {
    await pyodide.loadPackage((build.visualizationWheels ?? []).map((wheel) => `${dist}/${wheel}`),
                              { messageCallback: () => {} });
    visualizationLoaded = true;
  }
  const kwargs = c.exportAutomata ? { export_automata: c.exportAutomata } : {};
  const result = solve.callKwargs(c.smt2, pyodide.toPy(c.args ?? ['--fast']), kwargs)
    .toJs({ dict_converter: Object.fromEntries });
  const problems = c.exportAutomata ? exportProblems(c, result) : [];
  if (c.stderrIncludes && !result.stderr.includes(c.stderrIncludes)) problems.push(`stderr lacks ${c.stderrIncludes}`);
  const ok = (c.expected === undefined || result.answer === c.expected) && !problems.length;
  if (!ok) failures += 1;
  const exported = c.exportAutomata ? ` automata=${result.automata?.length}` : '';
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${c.name}: answer=${result.answer} expected=${c.expected} ` +
              `${result.seconds.toFixed(2)} s${exported}${result.error ? ' error=' + result.error : ''}` +
              `${problems.length ? ' problems: ' + problems.join(', ') : ''}`);
}
console.log(failures ? `${failures} failure(s)` : 'all ok');
process.exit(failures ? 1 : 0);
