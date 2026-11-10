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

const dist = resolve(process.argv[2] ?? 'wasm/dist');
const build = JSON.parse(readFileSync(`${dist}/amaya-build.json`, 'utf8'));

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
];
const cases = process.argv[3] ? JSON.parse(readFileSync(process.argv[3], 'utf8')) : builtinCases;

const t0 = performance.now();
const pyodide = await loadPyodide();
await pyodide.loadPackage(`${dist}/${build.wheel}`);
const solve = pyodide.pyimport('amaya.web').solve;
console.log(`boot+install: ${((performance.now() - t0) / 1000).toFixed(2)} s, wheel ${build.wheel}`);

let failures = 0;
for (const c of cases) {
  const result = solve(c.smt2, pyodide.toPy(c.args ?? ['--fast'])).toJs({ dict_converter: Object.fromEntries });
  const problems = [];
  if (c.stderrIncludes && !result.stderr.includes(c.stderrIncludes)) problems.push(`stderr lacks ${c.stderrIncludes}`);
  const ok = (c.expected === undefined || result.answer === c.expected) && !problems.length;
  if (!ok) failures += 1;
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${c.name}: answer=${result.answer} expected=${c.expected} ` +
              `${result.seconds.toFixed(2)} s${result.error ? ' error=' + result.error : ''}` +
              `${problems.length ? ' problems: ' + problems.join(', ') : ''}`);
}
console.log(failures ? `${failures} failure(s)` : 'all ok');
process.exit(failures ? 1 : 0);
