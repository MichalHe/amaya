/*
 * The Amaya playground: examples, solving, and the automata viewer. Used by the demo page of the WebAssembly
 * bundle (wasm/web/index.html) and by the playground of the website (site/playground/index.html), which
 * provide the elements with the ids used below. The page's CSS must define the colours --fg (text, also used
 * for drawing graphs) and --track-bg (background of the track names in edge labels).
 */
import { Amaya, AmayaTimeoutError, dotWithVariableNames } from './amaya.js?v=7221fe2e501e';

// Graphviz compiled to WebAssembly, loaded the first time a graph is shown.
const VIZ_URL = 'https://cdn.jsdelivr.net/npm/@viz-js/viz@3.31.0/dist/viz.js';
// Larger automata are only laid out on request: Graphviz runs on the main thread and may take a while.
const LARGE_STATES = 150, LARGE_EDGES = 600;

// Each example: [name, what Amaya does with it, SMT-LIB2 body after (set-logic LIA)].
const examples = [
  ['Residue modulo 3 (sat)', '∃k. x = 3k + 1: an automaton for the equation, k projected away, then determinization and minimization.',
   '(declare-fun x () Int)\n(assert (exists ((k Int)) (= x (+ (* 3 k) 1))))'],
  ['Linear system (sat)', 'x + 2y = 7 with x, y ≥ 0 and x > y: an automaton per atom, intersected one by one.',
   '(declare-fun x () Int)\n(declare-fun y () Int)\n(assert (and (= (+ x (* 2 y)) 7) (>= x 0) (>= y 0) (> x y)))'],
  ['Even numbers (sat)', '∃k. x = 2k with 5 < x < 9: k is projected away, then the result is intersected with the bounds.',
   '(declare-fun x () Int)\n(assert (and (exists ((k Int)) (= x (* 2 k))) (> x 5) (< x 9)))'],
  ['Quantifiers (sat)', '∃x. y = 3x ∧ y > 10: an intersection, then x is projected away.',
   '(declare-fun y () Int)\n(assert (exists ((x Int)) (and (= y (* 3 x)) (> y 10))))'],
  ['Universal quantifier (sat)', '∀y. y > x ⇒ 2y > x + 1, evaluated as ¬∃y. ¬(…): complements, a union and a projection.',
   '(declare-fun x () Int)\n(assert (forall ((y Int)) (=> (> y x) (> (* 2 y) (+ x 1)))))'],
  ['Divisibility (sat)', '3 divides x + y but not x: two projections and a complement.',
   '(declare-fun x () Int)\n(declare-fun y () Int)\n(assert (and (exists ((k Int)) (= (+ x y) (* 3 k)))\n  (not (exists ((m Int)) (= x (* 3 m)))) (>= x 0) (>= y 0)))'],
  ['Odd and even (unsat)', 'x = 2k + 1 and x = 2m: two projections whose intersection accepts nothing.',
   '(declare-fun x () Int)\n(assert (and (exists ((k Int)) (= x (+ (* 2 k) 1))) (exists ((m Int)) (= x (* 2 m)))))'],
  ['Congruences (sat)', 'x mod 3 = 1 and x mod 4 = 2: mod introduces auxiliary variables, so many automata are built.',
   '(declare-fun x () Int)\n(assert (and (= (mod x 3) 1) (= (mod x 4) 2) (> x 0)))'],
  ['Frobenius coin problem (unsat)', 'Every n > 23 is 5a + 7b with a, b ≥ 0: projections, a complement and an intersection.',
   '(declare-fun n () Int)\n(assert (and (> n 23)\n  (not (exists ((a Int) (b Int)) (and (>= a 0) (>= b 0) (= n (+ (* 5 a) (* 7 b))))))))'],
  ['Interval (sat)', 'Preprocessing turns 3 < x < 5 into x = 4, so only one automaton is built.',
   '(declare-fun x () Int)\n(assert (and (> x 3) (< x 5)))'],
  ['Parity (unsat)', '2x = 7 has no integer solution; preprocessing decides this, so no automata are built.',
   '(declare-fun x () Int)\n(assert (= (* 2 x) 7))'],
].map(([name, about, body]) => ({ name, about, smt2: `(set-logic LIA)\n${body}\n(check-sat)\n` }));
const exampleSelect = document.getElementById('example');
const exampleAbout = document.getElementById('example-about');
const formula = document.getElementById('formula');
for (const { name } of examples) exampleSelect.add(new Option(name, name));
function showExample() {
  const example = examples.find(({ name }) => name === exampleSelect.value);
  formula.value = example.smt2;
  exampleAbout.textContent = example.about;
}
// ?example=<name>&automata=dot|vtf|mata preselects an example and the export format (links from the website).
const params = new URLSearchParams(location.search);
if (examples.some(({ name }) => name === params.get('example'))) exampleSelect.value = params.get('example');
if (['dot', 'vtf', 'mata'].includes(params.get('automata'))) document.getElementById('export').value = params.get('automata');
showExample();
exampleSelect.onchange = showExample;

const status = document.getElementById('status');
const answer = document.getElementById('answer');
const output = document.getElementById('output');
const run = document.getElementById('run');
let backendOutput = [];

const amaya = new Amaya({ onOutput: (stream, text) => backendOutput.push(text) });
const t0 = performance.now();
amaya.init().then((versions) => {
  status.textContent = `Ready in ${((performance.now() - t0) / 1000).toFixed(1)} s.`;
  document.getElementById('footer').textContent =
    `Python ${versions.python}, Pyodide ${versions.pyodide ?? '?'}, Amaya ${amaya.build.amayaCommit}, sylvan ${amaya.build.sylvanVersion}`;
  run.disabled = false;
}).catch((error) => { status.textContent = `Failed to load: ${error.message}`; });

run.onclick = async () => {
  run.disabled = true;
  answer.textContent = ''; answer.className = '';
  output.hidden = true; backendOutput = [];
  automataSection.hidden = true;
  status.textContent = 'Solving…';
  const args = document.getElementById('args').value.split(/\s+/).filter(Boolean);
  const timeoutMs = 1000 * Number(document.getElementById('timeout').value || 60);
  const modeArgs = document.getElementById('model').checked ? ['-p'] : [];
  const exportAutomata = document.getElementById('export').value || undefined;
  try {
    const result = await amaya.solve(formula.value, { args, modeArgs, timeoutMs, exportAutomata });
    answer.textContent = result.answer ?? 'no answer';
    answer.className = result.answer ?? '';
    status.textContent = result.error ? `Error: ${result.error}` : `Finished in ${result.seconds.toFixed(2)} s.`;
    const text = [result.stdout.trim(), result.stderr.trim(), backendOutput.join('\n').trim()].filter(Boolean).join('\n\n');
    if (text) { output.textContent = text; output.hidden = false; }
    if (exportAutomata) showAutomata(result);
  } catch (error) {
    status.textContent = error instanceof AmayaTimeoutError ? `${error.message}; the solver was stopped.` : `Error: ${error.message}`;
  } finally {
    run.disabled = false;
  }
};

// ---- automata viewer ----
const automataSection = document.getElementById('automata');
const automatonSelect = document.getElementById('automaton');
const automatonInfo = document.getElementById('automaton-info');
const graphBox = document.getElementById('graph');
const source = document.getElementById('source');
const graphButton = document.getElementById('view-graph');
const sourceButton = document.getElementById('view-source');
const zoomButton = document.getElementById('zoom');
const namesBox = document.getElementById('names');
let items = [];
let variables = {};
let variablesNote = '';
let view = 'graph';
let renderToken = 0;
let vizInstance = null;

function loadViz() {
  if (!vizInstance) {
    vizInstance = import(VIZ_URL).then((module) => module.instance());
    vizInstance.catch(() => { vizInstance = null; });
  }
  return vizInstance;
}

function showAutomata(result) {
  const automata = result.automata ?? [];
  items = automata.map((a) => ({
    ...a,
    label: `#${a.id} ${a.operation} (${a.states} states, ${a.transitions} ${a.format === 'dot' ? 'edges' : 'transitions'})`,
  }));
  if (result.trace) items.push({ label: 'operation trace', name: 'trace-info.dot', format: 'dot', text: result.trace });
  variables = result.variables ?? {};
  const byId = Object.entries(variables).sort((a, b) => Number(a[0]) - Number(b[0]));
  variablesNote = byId.length ? `Variable ids, in track order: ${byId.map(([id, name]) => `${id} = ${name}`).join(', ')}.` : '';
  automatonSelect.replaceChildren(...items.map((item, index) => new Option(item.label, String(index))));
  automataSection.hidden = false;
  automatonSelect.parentElement.parentElement.hidden = !automata.length;
  if (!automata.length) {
    automatonInfo.textContent = result.error ? 'No automata were built before the error.'
      : 'No automata were built: Amaya decided this formula without them (for example during preprocessing).';
    graphBox.hidden = source.hidden = true;
    return;
  }
  // Default to the last automaton built, i.e. the one for the whole formula.
  automatonSelect.value = String(Math.max(0, automata.length - 1));
  showSelected();
}

// What is shown and downloaded: DOT automata with the tracks labelled by variable names, if chosen.
function displayedText(item) {
  const hasTracks = item.format === 'dot' && item.states !== undefined;
  return hasTracks && namesBox.checked ? dotWithVariableNames(item.text, variables) : item.text;
}

function showSelected(force = false) {
  const item = items[Number(automatonSelect.value)];
  if (!item) {
    automatonInfo.textContent = 'No automata were built.';
    graphBox.hidden = source.hidden = true;
    return;
  }
  const isGraph = item.format === 'dot';
  const mode = isGraph ? view : 'source';
  graphButton.disabled = zoomButton.disabled = !isGraph;
  namesBox.disabled = !isGraph || item.states === undefined;
  graphButton.setAttribute('aria-pressed', String(mode === 'graph'));
  sourceButton.setAttribute('aria-pressed', String(mode === 'source'));
  automatonInfo.textContent = item.states === undefined
    ? 'Graph of the operations performed: an edge leads from a result to its operands.'
    : `${item.states} states, ${item.transitions} ${isGraph ? 'edges' : 'transitions'} (${item.name}). ${variablesNote}`;
  source.textContent = displayedText(item);
  source.hidden = mode !== 'source';
  graphBox.hidden = mode !== 'graph';
  if (mode === 'graph') renderGraph(item, force);
}

async function renderGraph(item, force) {
  const token = ++renderToken;
  const note = document.createElement('p');
  if (!force && (item.states > LARGE_STATES || item.transitions > LARGE_EDGES)) {
    const button = document.createElement('button');
    button.className = 'secondary';
    button.textContent = 'Render anyway';
    button.onclick = () => showSelected(true);
    note.append(`Large automaton (${item.states} states, ${item.transitions} edges): laying it out may take a while.`, button);
    graphBox.replaceChildren(note);
    return;
  }
  note.textContent = 'Rendering…';
  graphBox.replaceChildren(note);
  try {
    const viz = await loadViz();
    await new Promise((resolve) => requestAnimationFrame(() => setTimeout(resolve)));  // let "Rendering…" paint
    if (token !== renderToken) return;
    const style = getComputedStyle(document.documentElement);
    const fg = style.getPropertyValue('--fg').trim();
    const font = 'Helvetica,Arial,sans-serif';
    // Display only: the track-name cells use Graphviz "gray", which is unreadable on a dark background.
    const dot = displayedText(item).replaceAll('BGCOLOR="gray"', `BGCOLOR="${style.getPropertyValue('--track-bg').trim()}"`);
    const svg = viz.renderSVGElement(dot, {
      graphAttributes: { bgcolor: 'transparent' },
      nodeAttributes: { color: fg, fontcolor: fg, fontname: font },
      edgeAttributes: { color: fg, fontcolor: fg, fontname: font },
    });
    if (token === renderToken) graphBox.replaceChildren(svg);
  } catch (error) {
    if (token === renderToken) note.textContent = `Cannot render the graph: ${error.message ?? error}`;
  }
}

automatonSelect.onchange = () => showSelected();
// Redraw the graph in the colours of a new theme (the website's theme toggle, or the system setting).
const redraw = () => { if (!automataSection.hidden && !graphBox.hidden) showSelected(); };
document.addEventListener('amaya-theme-change', redraw);
window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', redraw);
namesBox.onchange = () => showSelected(true);
graphButton.onclick = () => { view = 'graph'; showSelected(); };
sourceButton.onclick = () => { view = 'source'; showSelected(); };
zoomButton.onclick = () => {
  const fit = graphBox.classList.toggle('fit');
  zoomButton.textContent = fit ? 'Actual size' : 'Fit width';
};
document.getElementById('download').onclick = () => {
  const item = items[Number(automatonSelect.value)];
  if (!item) return;
  const link = document.createElement('a');
  link.href = URL.createObjectURL(new Blob([displayedText(item)], { type: 'text/plain' }));
  link.download = item.name;
  link.click();
  setTimeout(() => URL.revokeObjectURL(link.href), 1000);
};
