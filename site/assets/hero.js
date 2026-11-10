/*
 * The automaton on the landing page: Amaya's minimal automaton for  ∃k. x = 3k + 1  (x mod 3 = 1), run on the
 * binary encoding of a number the visitor types.
 *
 * AUTOMATON is Amaya's own output, copied verbatim:
 *
 *   python3 run-amaya.py --fast get-sat -o out --output-format vtf residue.smt2    # out/3-minimization.vtf
 *
 * where residue.smt2 asserts (exists ((k Int)) (= x (+ (* 3 k) 1))). Symbols have one bit per variable, x
 * first; the bit of k is a don't-care ('x') after k has been projected away. Words encode integers least
 * significant bit first in two's complement, the last bit being the sign. site/test/hero.mjs checks that the
 * automaton accepts exactly the numbers congruent to 1 modulo 3.
 */

export const FORMULA = '∃k. x = 3k + 1';

export const AUTOMATON = `@NFA
%States 0 1 2 3 4
%Initial 0
%Final 3 4
%Symbol-Vars 2

0 0x 2
0 1x 1
1 0x 3
1 1x 0
2 0x 0
2 1x 4
3 0x 3
3 1x 0
4 0x 0
4 1x 4
`;

/** The automaton as {initial, final: Set, states: [], delta: Map 'state,bit' -> state} (deterministic). */
export function parseAutomaton(vtf = AUTOMATON) {
  const field = (name) => vtf.match(new RegExp(`^%${name} (.*)$`, 'm'))[1].split(/\s+/).map(Number);
  const delta = new Map();
  for (const [, source, xBit, target] of vtf.matchAll(/^(\d+) ([01x])[01x] (\d+)$/gm)) {
    for (const bit of xBit === 'x' ? [0, 1] : [Number(xBit)]) {
      const key = `${source},${bit}`;
      if (delta.has(key) && delta.get(key) !== Number(target)) throw new Error(`not deterministic: ${key}`);
      delta.set(key, Number(target));
    }
  }
  return { initial: field('Initial')[0], final: new Set(field('Final')), states: field('States'), delta };
}

/** The shortest two's-complement encoding of n, least significant bit first; the last bit is the sign. */
export function encode(n) {
  let width = 1;
  while (!(-(2 ** (width - 1)) <= n && n < 2 ** (width - 1))) width += 1;
  const bits = [];
  for (let i = 0; i < width; i += 1) bits.push(Number((BigInt(n) >> BigInt(i)) & 1n));
  return bits;
}

/** The run of the automaton on the bits: [{state, bit, next}], and whether it ends in a final state. */
export function run(automaton, bits) {
  const steps = [];
  let state = automaton.initial;
  for (const bit of bits) {
    const next = automaton.delta.get(`${state},${bit}`);
    steps.push({ state, bit, next });
    state = next;
  }
  return { steps, accepted: automaton.final.has(state), last: state };
}

// ---- drawing ----

const SVG = 'http://www.w3.org/2000/svg';
const RADIUS = 21;
// Hand-placed layout of the five states, and the control points of the edges (quadratic Bézier curves).
const POSITIONS = { 0: [120, 150], 1: [270, 64], 2: [270, 236], 3: [430, 64], 4: [430, 236] };
const CURVES = {
  '0,1': [175, 70], '1,0': [225, 135],
  '0,2': [175, 230], '2,0': [225, 165],
  '1,3': null, '2,4': null,
  '3,0': [300, 128], '4,0': [300, 172],
};
const LOOPS = { 3: 'up', 4: 'down' };
// Where labels sit: t along the curve (default the middle), and on which side (1: outside the bend, -1: inside),
// so that the labels of the edges into q0 do not land on each other's curves.
const LABELS = { '3,0': { t: 0.3 }, '4,0': { t: 0.3 }, '1,0': { side: -1 }, '2,0': { side: -1 } };

function element(name, attributes = {}, parent = null) {
  const node = document.createElementNS(SVG, name);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
  if (parent) parent.append(node);
  return node;
}

function towards([x, y], [tx, ty], distance) {
  const length = Math.hypot(tx - x, ty - y);
  return [x + ((tx - x) / length) * distance, y + ((ty - y) / length) * distance];
}

/** Path and label position of an edge between two different states. */
function edgeGeometry(source, target) {
  const from = POSITIONS[source], to = POSITIONS[target];
  const control = CURVES[`${source},${target}`];
  if (!control) {
    const start = towards(from, to, RADIUS), end = towards(to, from, RADIUS + 2);
    const middle = [(start[0] + end[0]) / 2, (start[1] + end[1]) / 2];
    return { d: `M${start} L${end}`, label: [middle[0], middle[1] - 9] };
  }
  const start = towards(from, control, RADIUS), end = towards(to, control, RADIUS + 2);
  // The label sits beside the point at t of the curve, by default on the outer side of the bend.
  const { t = 0.5, side = 1 } = LABELS[`${source},${target}`] ?? {};
  const at = (i) => (1 - t) ** 2 * start[i] + 2 * (1 - t) * t * control[i] + t ** 2 * end[i];
  const tangent = (i) => 2 * (1 - t) * (control[i] - start[i]) + 2 * t * (end[i] - control[i]);
  const point = [at(0), at(1)];
  const length = Math.hypot(tangent(0), tangent(1));
  let normal = [-tangent(1) / length, tangent(0) / length];
  if ((control[0] - point[0]) * normal[0] + (control[1] - point[1]) * normal[1] < 0) normal = [-normal[0], -normal[1]];
  const label = [point[0] + side * 11 * normal[0], point[1] + side * 11 * normal[1] + 4];
  return { d: `M${start} Q${control} ${end}`, label };
}

function loopGeometry(state) {
  const [x, y] = POSITIONS[state];
  const s = LOOPS[state] === 'up' ? -1 : 1;
  const a = [x - 11, y + s * 18], b = [x + 11, y + s * 18];
  return { d: `M${a} C${x - 34},${y + s * 62} ${x + 34},${y + s * 62} ${b}`, label: [x, y + s * 58 + (s > 0 ? 9 : -3)] };
}

/** Draw the automaton into the svg; returns lookups of the drawn states and edges ('state,bit'). */
function draw(svg, automaton) {
  const defs = element('defs', {}, svg);
  for (const id of ['hero-arrow', 'hero-arrow-active']) {
    const marker = element('marker', { id, viewBox: '0 0 10 10', refX: 8, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    element('path', { d: 'M0,0 L10,5 L0,10 z', class: id }, marker);
  }
  const edges = new Map(), states = new Map();
  const edgeLayer = element('g', {}, svg), stateLayer = element('g', {}, svg);
  // Group the bits of parallel transitions (none here, but keep it general): one drawn edge per state pair.
  const pairs = new Map();
  for (const [key, target] of automaton.delta) {
    const [source, bit] = key.split(',').map(Number);
    const pair = `${source},${target}`;
    if (!pairs.has(pair)) pairs.set(pair, []);
    pairs.get(pair).push(bit);
  }
  for (const [pair, bits] of pairs) {
    const [source, target] = pair.split(',').map(Number);
    const geometry = source === target ? loopGeometry(source) : edgeGeometry(source, target);
    const group = element('g', { class: 'hero-edge' }, edgeLayer);
    element('path', { d: geometry.d, 'marker-end': 'url(#hero-arrow)' }, group);
    const label = element('text', { x: geometry.label[0], y: geometry.label[1], 'text-anchor': 'middle' }, group);
    label.textContent = bits.sort().join(',');
    for (const bit of bits) edges.set(`${source},${bit}`, group);
  }
  const [ix, iy] = POSITIONS[automaton.initial];
  element('path', { d: `M${ix - 62},${iy} L${ix - RADIUS - 2},${iy}`, class: 'hero-start', 'marker-end': 'url(#hero-arrow)' }, edgeLayer);
  for (const state of automaton.states) {
    const [x, y] = POSITIONS[state];
    const group = element('g', { class: 'hero-state' }, stateLayer);
    element('circle', { cx: x, cy: y, r: RADIUS }, group);
    if (automaton.final.has(state)) element('circle', { cx: x, cy: y, r: RADIUS - 4, class: 'hero-final' }, group);
    const text = element('text', { x, y: y + 5, 'text-anchor': 'middle' }, group);
    text.textContent = `q${state}`;
    states.set(state, group);
  }
  return { edges, states };
}

/**
 * Mount the widget: `root` contains an <svg>, an <input type="number">, a .hero-tape, a .hero-verdict and a
 * button.hero-replay.
 */
export function mountHero(root) {
  const automaton = parseAutomaton();
  const svg = root.querySelector('svg');
  const input = root.querySelector('input');
  const tape = root.querySelector('.hero-tape');
  const verdict = root.querySelector('.hero-verdict');
  const { edges, states } = draw(svg, automaton);
  const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  let timer = null;

  function mark(state, edge) {
    for (const group of states.values()) group.classList.remove('is-current');
    for (const group of edges.values()) group.classList.remove('is-taken');
    for (const path of svg.querySelectorAll('.hero-edge path')) path.setAttribute('marker-end', 'url(#hero-arrow)');
    if (state !== null) states.get(state).classList.add('is-current');
    if (edge) {
      edge.classList.add('is-taken');
      edge.querySelector('path').setAttribute('marker-end', 'url(#hero-arrow-active)');
    }
  }

  function start() {
    clearTimeout(timer);
    const n = Number(input.value);
    if (!Number.isInteger(n) || Math.abs(n) > 1e6) {
      verdict.textContent = 'Type an integer between −1 000 000 and 1 000 000.';
      verdict.className = 'hero-verdict';
      tape.replaceChildren();
      mark(automaton.initial, null);
      return;
    }
    const bits = encode(n);
    const result = run(automaton, bits);
    const cells = bits.map((bit, i) => {
      const cell = document.createElement('span');
      cell.className = i === bits.length - 1 ? 'hero-bit hero-sign' : 'hero-bit';
      cell.textContent = String(bit);
      cell.title = i === bits.length - 1 ? 'sign bit' : `bit ${i} (value ${2 ** i})`;
      return cell;
    });
    tape.replaceChildren(...cells);
    verdict.className = 'hero-verdict';
    const residue = ((n % 3) + 3) % 3, k = (n - residue) / 3;
    const finish = () => {
      mark(result.last, null);
      verdict.classList.add(result.accepted ? 'is-accepted' : 'is-rejected');
      verdict.textContent = result.accepted
        ? `Accepted: ${n} = 3·${k < 0 ? `(${k})` : k} + 1.`
        : `Rejected: ${n} mod 3 = ${residue}.`;
    };
    if (reducedMotion) {
      cells.forEach((cell) => cell.classList.add('is-read'));
      finish();
      return;
    }
    verdict.textContent = `Reading ${n}, least significant bit first…`;
    let i = 0;
    mark(automaton.initial, null);
    const step = () => {
      if (i === result.steps.length) { finish(); return; }
      const { state, bit, next } = result.steps[i];
      cells.forEach((cell, j) => cell.classList.toggle('is-read', j <= i));
      mark(next, edges.get(`${state},${bit}`));
      i += 1;
      timer = setTimeout(step, 650);
    };
    timer = setTimeout(step, 400);
  }

  input.addEventListener('input', start);
  root.querySelector('.hero-replay').addEventListener('click', start);
  start();
}
