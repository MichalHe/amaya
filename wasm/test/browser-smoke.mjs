// Browser test of the static bundle in wasm/dist: drives the demo page in headless Chrome.
//
//   python3 -m http.server -d wasm/dist 8765 &
//   npm install puppeteer-core
//   CHROME=/usr/bin/google-chrome node wasm/test/browser-smoke.mjs http://localhost:8765/
//
// Solves every example of the demo page, checks the answers, and checks that a timeout stops the solver
// and that the page recovers afterwards.
import puppeteer from 'puppeteer-core';

// Click an element after scrolling it to the middle of the viewport, so that no sticky header covers it.
async function click(page, selector) {
  await page.$eval(selector, (element) => element.scrollIntoView({ block: 'center', inline: 'center' }));
  await page.click(selector);
}

const url = process.argv[2] ?? 'http://localhost:8765/';
// Answers of the demo examples (cross-checked with cvc5).
const expected = {
  'Residue modulo 3 (sat)': 'sat',
  'Linear system (sat)': 'sat',
  'Even numbers (sat)': 'sat',
  'Quantifiers (sat)': 'sat',
  'Universal quantifier (sat)': 'sat',
  'Divisibility (sat)': 'sat',
  'Odd and even (unsat)': 'unsat',
  'Congruences (sat)': 'sat',
  'Frobenius coin problem (unsat)': 'unsat',
  'Interval (sat)': 'sat',
  'Parity (unsat)': 'unsat',
};

const browser = await puppeteer.launch({
  executablePath: process.env.CHROME ?? '/usr/bin/google-chrome',
  headless: true,
  args: ['--no-sandbox'],
});
let failures = 0;
try {
  const page = await browser.newPage();
  page.on('pageerror', (error) => console.log('page error:', error.message));
  const requested = [];
  page.on('request', (request) => requested.push(request.url()));
  const t0 = Date.now();
  await page.goto(url);
  await page.waitForFunction(() => !document.getElementById('run').disabled, { timeout: 120000 });
  console.log(`page ready after ${((Date.now() - t0) / 1000).toFixed(1)} s: ` +
              await page.$eval('#status', (e) => e.textContent));
  console.log('footer:', await page.$eval('#footer', (e) => e.textContent));
  // Files that differ between builds are requested with the build id, so stale cached copies are not used.
  const versioned = ['playground.js', 'amaya.js', 'amaya-worker.js'].every((file) => requested.some((url) => url.includes(`/${file}?v=`)));
  console.log(`${versioned ? 'ok  ' : 'FAIL'} versioned URLs: ${requested.filter((url) => /(amaya|amaya-worker|playground)\.js|\.whl/.test(url)).map((url) => url.split('/').pop()).join(' ')}`);
  failures += versioned ? 0 : 1;

  async function solve(timeoutSeconds = 60) {
    await page.$eval('#timeout', (e, v) => { e.value = v; }, String(timeoutSeconds));
    await click(page, '#run');
    await page.waitForFunction(() => !document.getElementById('run').disabled, { timeout: 180000 });
    return {
      answer: await page.$eval('#answer', (e) => e.textContent),
      status: await page.$eval('#status', (e) => e.textContent),
    };
  }

  for (const [name, answer] of Object.entries(expected)) {
    await page.select('#example', name);
    const result = await solve();
    const ok = result.answer === answer;
    failures += ok ? 0 : 1;
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${name}: ${result.answer} (${result.status})`);
  }

  // A formula that does not finish quickly: the timeout must stop it and the page must recover.
  await page.$eval('#formula', (e) => {
    const n = 14;
    const vars = Array.from({ length: n }, (_, i) => `x${i}`);
    e.value = '(set-logic LIA)\n' + vars.map((v) => `(declare-fun ${v} () Int)`).join('\n') +
      `\n(assert (= (+ ${vars.map((v, i) => `(* ${2 * i + 3} ${v})`).join(' ')}) 1000003))` +
      `\n(assert (and ${vars.map((v) => `(>= ${v} 0)`).join(' ')}))\n(check-sat)\n`;
  });
  // Stopped with no answer: a run that finished within the time limit would not show that the timeout works.
  const slow = await solve(1);
  const stopped = /stopped/.test(slow.status) && slow.answer === '';
  console.log(`${stopped ? 'ok  ' : 'FAIL'} timeout: answer='${slow.answer}' status='${slow.status}'`);
  failures += stopped ? 0 : 1;

  await page.select('#example', 'Parity (unsat)');
  const after = await solve();
  const recovered = after.answer === 'unsat';
  console.log(`${recovered ? 'ok  ' : 'FAIL'} after timeout: ${after.answer} (${after.status})`);
  failures += recovered ? 0 : 1;

  // Exported automata: the graph of the last automaton is rendered (Graphviz from the CDN), the operation
  // trace can be shown, and a text format is displayed as source.
  await page.select('#export', 'dot');
  await page.select('#example', 'Quantifiers (sat)');
  const exported = await solve();
  await page.waitForSelector('#graph svg', { timeout: 60000 });
  const graph = await page.evaluate(() => {
    const select = document.getElementById('automaton');
    return { count: select.options.length, selected: select.selectedOptions[0]?.textContent,
             last: select.options[select.options.length - 2]?.textContent,
             nodes: document.querySelectorAll('#graph svg g.node').length };
  });
  const graphOk = exported.answer === 'sat' && graph.count > 2 && graph.selected === graph.last && graph.nodes > 0;
  console.log(`${graphOk ? 'ok  ' : 'FAIL'} automata graph: ${graph.count - 1} automata + trace, ` +
              `selected '${graph.selected}', ${graph.nodes} nodes drawn`);
  failures += graphOk ? 0 : 1;

  // Tracks are labelled with variable names by default, with ids when the box is unchecked.
  const trackLabels = () => page.$$eval('#graph svg text', (texts) => texts.map((t) => t.textContent).filter((t) => t.endsWith(':')));
  const named = await trackLabels();
  await click(page, '#names');
  await page.waitForFunction(() => [...document.querySelectorAll('#graph svg text')].some((t) => t.textContent.startsWith('Var(id=')));
  const ids = await trackLabels();
  await click(page, '#names');
  await page.waitForFunction(() => [...document.querySelectorAll('#graph svg text')].some((t) => t.textContent === 'y:'));
  const namesOk = named.includes('y:') && !named.some((t) => t.startsWith('Var(id=')) && ids.some((t) => t.startsWith('Var(id='));
  console.log(`${namesOk ? 'ok  ' : 'FAIL'} track labels: ${[...new Set(named)].join(' ')} / unchecked: ${[...new Set(ids)].join(' ')}`);
  failures += namesOk ? 0 : 1;

  await page.evaluate(() => {
    const select = document.getElementById('automaton');
    select.value = String(select.options.length - 1);
    select.dispatchEvent(new Event('change'));
  });
  await page.waitForFunction(() => document.querySelectorAll('#graph svg g.node').length > 0 &&
                                   /trace/.test(document.getElementById('automaton').selectedOptions[0].textContent));
  console.log('ok   operation trace rendered');

  await page.select('#export', 'vtf');
  await solve();
  const vtf = await page.evaluate(() => ({ hidden: document.getElementById('source').hidden,
                                           text: document.getElementById('source').textContent }));
  const vtfOk = !vtf.hidden && vtf.text.startsWith('@NFA');
  console.log(`${vtfOk ? 'ok  ' : 'FAIL'} automata as VTF: ${JSON.stringify(vtf.text.slice(0, 40))}`);
  failures += vtfOk ? 0 : 1;

  await page.select('#example', 'Parity (unsat)');
  await solve();
  const none = await page.$eval('#automaton-info', (e) => e.textContent);
  // The empty automaton selector and its buttons are hidden, not just left empty.
  const selectorShown = await page.$eval('#automaton', (e) => e.offsetParent !== null);
  const noneOk = /No automata were built: Amaya decided/.test(none) && !selectorShown;
  console.log(`${noneOk ? 'ok  ' : 'FAIL'} formula decided without automata (selector ${selectorShown ? 'shown' : 'hidden'}): ${none}`);
  failures += noneOk ? 0 : 1;

  // The API's worker life cycle: terminate() cancels a start-up in progress, and a canceled start-up cannot
  // stop the worker of a later one.
  const lifecycle = await page.evaluate(async () => {
    const { Amaya } = await import(new URL('amaya.js', location.href).href);
    const settle = (promise, ms) => Promise.race([promise.then(() => 'resolved', () => 'rejected'),
                                                  new Promise((resolve) => setTimeout(() => resolve('pending'), ms))]);
    // terminate() while amaya-build.json is being fetched.
    const a = new Amaya();
    const first = a.init();
    a.terminate();
    const duringFetch = await settle(first, 30000);
    const workerLeft = a.worker !== null;
    // terminate() while the worker starts, then init() at once.
    const b = new Amaya();
    const old = b.init();
    while (!b.worker) await new Promise((resolve) => setTimeout(resolve, 5));
    b.terminate();
    const fresh = b.init();
    const oldStartup = await settle(old, 30000);
    const freshStartup = await settle(fresh, 60000);
    const answer = freshStartup === 'resolved'
      ? (await b.solve('(set-logic LIA)\n(declare-fun x () Int)\n(assert (> x 3))\n(check-sat)\n', { timeoutMs: 30000 })).answer
      : null;
    b.terminate();
    return { duringFetch, workerLeft, oldStartup, freshStartup, answer };
  });
  const lifecycleOk = lifecycle.duringFetch === 'rejected' && !lifecycle.workerLeft && lifecycle.oldStartup === 'rejected' &&
    lifecycle.freshStartup === 'resolved' && lifecycle.answer === 'sat';
  console.log(`${lifecycleOk ? 'ok  ' : 'FAIL'} terminate() during start-up: ${JSON.stringify(lifecycle)}`);
  failures += lifecycleOk ? 0 : 1;
} finally {
  await browser.close();
}
console.log(failures ? `${failures} failure(s)` : 'all ok');
process.exit(failures ? 1 : 0);
