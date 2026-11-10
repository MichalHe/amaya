// Browser test of the static bundle in wasm/dist: drives the demo page in headless Chrome.
//
//   python3 -m http.server -d wasm/dist 8765 &
//   npm install puppeteer-core
//   CHROME=/usr/bin/google-chrome node wasm/test/browser-smoke.mjs http://localhost:8765/
//
// Solves every example of the demo page, checks the answers, and checks that a timeout stops the solver
// and that the page recovers afterwards.
import puppeteer from 'puppeteer-core';

const url = process.argv[2] ?? 'http://localhost:8765/';
const expected = {
  'Interval (sat)': 'sat',
  'Parity (unsat)': 'unsat',
  'Quantifiers (sat)': 'sat',
  'Frobenius coin problem (unsat)': 'unsat',
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
  const t0 = Date.now();
  await page.goto(url);
  await page.waitForFunction(() => !document.getElementById('run').disabled, { timeout: 120000 });
  console.log(`page ready after ${((Date.now() - t0) / 1000).toFixed(1)} s: ` +
              await page.$eval('#status', (e) => e.textContent));
  console.log('footer:', await page.$eval('#footer', (e) => e.textContent));

  async function solve(timeoutSeconds = 60) {
    await page.$eval('#timeout', (e, v) => { e.value = v; }, String(timeoutSeconds));
    await page.click('#run');
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
  const slow = await solve(3);
  const stopped = /stopped/.test(slow.status) || slow.answer !== '';
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
  await page.select('#example', 'Interval (sat)');
  const exported = await solve();
  await page.waitForSelector('#graph svg', { timeout: 60000 });
  const graph = await page.evaluate(() => {
    const select = document.getElementById('automaton');
    return { count: select.options.length, selected: select.selectedOptions[0]?.textContent,
             last: select.options[select.options.length - 2]?.textContent,
             nodes: document.querySelectorAll('#graph svg g.node').length };
  });
  const graphOk = exported.answer === 'sat' && graph.count > 1 && graph.selected === graph.last && graph.nodes > 0;
  console.log(`${graphOk ? 'ok  ' : 'FAIL'} automata graph: ${graph.count - 1} automata + trace, ` +
              `selected '${graph.selected}', ${graph.nodes} nodes drawn`);
  failures += graphOk ? 0 : 1;

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
} finally {
  await browser.close();
}
console.log(failures ? `${failures} failure(s)` : 'all ok');
process.exit(failures ? 1 : 0);
