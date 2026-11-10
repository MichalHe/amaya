// Browser test of the website built by site/build.sh: the landing page and its automaton, and the link from it
// into the playground. The playground itself is tested by wasm/test/browser-smoke.mjs (run it on <url>/playground/).
//
//   ./site/build.sh && python3 -m http.server -d site/_site 8000 &
//   npm install puppeteer-core
//   CHROME=/usr/bin/google-chrome node site/test/site-smoke.mjs http://localhost:8000/
import puppeteer from 'puppeteer-core';

// Click an element after scrolling it to the middle of the viewport, so that no sticky header covers it.
async function click(page, selector) {
  await page.$eval(selector, (element) => element.scrollIntoView({ block: 'center', inline: 'center' }));
  await page.click(selector);
}

const url = new URL(process.argv[2] ?? 'http://localhost:8000/');
const browser = await puppeteer.launch({
  executablePath: process.env.CHROME ?? '/usr/bin/google-chrome',
  headless: true,
  args: ['--no-sandbox'],
});
let failures = 0;
function check(ok, message) {
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${message}`);
  failures += ok ? 0 : 1;
}

try {
  const page = await browser.newPage();
  const problems = [];
  page.on('pageerror', (error) => problems.push(`page error: ${error.message}`));
  page.on('console', (message) => { if (message.type() === 'error') problems.push(`console: ${message.text()}`); });
  page.on('response', (response) => {
    if (response.status() >= 400 && response.url().startsWith(url.origin)) problems.push(`HTTP ${response.status()} ${response.url()}`);
  });

  await page.goto(url.href, { waitUntil: 'networkidle0' });
  check((await page.title()).startsWith('Amaya'), `landing page: "${await page.title()}"`);

  // Every in-page link has a target.
  const missing = await page.$$eval('a[href^="#"]', (links) => links.map((a) => a.getAttribute('href'))
    .filter((href) => href.length > 1 && !document.getElementById(href.slice(1))));
  check(!missing.length, `in-page links have targets${missing.length ? ': missing ' + missing.join(' ') : ''}`);

  // The automaton: 7 = 3·2 + 1 is accepted, 8 is not; the drawing has five states and every bit is read.
  const verdict = async (value) => {
    await page.$eval('#hero-automaton input', (input, v) => { input.value = v; input.dispatchEvent(new Event('input')); }, String(value));
    await page.waitForFunction(() => /Accepted|Rejected/.test(document.querySelector('.hero-verdict').textContent), { timeout: 20000 });
    return page.$eval('.hero-verdict', (e) => e.textContent);
  };
  const states = await page.$$eval('#hero-automaton .hero-state', (groups) => groups.length);
  check(states === 5, `hero automaton has ${states} states`);
  for (const [value, accepted] of [[7, true], [8, false], [-2, true], [0, false]]) {
    const text = await verdict(value);
    check(text.startsWith(accepted ? 'Accepted' : 'Rejected'), `x = ${value}: ${text}`);
  }
  const read = await page.$$eval('.hero-bit', (cells) => [cells.length, cells.filter((c) => c.classList.contains('is-read')).length]);
  check(read[0] > 0 && read[0] === read[1], `all ${read[0]} bits of the last number were read`);

  // Tabs and the theme toggle.
  await click(page, '#tab-docker');
  check(await page.$eval('#panel-docker', (e) => !e.hidden) && await page.$eval('#panel-source', (e) => e.hidden), 'Docker tab shows its panel');
  const before = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  await click(page, '.masthead .theme-toggle');
  const after = await page.evaluate(() => [document.documentElement.dataset.theme, getComputedStyle(document.body).backgroundColor]);
  check(after[0] && after[1] !== before, `theme toggle switches to ${after[0]} (${before} -> ${after[1]})`);

  check(!problems.length, `no errors on the landing page${problems.length ? ':\n  ' + problems.join('\n  ') : ''}`);

  // No horizontal scrolling of the page at phone width (code blocks scroll inside themselves).
  await page.setViewport({ width: 360, height: 800 });
  const overflow = await page.evaluate(() => document.documentElement.scrollWidth - document.documentElement.clientWidth);
  check(overflow <= 0, `no horizontal page scroll at 360 px (overflow ${overflow} px)`);
  // The automaton is scaled down on phones; its smallest label must stay readable (box of 13 px: an 11 px font).
  const smallestLabel = await page.$$eval('#hero-automaton text', (texts) => Math.min(...texts.map((t) => t.getBoundingClientRect().height)));
  check(smallestLabel >= 13, `hero labels readable at 360 px (smallest box ${smallestLabel.toFixed(1)} px)`);
  await page.setViewport({ width: 1280, height: 900 });

  // The link below the automaton opens the playground on the same formula with graphs, and Amaya's last
  // automaton is the five-state one drawn on the landing page.
  problems.length = 0;
  const link = await page.$eval('#hero-caption a', (a) => a.href);
  await page.goto(link);
  await page.waitForFunction(() => !document.getElementById('run').disabled, { timeout: 120000 });
  const preset = await page.evaluate(() => [document.getElementById('example').value, document.getElementById('export').value]);
  check(preset[0] === 'Residue modulo 3 (sat)' && preset[1] === 'dot', `playground link presets ${preset.join(', ')}`);
  await click(page, '#run');
  await page.waitForSelector('#graph svg', { timeout: 120000 });
  const last = await page.$eval('#automaton', (select) => select.selectedOptions[0].textContent);
  check(/5 states/.test(last), `playground builds the same automaton: ${last}`);
  check(!problems.length, `no errors in the playground${problems.length ? ':\n  ' + problems.join('\n  ') : ''}`);
} finally {
  await browser.close();
}
console.log(failures ? `${failures} failure(s)` : 'all ok');
process.exit(failures ? 1 : 0);
