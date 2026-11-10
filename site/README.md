# Website

The sources of Amaya's website, published at <https://verifit.github.io/amaya/>: a landing page and the
playground, which runs Amaya compiled to WebAssembly (see [`wasm/`](../wasm/README.md)).

| Path | Content |
|---|---|
| `index.html` | Landing page |
| `playground/index.html` | Playground page; its logic is `wasm/web/playground.js`, shared with the demo page of the WebAssembly bundle |
| `404.html` | Page for missing paths (absolute links, own styles) |
| `assets/site.css`, `assets/site.js`, `assets/theme.js` | Styles and behaviour shared by the pages (colour theme, tabs, copy buttons) |
| `assets/hero.js` | The automaton on the landing page: Amaya's output for `∃k. x = 3k + 1`, drawn and run on a number |
| `assets/fonts/` | Source Serif 4 and IBM Plex (SIL Open Font License, see `OFL-*.txt`) |
| `build.sh` | Assembles the site in `site/_site` |
| `test/` | `hero.mjs` (the automaton accepts exactly `x mod 3 = 1`), `site-smoke.mjs` (the pages in Chrome) |

## Building and previewing

```sh
./wasm/build.sh            # the WebAssembly bundle in wasm/dist; see wasm/README.md for its requirements
./site/build.sh            # the site in site/_site
python3 -m http.server -d site/_site 8000
```

`site/build.sh` copies the pages and assets, Amaya's logo (`extras/amaya_logo.png`), and the bundle from
`wasm/dist` into `playground/` (the bundle's own demo page is left out).

Tests (they need `npm install pyodide puppeteer-core` and Chrome):

```sh
node site/test/hero.mjs
CHROME=/usr/bin/google-chrome node site/test/site-smoke.mjs http://localhost:8000/
CHROME=/usr/bin/google-chrome node wasm/test/browser-smoke.mjs http://localhost:8000/playground/
```

## Deployment

`.github/workflows/website.yml` builds the bundle and the site, runs the tests above, and on every push to
`devel` that touches the site, the WebAssembly build or the solver, publishes `site/_site` on the `gh-pages`
branch. Pull requests only build and test it. A maintainer runs the workflow by hand from the Actions tab
(*website*, *Run workflow*, on `devel`).

GitHub Pages has to serve that branch once: *Settings → Pages → Build and deployment → Deploy from a branch*,
branch `gh-pages`, folder `/ (root)`.

## Regenerating the landing page's automaton

`assets/hero.js` contains Amaya's output verbatim. To regenerate it, run

```sh
cat > residue.smt2 <<'EOF'
(set-logic LIA)
(declare-fun x () Int)
(assert (exists ((k Int)) (= x (+ (* 3 k) 1))))
(check-sat)
EOF
python3 run-amaya.py --fast get-sat -o out --output-format vtf residue.smt2
```

and copy `out/3-minimization.vtf` into `AUTOMATON`. The layout in `hero.js` places the five states by hand, so a
different automaton also needs new positions; `node site/test/hero.mjs` checks the language.
