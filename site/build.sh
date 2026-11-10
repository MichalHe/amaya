#!/usr/bin/env bash
# Assemble the website in an output directory (default site/_site): the landing page with its assets and Amaya's
# logo, and the playground with the WebAssembly bundle of wasm/dist (build that first with wasm/build.sh).
#
#   ./wasm/build.sh && ./site/build.sh && python3 -m http.server -d site/_site 8000
#
# Environment: WASM_DIST, the bundle to use (default wasm/dist).
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO=$(dirname "$HERE")
OUT=${1:-$HERE/_site}
DIST=${WASM_DIST:-$REPO/wasm/dist}
if [ ! -f "$DIST/amaya-build.json" ]; then
    echo "No WebAssembly bundle in $DIST; run wasm/build.sh first." >&2
    exit 1
fi

rm -rf "$OUT"
mkdir -p "$OUT/playground"
cp "$HERE/index.html" "$HERE/404.html" "$OUT/"
cp -r "$HERE/assets" "$OUT/"
cp "$REPO/extras/amaya_logo.png" "$OUT/assets/amaya-logo.png"

# The playground: the bundle without its stand-alone demo page, and the website's page, which loads
# playground.js with the build id like the demo page does (see wasm/README.md, "Updating a deployment").
for file in "$DIST"/*; do
    [ "$(basename "$file")" = index.html ] || cp "$file" "$OUT/playground/"
done
BUILD_ID=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1])).get("buildId", ""))' "$DIST/amaya-build.json")
if [ -z "$BUILD_ID" ]; then
    echo "No buildId in $DIST/amaya-build.json; rebuild the bundle with wasm/build.sh." >&2
    exit 1
fi
sed "s|src=\"./playground.js\"|src=\"./playground.js?v=$BUILD_ID\"|" "$HERE/playground/index.html" > "$OUT/playground/index.html"
grep -q "playground.js?v=$BUILD_ID" "$OUT/playground/index.html"

# Served as is: GitHub Pages would otherwise run Jekyll on the files.
touch "$OUT/.nojekyll"
echo "Built the website in $OUT"
