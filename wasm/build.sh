#!/usr/bin/env bash
# Build Amaya for WebAssembly (Pyodide) and assemble a static web bundle in wasm/dist/.
#
# Requirements: git, a Python 3.13 interpreter with `pyodide-build` installed (its `pyodide` CLI is
# looked up as $PYODIDE_CLI, default `pyodide`). The matching Emscripten SDK is installed into the
# Pyodide cross-build environment on first use.
#
# Environment variables (all optional):
#   PYODIDE_VERSION          Pyodide release to build for (default 0.29.5); the web page must load the
#                            same release, see wasm/web/amaya.js.
#   PYODIDE_CLI              path of the pyodide-build CLI (default: pyodide)
#   PYODIDE_XBUILDENV_PATH   where to keep the cross-build environment (default: wasm/build/xbuildenv)
#   SYLVAN_VERSION           sylvan git tag (default v1.5.0)
#   HOST_PYTHON              Python with pip, used to build the pure-Python wheels needed for exporting
#                            automata (graphviz, dd and dd's dependencies); default python3
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO=$(dirname "$HERE")
BUILD="$HERE/build"
DIST="$HERE/dist"
PYODIDE_VERSION=${PYODIDE_VERSION:-0.29.5}
PYODIDE_CLI=${PYODIDE_CLI:-pyodide}
SYLVAN_VERSION=${SYLVAN_VERSION:-v1.5.0}
HOST_PYTHON=${HOST_PYTHON:-python3}
# Pure-Python packages that exporting automata needs (amaya/visualization.py); loaded by the page on demand.
# dd 0.6.0 requires ply <= 3.10.
VISUALIZATION_PACKAGES=(graphviz==0.21 dd==0.6.0 astutils==0.0.6 ply==3.10)
export PYODIDE_XBUILDENV_PATH=${PYODIDE_XBUILDENV_PATH:-$BUILD/xbuildenv}

mkdir -p "$BUILD" "$DIST"

# 1. sylvan sources
if [ ! -d "$BUILD/sylvan-$SYLVAN_VERSION/src" ]; then
    git clone --quiet --depth 1 --branch "$SYLVAN_VERSION" https://github.com/trolando/sylvan.git "$BUILD/sylvan-$SYLVAN_VERSION"
fi

# 2. staged source tree for the wheel
STAGE="$BUILD/stage"
rm -rf "$STAGE"
mkdir -p "$STAGE/mtbdd-backend/wrapper"
rsync -a --exclude '__pycache__' --exclude '*.so' --exclude '*.pyc' "$REPO/amaya/" "$STAGE/amaya/"
cp "$REPO/run-amaya.py" "$STAGE/amaya/_cli.py"
rsync -a "$REPO/mtbdd-backend/src" "$REPO/mtbdd-backend/include" "$STAGE/mtbdd-backend/"
cp "$REPO/mtbdd-backend/wrapper/base.pyx" "$STAGE/mtbdd-backend/wrapper/"
rsync -a "$BUILD/sylvan-$SYLVAN_VERSION/src/" "$STAGE/sylvan/"
cp "$HERE/packaging/setup.py" "$HERE/packaging/pyproject.toml" "$HERE/packaging/amaya_wasm_compat.h" "$STAGE/"
cp "$REPO/LICENSE.txt" "$STAGE/"

# 3. cross-build environment and Emscripten
if ! "$PYODIDE_CLI" xbuildenv versions 2>/dev/null | grep -q "$PYODIDE_VERSION"; then
    "$PYODIDE_CLI" xbuildenv install "$PYODIDE_VERSION"
fi
"$PYODIDE_CLI" xbuildenv use "$PYODIDE_VERSION" > /dev/null
EMSDK_ENV="$PYODIDE_XBUILDENV_PATH/$PYODIDE_VERSION/emsdk/emsdk_env.sh"
if [ ! -f "$EMSDK_ENV" ]; then
    "$PYODIDE_CLI" xbuildenv install-emscripten
fi
# shellcheck disable=SC1090
source "$EMSDK_ENV" > /dev/null 2>&1

# 4. the wheel
rm -f "$DIST"/amaya-*.whl
(cd "$STAGE" && "$PYODIDE_CLI" build --outdir "$DIST")
WHEEL=$(cd "$DIST" && ls amaya-*.whl | head -n 1)

# 5. pure-Python wheels for exporting automata. dd is built from its sdist: its binary wheels contain
#    CUDD extensions; without them it is pure Python. Its generated C sources are removed.
WHEELS="$BUILD/wheels"
if [ ! -f "$WHEELS/.complete" ]; then
    rm -rf "$WHEELS"
    "$HOST_PYTHON" -m pip wheel --quiet --no-deps --no-binary dd --wheel-dir "$WHEELS" "${VISUALIZATION_PACKAGES[@]}"
    "$HOST_PYTHON" "$HERE/packaging/slim_wheel.py" "$WHEELS"/dd-*.whl 'dd/*.c' 'dd/*.pyx' 'dd/*.pxd'
    touch "$WHEELS/.complete"
fi
rm -f "$DIST"/graphviz-*.whl "$DIST"/dd-*.whl "$DIST"/astutils-*.whl "$DIST"/ply-*.whl
cp "$WHEELS"/*.whl "$DIST/"
VISUALIZATION_WHEELS=$("$HOST_PYTHON" -c 'import json, pathlib, sys; print(json.dumps(sorted(p.name for p in pathlib.Path(sys.argv[1]).glob("*.whl"))))' "$WHEELS")

# 6. web bundle: worker, main-thread API, demo page, and a manifest naming the wheels
cp "$HERE/web/amaya.js" "$HERE/web/amaya-worker.js" "$HERE/web/index.html" "$DIST/"
cat > "$DIST/amaya-build.json" <<EOF
{
  "wheel": "$WHEEL",
  "visualizationWheels": $VISUALIZATION_WHEELS,
  "pyodideVersion": "$PYODIDE_VERSION",
  "sylvanVersion": "$SYLVAN_VERSION",
  "amayaCommit": "$(git -C "$REPO" rev-parse --short HEAD 2>/dev/null || echo unknown)"
}
EOF
echo "Built $DIST/$WHEEL"
echo "Serve $DIST with any static file server, e.g.: python3 -m http.server -d $DIST 8000"
