"""
Build the Amaya wheel for Pyodide (WebAssembly).

wasm/build.sh copies this file into a staged source tree and runs `pyodide build` there:

    amaya/                                Python package; run-amaya.py is copied to amaya/_cli.py
    mtbdd-backend/src, mtbdd-backend/include, mtbdd-backend/wrapper/base.pyx
    sylvan/                               src/ directory of sylvan (v1.5.0)

The MTBDD backend and sylvan are compiled into one extension module, `amaya.libamaya`, so the wheel
has no external library dependencies. sylvan_gmp.c is left out: Amaya does not use GMP leaves.
"""
import os

from Cython.Build import cythonize
from setuptools import Extension, find_namespace_packages, setup
from setuptools.command.build_ext import build_ext

BACKEND_SOURCES = [
    'mtbdd-backend/src/' + name for name in (
        'base.cpp', 'custom_leaf.cpp', 'operations.cpp', 'wrapper.cpp', 'lazy.cpp', 'tfa_leaf.cpp',
        'pareto_set.cpp', 'rewrites.cpp', 'bit_set.cpp', 'bit_set_leaf.cpp', 'algorithms.cpp',
        'interrupt.cpp', 'sylvan-extra.c',
    )
]
SYLVAN_SOURCES = [
    'sylvan/' + name for name in (
        'lace.c', 'sha2.c', 'sylvan_bdd.c', 'sylvan_cache.c', 'sylvan_common.c', 'sylvan_hash.c',
        'sylvan_ldd.c', 'sylvan_mt.c', 'sylvan_mtbdd.c', 'sylvan_refs.c', 'sylvan_sl.c', 'sylvan_stats.c',
        'sylvan_table.c',
    )
]


class BuildExtPerLanguage(build_ext):
    """Compile C++ sources as C++20 and C sources as C11; build sylvan with NDEBUG like its CMake release build."""

    def build_extensions(self):
        compile_one = self.compiler._compile

        def _compile(obj, src, ext, cc_args, extra_postargs, pp_opts):
            if src.endswith(('.cpp', '.cc', '.cxx')):
                flags = ['-std=c++20', '-Wno-register']  # sylvan's lace.h uses `register`
            else:
                flags = ['-std=gnu11']
                if '/sylvan/' in src.replace('\\', '/') or src.startswith('sylvan/'):
                    flags.append('-DNDEBUG')
            return compile_one(obj, src, ext, cc_args, list(extra_postargs) + flags, pp_opts)

        self.compiler._compile = _compile
        super().build_extensions()


extension = Extension(
    name='amaya.libamaya',
    sources=['mtbdd-backend/wrapper/base.pyx'] + BACKEND_SOURCES + SYLVAN_SOURCES,
    language='c++',
    include_dirs=['mtbdd-backend/include', 'sylvan'],
    extra_compile_args=['-O2', '-include', 'amaya_wasm_compat.h'],
)
if os.environ.get('AMAYA_WASM_DEBUG'):  # symbol names in WebAssembly stack traces
    extension.extra_compile_args += ['-g2', '-O1']
    extension.extra_link_args = ['-g2']

setup(
    packages=find_namespace_packages(include=['amaya', 'amaya.*']),  # amaya.presburger has no __init__.py
    ext_modules=cythonize([extension], compiler_directives={'language_level': '3'}),
    cmdclass={'build_ext': BuildExtPerLanguage},
)
