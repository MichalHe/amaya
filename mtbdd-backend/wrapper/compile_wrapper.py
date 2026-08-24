from setuptools import setup, Extension
from Cython.Build import cythonize

# Sources mirror the `shared-lib` target in mtbdd-backend/Makefile, since the
# NFA implementation is spread across the backend and pulls in the solver's
# leaf types (custom_leaf.cpp, bit_set*.cpp), machinery init (wrapper.cpp)
# and other helpers it depends on.
backend_sources = [
    "../src/base.cpp",
    "../src/custom_leaf.cpp",
    "../src/operations.cpp",
    "../src/wrapper.cpp",
    "../src/lazy.cpp",
    "../src/tfa_leaf.cpp",
    "../src/pareto_set.cpp",
    "../src/rewrites.cpp",
    "../src/bit_set.cpp",
    "../src/bit_set_leaf.cpp",
    "../src/algorithms.cpp",
    "../src/sylvan-extra.c",
]

ext = Extension(
    name="libamaya",
    sources=["base.pyx"] + backend_sources,
    language="c++",
    include_dirs=["/home/mhecko/.local/include", "../include"],
    library_dirs=["/home/mhecko/.local/lib64"],
    runtime_library_dirs=["/home/mhecko/.local/lib64"],
    libraries=["sylvan", "gmp", "pthread"],
    extra_compile_args=["--std=c++20"],
)

setup(
    ext_modules=cythonize([ext], compiler_directives={'language_level': "3"})
)
