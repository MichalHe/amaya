"""
Entry point for running Amaya in-process, e.g. under Pyodide (WebAssembly) on a web page.

`solve(smt2_text, args)` runs the same code path as `run-amaya.py [args] get-sat FILE` and returns a
dictionary with the answer and the captured output. The CLI script is shipped inside the package as
`amaya/_cli.py` by the WebAssembly build (wasm/build.sh); in a source checkout the repository's
`run-amaya.py` is used.
"""
from __future__ import annotations

import contextlib
import io
import os
import runpy
import sys
import tempfile
import time
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Union

ANSWERS = ('sat', 'unsat', 'unknown')


def _cli_path() -> Path:
    packaged = Path(__file__).with_name('_cli.py')
    if packaged.is_file():
        return packaged
    checkout = Path(__file__).resolve().parent.parent / 'run-amaya.py'
    if checkout.is_file():
        return checkout
    raise FileNotFoundError('Neither amaya/_cli.py nor run-amaya.py found')


def _reset_solver_config() -> None:
    """The CLI mutates the global `solver_config`; restore its defaults so runs do not influence each other."""
    from amaya.config import SolverConfig, solver_config
    solver_config.__dict__.update(SolverConfig().__dict__)


def solve(smt2_text: str, args: Optional[Sequence[str]] = None, mode: str = 'get-sat',
          mode_args: Optional[Sequence[str]] = None) -> Dict[str, Union[str, int, float, None, List[str]]]:
    """
    Run Amaya on the given SMT-LIB2 text.

    :param smt2_text: The SMT-LIB2 input.
    :param args: Global CLI options placed before the mode, e.g. ['--fast'] or ['--fast', '-O', 'all'].
    :param mode: CLI mode, 'get-sat' (default) or 'convert'.
    :param mode_args: Options placed after the mode, e.g. ['-f', 'smt2'] for 'convert'.
    :returns: {'answer': 'sat'|'unsat'|'unknown'|None, 'error': str|None, 'exit_code': int, 'stdout': str,
               'stderr': str, 'seconds': float, 'argv': [...]} - `answer` is the last answer line printed
               on stdout; `error` is set when Amaya failed or printed no answer.
    """
    args = list(args or [])
    mode_args = list(mode_args or [])
    _reset_solver_config()

    with tempfile.NamedTemporaryFile('w', suffix='.smt2', delete=False) as input_file:
        input_file.write(smt2_text)
        input_path = input_file.name

    argv = ['run-amaya.py', *args, mode, *mode_args, input_path]
    stdout, stderr = io.StringIO(), io.StringIO()
    exit_code = 0
    saved_argv = sys.argv
    # Amaya's log handler (amaya/__init__.py) holds the stream that was sys.stderr when amaya was imported, so
    # redirect_stderr alone would not capture --verbose/--debug output.
    from amaya import console_handler
    saved_log_stream = console_handler.setStream(stderr)
    started = time.perf_counter()
    try:
        sys.argv = argv
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            try:
                runpy.run_path(str(_cli_path()), run_name='__main__')
            except SystemExit as exit_request:
                code = exit_request.code
                if isinstance(code, int):
                    exit_code = code
                elif code is None:
                    exit_code = 0
                else:
                    print(code, file=sys.stderr)
                    exit_code = 1
            except Exception as error:  # report instead of killing the host page/worker
                import traceback
                traceback.print_exc()
                exit_code = 2
    finally:
        console_handler.setStream(saved_log_stream)
        sys.argv = saved_argv
        os.unlink(input_path)
    seconds = time.perf_counter() - started

    out_text = stdout.getvalue()
    answer = None
    for line in reversed(out_text.splitlines()):
        if line.strip() in ANSWERS:
            answer = line.strip()
            break
    err_text = stderr.getvalue()
    error = None
    if exit_code != 0:
        error = (err_text.strip().splitlines() or [f'Amaya exited with code {exit_code}'])[-1]
    elif answer is None and mode == 'get-sat':
        error = 'Amaya produced no answer (is the input malformed or missing (check-sat)?)'
    return {'answer': answer, 'error': error, 'exit_code': exit_code, 'stdout': out_text, 'stderr': err_text,
            'seconds': seconds, 'argv': argv[1:-1]}


def version_info() -> Dict[str, str]:
    """Versions of the runtime pieces, for display on a web page."""
    import platform
    info = {'python': platform.python_version(), 'platform': sys.platform}
    try:
        import pyodide  # type: ignore
        info['pyodide'] = getattr(pyodide, '__version__', 'unknown')
    except ImportError:
        pass
    return info
