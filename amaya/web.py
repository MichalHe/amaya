"""
Entry point for running Amaya in-process, e.g. under Pyodide (WebAssembly) on a web page.

`solve(smt2_text, args)` runs the same code path as `run-amaya.py [args] get-sat FILE` and returns a
dictionary with the answer and the captured output. With `export_automata='dot'|'vtf'|'mata'` it also
returns the automata that the CLI writes for `get-sat -o DIR --output-format FORMAT`. The CLI script is shipped inside the package as
`amaya/_cli.py` by the WebAssembly build (wasm/build.sh); in a source checkout the repository's
`run-amaya.py` is used.
"""
from __future__ import annotations

import contextlib
import importlib
import io
import logging
import os
import re
import runpy
import shutil
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence

ANSWERS = ('sat', 'unsat', 'unknown')
EXPORT_FORMATS = ('dot', 'vtf', 'mata')
EXPORT_DEPENDENCIES = ('graphviz', 'dd')
TRACE_FILE = 'trace-info.dot'


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


def missing_export_dependencies() -> List[str]:
    """Python packages that exporting automata needs but that are not installed."""
    missing = []
    for module in EXPORT_DEPENDENCIES:
        try:
            importlib.import_module(module)
        except ImportError:
            missing.append(module)
    return missing


@contextlib.contextmanager
def _capture_variable_names(sink: Dict[int, str]) -> Iterator[None]:
    """
    Record the variable table of the evaluation (id -> SMT name).

    Exported automata label their tracks with variable ids only; the names let a page show which track
    belongs to which SMT variable.
    """
    from amaya import parse
    original = parse.perform_whole_evaluation_on_source_text

    def evaluate_and_record(*args, **kwargs):
        result = original(*args, **kwargs)
        for var, info in (getattr(result, 'var_table', None) or {}).items():
            sink[var.id] = getattr(info, 'name', str(var.id))
        return result

    parse.perform_whole_evaluation_on_source_text = evaluate_and_record
    try:
        yield
    finally:
        parse.perform_whole_evaluation_on_source_text = original


def _automaton_size(text: str, output_format: str) -> Dict[str, int]:
    """Number of states and of transition lines (dot: edges; vtf/mata: symbol lines) of an exported automaton."""
    if output_format == 'dot':
        states = len(re.findall(r'shape=(?:double)?circle', text))
        transitions = sum(1 for line in text.splitlines() if ' -> ' in line and '@Start' not in line)
    elif output_format == 'vtf':
        states_line = next((line for line in text.splitlines() if line.startswith('%States')), '%States')
        states = len(states_line.split()) - 1
        transitions = sum(1 for line in text.splitlines() if line and line[0] not in '@%')
    else:  # mata: states only appear in %Initial/%Final and in transitions
        lines = [line.split() for line in text.splitlines() if line and line[0] not in '@%']
        states = len({state for parts in lines if len(parts) == 3 for state in (parts[0], parts[2])} |
                     {state for line in text.splitlines() if line.startswith(('%Initial', '%Final'))
                      for state in line.split()[1:]})
        transitions = len(lines)
    return {'states': states, 'transitions': transitions}


def _collect_exported_automata(directory: str, output_format: str) -> List[Dict[str, Any]]:
    """Read the files written by `get-sat -o DIR`: `<operation id>-<operation>.<format>`, ordered by id."""
    automata = []
    for path in Path(directory).iterdir():
        match = re.fullmatch(rf'(\d+)-(.+)\.{output_format}', path.name)
        if not match:
            continue
        text = path.read_text()
        automata.append({'id': int(match.group(1)), 'operation': match.group(2), 'format': output_format,
                         'name': path.name, 'text': text, **_automaton_size(text, output_format)})
    automata.sort(key=lambda automaton: automaton['id'])
    return automata


def solve(smt2_text: str, args: Optional[Sequence[str]] = None, mode: str = 'get-sat',
          mode_args: Optional[Sequence[str]] = None, export_automata: Optional[str] = None) -> Dict[str, Any]:
    """
    Run Amaya on the given SMT-LIB2 text.

    :param smt2_text: The SMT-LIB2 input.
    :param args: Global CLI options placed before the mode, e.g. ['--fast'] or ['--fast', '-O', 'all'].
    :param mode: CLI mode, 'get-sat' (default) or 'convert'.
    :param mode_args: Options placed after the mode, e.g. ['-f', 'smt2'] for 'convert'.
    :param export_automata: 'dot', 'vtf' or 'mata' to also return every automaton built during the
                            decision procedure (get-sat only; needs the `graphviz` and `dd` packages).
    :returns: {'answer': 'sat'|'unsat'|'unknown'|None, 'error': str|None, 'exit_code': int, 'stdout': str,
               'stderr': str, 'seconds': float, 'argv': [...]} - `answer` is the last answer line printed
               on stdout; `error` is set when Amaya failed or printed no answer.
               With `export_automata`, also 'automata': [{'id', 'operation', 'format', 'name', 'text',
               'states', 'transitions'}, ...] ordered by operation id (the last one is the automaton of the
               whole formula), 'trace': the operation graph in DOT (or None), and 'variables':
               {variable id: SMT name}.
    """
    args = list(args or [])
    mode_args = list(mode_args or [])
    export_dir = None
    if export_automata is not None:
        if export_automata not in EXPORT_FORMATS:
            raise ValueError(f'export_automata must be one of {EXPORT_FORMATS}, not {export_automata!r}')
        if mode != 'get-sat':
            raise ValueError('automata can only be exported in get-sat mode')
        missing = missing_export_dependencies()
        if missing:
            raise RuntimeError(f'exporting automata needs the Python packages {", ".join(missing)}')
        # `dd` warns about every BDD cube with don't-care bits that the exporter asks it to enumerate
        logging.getLogger('dd').setLevel(logging.ERROR)
        export_dir = tempfile.mkdtemp(prefix='amaya-automata-')
        mode_args += ['-o', export_dir, '--output-format', export_automata]
    _reset_solver_config()

    with tempfile.NamedTemporaryFile('w', suffix='.smt2', delete=False) as input_file:
        input_file.write(smt2_text)
        input_path = input_file.name

    argv = ['run-amaya.py', *args, mode, *mode_args, input_path]
    stdout, stderr = io.StringIO(), io.StringIO()
    exit_code = 0
    saved_argv = sys.argv
    variables: Dict[int, str] = {}
    # Amaya's log handler (amaya/__init__.py) holds the stream that was sys.stderr when amaya was imported, so
    # redirect_stderr alone would not capture --verbose/--debug output.
    from amaya import console_handler
    saved_log_stream = console_handler.setStream(stderr)
    started = time.perf_counter()
    try:
        sys.argv = argv
        capture_names = _capture_variable_names(variables) if export_dir else contextlib.nullcontext()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr), capture_names:
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
            except Exception:  # report instead of killing the host page/worker
                import traceback
                traceback.print_exc()
                exit_code = 2
    finally:
        console_handler.setStream(saved_log_stream)
        sys.argv = saved_argv
        os.unlink(input_path)
    seconds = time.perf_counter() - started

    exported: Dict[str, Any] = {}
    if export_dir:
        trace_path = Path(export_dir, TRACE_FILE)
        exported = {'automata': _collect_exported_automata(export_dir, export_automata),
                    'trace': trace_path.read_text() if trace_path.is_file() else None,
                    'variables': variables}
        shutil.rmtree(export_dir, ignore_errors=True)

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
            'seconds': seconds, 'argv': argv[1:-1], **exported}


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
