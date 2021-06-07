# Amaya

This is an experimental, automata-based linear integer arithmetic (LIA) SAT solver. 

## Installing
Since the version 0.2 the solver supports representation of automata transition functions in form of MTBDDs.
In order to provide this support it relies on [sylvan](https://github.com/trolando/sylvan) for efficient MTBDD manipulation, 
more specifically most of the operations needed are implemented in C++ using constructs provided by Sylvan and then exposed
via a C wrapper using the python _ctypes_ library.

To use this library you need to have a working installation of the _sylvan_ library and compile the C++ codebase
hosted as a separate repository [here](https://github.com/MichalHe/learning-sylvan). Make sure the result of the
compilation is present (e.g. a symlink) in the root of this project as that is the place where the _ctypes_ library
will look for it.

After compiling the C++ module, install the required python dependencies from the `requirements.txt`.

## Running
The runner script `amaya.py` is currently capable of two run modes, each with its own set of command line options. Some
options can be applied regardless of the run mode chosen. To view those, see `python3 amaya.py --help`. 

### Get-Sat 
```bash
python3 amaya.py get-sat FILE
```
The get-sat command evaluates the given SMT2 lib file and reports the results (sat/unsat). This command supports various
flags for inspecting the evaluation process such as the export of the automatons created during the evaluation, or writing
out the runtime for the individual operations performed during the evaluation etc. 

To see a full list of supported switches, see:
```bash
python3 amaya.py get-sat --help
```

#### Example - Viewing the automatons created during evaluation of a TPTP benchmark file
The following command will print to the _stdout_ all automatons created during the evaluation phase in the order they were created. 
Furthermore one can supply additional option `--dump-dest DEST` that will cause outputing the individual automatons to separate
files in the specified `DEST` directory. (If the directory does not exists it will be created.)
```bash
python3 amaya.py --backend MTBDD get-sat --dump-created-automatons smt-files/tptp/ARI005\=1.smt2
```

### Benchmarks
The second command the standard runner provides is the build in benchmarking tool. The specification of which formulae files 
belong to the benchmark that is about to be executed can be in various forms - from naming individual files to specifying
directories that should be recursively searched for smt2 files. Furthermore one can specify the number of executions that will
be performed, as well as the output format for the report (although only _json_ is supported at the moment). Note that the reported
runtimes are in nanoseconds.

If the benchmarking runner encounters a file for which the evaluation procedure did yield different results as expected (specified
in the file via the `smt-info` statement) the file will not be rerun and will have its `failed` field in the report set to `True`.

To see a full list of supported options, see:
```bash
python3 amaya.py benchmark --help
```

#### Example - Running the TPTP benchmark
The following command specifies a benchmark to be run as all smt2 files present in the `smt-files/tptp` folder (without recursive
searching). The option `--backend naive` specifies that the transition functions should be stored as Python built-in sets of transition symbols
(will not use MTBDDs). The option `--execute-times 10` specifies that every benchmark file should be run 10 times. 
```bash
python3 amaya.py --backend naive benchmark --add-directory smt-files/tptp/ --execute-times 10
```

## Known bugs
The MTBDD backend currently does a very poor job of marking which MTBDDs are currently in use and therefore cannot be freed if Sylvan runs out
of memory and enters garbage collection. This is a known issue and is currently WiP.  

## Benchmark tests
The following table gives serves to reflect the current capabilities of the Amaya solver. 

|Benchmark name | MTBDD TFN Status | Naive TFN Status |Notes |
--- | --- | --- | ---
| TPTP | Passing | Passing | |
| Psyco | Not passing | Unknown | The naive TFN runtime is enormous |
