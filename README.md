# Amaya

<p align="center">
  <img src="https://github.com/MichalHe/amaya/blob/b14829f48011e50b0c73f98fa06c53adfd9242b8/extras/amaya_logo.png?raw=true" />
</p>

This is an experimental, automata-based linear integer arithmetic (LIA) SMT solver. 

Amaya supports two execution backends: 
- a native backend representing transition symbols explicitly. Slow, but great for experimentation,
- a high-performance MTBDD-based backend representing transition symbols symbolically using MTBDDs.

## Installing
All required dependencies can be found in `requirements.txt` and a virtual environment with these dependencies is all that 
is needed to run Amaya using the native (default) backend.

### Building the high-performance MTBDD backend
Amaya relies on [sylvan](https://github.com/trolando/sylvan) providing efficient MTBDD implementation. This is achieved by
implementing a C++ library with custom MTBDD leaves utilized by Amaya, and then implementing a Python `ctypes` wrapper around
this library.

The following steps should be performed in order to use the MTBDD-backend:
1) Compile and install the _sylvan_ library 
2) Compile the Amaya's C++ library according to the given instructions [amaya-sylvan](https://github.com/MichalHe/learning-sylvan). 
3) Make sure the resulting shared object is present (a symlink is sufficient) in `amaya/` folder, so that the `ctypes` wrapper will be able to find it.

## Running
The `run-amaya.py` script provides a user interface to Amaya. This script is current capable of running Amaya in two modes:
- `get-sat` - single execution of the decision procedure, outputting the SAT value
- `benchmark` - executes and measures the decision procedure runtime (hot-start).
The `run-amaya.py` script also provides options that can tweak the decision procedure regardless of the execution mode 
(e.g. enable eager minimization). See `python3 run-amaya.py --help`. 

### Get-Sat 
```bash
python3 run-amaya.py get-sat FILE
```
The get-sat command evaluates the given SMT2 lib file and reports the results (sat/unsat). This command supports various
flags for inspecting the evaluation process such as the export of the automatons created during the evaluation, or
writing out the runtime for the individual operations performed during the evaluation etc. 

To see a full list of supported switches, see:
```bash
python3 run-amaya.py get-sat --help
```

#### Example - Exporting the intermediate automata created during evaluation of a TPTP benchmark file
The following command will output the automata created during the decision procedure in the order they were created to
the provided folder. The output format of the exported automata can be changed by `--output-format`.
```bash
python3 run-amaya.py --backend MTBDD get-sat --output-created-automata smt-files/tptp/ARI005\=1.smt2
```

### Benchmarks
Run Amaya in the benchmarking mode. This mode requires a set of input files to be specified. See `python3 run-amaya.py 
benchmark --help` for information about how to specify the input files.

If the benchmarking runner encounters a file for which the evaluation procedure did yield different results as expected
(specified in the file via the `smt-info` statement) the file will not be rerun and will have its `failed` field in the
report set to `True`.

To see a full list of supported options, see:
```bash
python3 run-amaya.py benchmark --help
```

#### Example - Running the TPTP benchmark
The following command benchmarks Amaya to be run for all SMT2 files present in the `smt-files/tptp` folder (will not be
searched recursively). The option `--backend naive` specifies that the slower, native backend should be used. The 
option `--execute-times 10` specifies that every benchmark file should be run 10 times and the average runtime will be
returned.
```bash
python3 run-amaya.py --backend naive benchmark --add-directory smt-files/tptp/ --execute-times 10
```

## Known bugs
Some of the harder problems consume more than 10g of RAM (e.g. Psyco).

## Benchmark tests
The following table gives serves to reflect the current capabilities of the Amaya solver. 

|Benchmark name | MTBDD TFN Status | Naive TFN Status |Notes |
--- | --- | --- | ---
| TPTP | Passing | Passing | |
| UltimateAutomizer | Passing | Passing | |
| Psyco | Not passing | Unknown | The naive TFN runtime is enormous |

## Implementation backlog
- [ ] Unify the `ast_relations` and `relations_structures` modules into `relations` module with `data` and `algorithm` submodules
