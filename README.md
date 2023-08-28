# Amaya

<p align="center">
  <img src="https://github.com/MichalHe/amaya/blob/b14829f48011e50b0c73f98fa06c53adfd9242b8/extras/amaya_logo.png?raw=true" />
</p>

Amaya is an experimental, automata-based linear integer arithmetic (LIA) SMT solver.

Amaya supports two execution backends:
- a native backend representing transition symbols explicitly. Slow, but offers more experimentation-oriented features such as tracking the semantics of automaton states.
- a high-performance MTBDD-based backend representing transition symbols symbolically using MTBDDs.

## Installing
All required dependencies can be found in `requirements.txt` and a virtual environment with these dependencies is all that
is needed to run Amaya using the native (default) backend.

### Building the high-performance MTBDD backend
Amaya relies on [sylvan](https://github.com/trolando/sylvan) providing efficient MTBDD implementation. In order to utilize Sylvan, Amaya
implements a C++ library with custom MTBDD leaves and automata algorithms. The python frontend then relies on Python's `ctypes` module
to call Amaya's C++ library.

The following steps need to be performed in order to use the MTBDD-backend:
1) Compile and install [sylvan](https://github.com/trolando/sylvan)
2) Compile [Amaya's C++ library](https://github.com/MichalHe/learning-sylvan).
3) Make sure the resulting shared object is present in `amaya/` folder, so that the `ctypes` wrapper will be able to find it.

## Running
The `run-amaya.py` script provides a user interface to Amaya. This script is current capable of running Amaya in three modes:
- `get-sat`   - single execution of the solver, outputting the SAT value (sat/unsat) of the formula
- `benchmark` - executes and measures the decision procedure runtime (hot-start).
- `convert`   - Run Amaya's preprocessor and output the result in different formats.
The `run-amaya.py` script also provides options that can tweak the decision procedure regardless of the execution mode
(e.g. enable eager minimization). See `./run-amaya.py --help`.

### Get-Sat
```bash
python3 run-amaya.py get-sat FILE
```
The get-sat command evaluates the given SMTLIB2 file and reports the results (sat/unsat). This command supports various
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
The following command benchmarks Amaya to be run for all SMTLIB2 files present in the `smt-files/tptp` folder (will not be
searched recursively). The option `--backend naive` specifies that the slower, native backend should be used. The
option `--execute-times 10` specifies that every benchmark file should be run 10 times and the average runtime will be
returned.
```bash
python3 run-amaya.py --backend naive benchmark --add-directory smt-files/tptp/ --execute-times 10
```

### Convert
Convert formula from SMTLIB2 into various output formats.

#### Example - Convert SMTLIB2 to the LASH format
The following example converts an SMTLIB2 formula into the LASH format and outputs the result to the stdout.
```bash
./run-amaya.py -p no-congruences -p assign-new-var-names -p nonlinear-term-use-two-vars \
    benchmarks/formulae/20190429-UltimateAutomizerSvcomp2019/jain_7_true-unreach-call_true-no-overflow_false-termination.i_10.smt2
```

Since LASH does not support congruences atoms, Amaya's preprocessor must be instructed to not introduce congruences (`-p no-congruences`)
and rather use inequations. Amaya uses congruences by default, as they offer better runtime characteristics when the moduli in formulae
are powers of 2. Furthermore, as some benchmarks might use symbols that cannot be part of variable identifiers in the LASH format, the
preprocessor is instructed to drop all of the variable names and introduce new ones (`-p assign-new-var-names`). Finally,
the `-p nonlinear-term-use-two-vars` causes Amaya's preprocessor to use two fresh quantified variables instead of one, causing the automata
manipulated by LASH to be smaller at the cost of having more variables.
