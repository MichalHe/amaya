# Progress: Inner Quantifier Squeeze Elimination (IQSE)

Tracks work-order steps 1-5 of `docs/QSE_IMPLEMENTATION_PLAN.md` §9. Steps 6-7 (differential
benchmark run, re-tiering) are out of scope of this record; see §10 of the plan for the
quantities they would measure.

## Status

| Step | Content | Status |
|---|---|---|
| 1 | `amaya/preprocessing/inner_quantifier_squeeze_elimination.py`: §4.2 detection, §4.4 substitution | Done |
| 2 | T15 brute-force equivalence test | Done |
| 3 | I1, I2: config flag and CLI mapping | Done |
| 4 | I3, I5: pipeline registration | Done |
| 5 | I4: legacy sequence | Done |

## Changes

| File | Change |
|---|---|
| `amaya/preprocessing/inner_quantifier_squeeze_elimination.py` | New module. `eliminate_inner_quantifier_squeezes` (entry point), `_eliminate_squeezes_for_quantifier`, `_try_eliminate_squeezed_var`, `_try_match_squeeze_pair`, `_find_squeeze_pair`, `_classify_residual_conjunct`, `_substitute_squeezed_var_in_bound`, plus `Squeeze_Match` / `Residual_Bound` / `Residual_Bound_Kind` |
| `tests/test_inner_quantifier_squeeze_elimination.py` | New module. T1-T15 from plan §8, verbatim in naming |
| `amaya/config.py` | `OptimizationsConfig.eliminate_squeezed_inner_quantifiers: bool = False` (I1) |
| `run-amaya.py` | `opt_to_config_field['squeeze-elimination']`, `-O` help paragraph (I2) |
| `amaya/preprocessing/pipeline.py` | `_pass_squeeze_elimination` adapter; `Pass_Descriptor(name='squeeze-elimination', ...)` registered immediately before `rce`, per plan §7.1/§7.2 (I3) |
| `amaya/parse.py` | Guarded call in `_optimize_formula_structure_legacy`, placed after the `resolve_conditional_equalities` block (I4) |
| `tests/test_pipeline_registry.py` | Non-`FINALIZE` pass count 17 -> 18; `test_all_optimizations_enabled_yields_the_17_non_finalize_passes` renamed to `..._18_...`; module docstring item (c) updated (I5) |

## Deviations from the plan discovered during implementation

None. The plan's §4.2-§4.5 formulas, the `Squeeze_Match`/`Residual_Bound` field lists, and the
module layout of §6 were implemented as specified; every T1-T15 assertion in
`tests/test_inner_quantifier_squeeze_elimination.py` passed on the first run against the
hand-derived expected values (no test was adjusted to match a diverging implementation).

## Verification performed

- `venv/bin/python -m pytest tests/test_inner_quantifier_squeeze_elimination.py -v`: 15/15 pass (T1-T15).
- `venv/bin/python -m pytest tests/test_pipeline_registry.py tests/test_optimization_pipeline.py tests/test_preprocessing.py tests/test_conditional_equality_resolution.py -q`: 51 passed, 4 skipped, 1 xfailed (all pre-existing skips/xfail, unrelated to this change).
- `venv/bin/python run-amaya.py -O squeeze-elimination --help`: parses (work-order step 3 acceptance criterion).
- Full suite (`venv/bin/python -m pytest -q`, excluding 9 test modules that fail to collect on `devel` before this change - stale imports of removed modules such as `amaya.ast_relations`, unrelated to IQSE): 344 passed, 8 skipped, 1 xfailed, 1 failed. The 1 failure
  (`tests/test_bounded_congruence_detection.py::test_bounded_congruence_construction_preserves_the_answer`)
  was confirmed via `git stash` to fail identically before this change; it is unrelated to IQSE.

## Not measured

Per plan §10, unchanged by this implementation: squeeze-pattern hit rate on any benchmark corpus,
the effect of §5.3's coefficient growth on automaton size, interaction with `rce` / `miniscope` /
`opt-bottom-exists`, and end-to-end solving time. No number in this document is derived from a
benchmark run.
