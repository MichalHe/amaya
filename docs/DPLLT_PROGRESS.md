# Progress: DPLL(T)-style Top-Level Solving with an Automata Theory Backend

Implementation record for `docs/DPLLT_WITH_AUTOMATA.md`. The strategy is disabled by default and is
selected by `--use-dpllt-automata`.

## Status

| Design section | Content | Status |
|---|---|---|
| §4 | Split into the general part and the positive-existential part, eligibility, applicability conditions | Done |
| §5.1 | Renaming the binders of `chi` apart, alphabet rebuild | Done |
| §5.2, §5.3 | Literal identity, the monotone abstraction | Done |
| §6.1 | The automaton for `phi`, built once | Done |
| §6.2 | The loop | Done |
| §6.3 | Implicant minimization | Done |
| §6.4 | Assembling the assertion, the hoisted prefix | Done |
| §6.5 | Model reporting; `solutions_nfa` left `None` | Done |
| §6.6 | Blocking clauses | Done |
| §7 | Assertion optimizer, three modes | Done; the `restricted` allowlist holds `linearize`, the remaining passes are unclassified |
| §8.1-§8.4 | Caches, the clone-on-read/write discipline | Done |
| §9 | Module layout | Done |
| §10 | Configuration and command line | Done |
| §12 | Instrumentation: the per-run counters, and logging every formula handed to the automata engine | Done |
| §15 | Test plan T1-T15 | Done |
| §10 | `--dpllt-show-existential-part`, added after the design was written; covered by T16 | Done |
| §6.5b, §6.6 | `find_bounds_refutation` plus core blocking, added after the design was written; covered by T18 | Done |
| §6.5b rules R4, R5 | Relation-minimum and bound propagation, with justification propagation in place of a derivation graph; covered by T19 | Done |
| §6.5b rule R0 | A literal and its negation, both asserted; covered by T20 | Done |
| §7.2 | `linearize` admitted to the allowlist, with its monotonicity argument confined to the variables the assertion quantifies; covered by T21, T22 | Done |
| §10, §16 item 2 | `--dpllt-count-abstraction-models` / `--dpllt-abstraction-model-limit`, added after the design was written; covered by T17. Makes the worst-case iteration count measurable per formula without constructing an automaton, but no benchmark set has been measured with it | Done |
| §7.2 | Classification of every pipeline pass as solution-set-preserving or not | **Partly done.** `linearize` is classified and admitted; the other 17 are not, so `restricted` applies that one pass only |
| §16 | The ten unmeasured quantities | **Not measured.** Items 1 and 2 are partially addressed by the engagement figures below; the rest are untouched |

## Changes

| File | Change |
|---|---|
| `amaya/dpllt_automata.py` | New module. Entry points `evaluate_prepared_formula_with_dpllt_automata`, `perform_whole_evaluation_on_source_text_with_dpllt_automata`, `solve_with_dpllt_over_automata`; the symbols listed in design §9 |
| `amaya/config.py` | `DpllTAutomataConfig`, `SolverConfig.dpllt_automata`, the `ASSERTION_OPTIMIZER_MODE_*` constants and `ASSERTION_OPTIMIZER_MODES` |
| `run-amaya.py` | `--use-dpllt-automata`, `--dpllt-assertion-optimizer`, `--dpllt-no-implicant-minimization`, `--dpllt-no-bound-var-projection`, `--dpllt-prefix-cache-entries`, `--dpllt-report`, `--dpllt-show-existential-part`, `--dpllt-count-abstraction-models`, `--dpllt-abstraction-model-limit`; the two mutual-exclusion checks; the `get_evaluation_strategy` branch |
| `tests/test_dpllt_automata.py` | New module, T1-T18; T1-T15 are design §15 in its naming, T16-T18 cover what was added afterwards |
| `docs/DPLLT_WITH_AUTOMATA.md` | Status header, §9 symbol table updated to the implemented names, `intersect_automata` documented |

Neither `amaya/parse.py` nor any pass module is edited: the strategy is injected through the existing
`evaluate_prepared_formula` parameter of `amaya.parse.perform_whole_evaluation_on_source_text`, and
recursive evaluations are routed through the automaton cache by the existing module-attribute
rebinding in `amaya.cse_cache.cse_enabled`.

## Deviations from the design discovered during implementation

| # | Deviation | Reason |
|---|---|---|
| D1 | `intersect_automata` added (design §9). `amaya.automatons.NFA.intersection` asserts `resulting_nfa.used_variables`, so it cannot be handed two trackless operands - which is what an empty `phi` (a trivially accepting automaton) plus an assertion whose every variable was projected away produces | Found by `benchmarks/formulae/tptp/NUM896_1.smt2`, `NUM897_1.smt2`, `NUM898_1.smt2`, which raised `AssertionError` before the helper existed |
| D2 | Asserted literals are carried as abstraction ids, not as nodes, so the design's `collect_asserted_literals_from_sat_model` / `minimize_asserted_literal_set` / `build_assertion_formula_for_literal_set` are `Monotone_Literal_Abstraction.collect_asserted_atom_ids_from_sat_model` / `minimize_asserted_atom_ids` / `build_assertion_formula_for_atom_ids` | The blocking clause and the skeleton evaluation are written in terms of ids; the node is recovered through `Literal_Abstraction_Manager.literal_by_atom_id` where it is needed |
| D3 | `Assertion_Automaton_Builder._is_prefix_caching_applicable` declines the prefix cache when the lazy conjunction construction or the bounded congruence construction would fire | Both build a whole conjunction in one step (`amaya.parse.try_lazy_construct_conjunction`, `amaya.parse.try_construct_bounded_congruence`), which the incremental intersection would replace with one intersection per conjunct. Not anticipated in design §8.2 |
| D4 | `Assertion_Automaton_Builder._build_conjunction_automaton` applies `amaya.parse.minimize_automaton_if_configured` after every intersection and stops as soon as the running automaton has no final states | Mirrors `amaya.parse.evaluate_binary_conjunction_expr`; without it, `-m hopcroft` silently did not apply to assertions |
| D5 | The fall-through evaluates the original root, not the normalized one | An input the strategy does not apply to is then evaluated exactly as the default driver would evaluate it |
| D6 | `_constant_value_of_node` folds `NOT BoolLiteral` into a constant instead of abstracting it as a literal | A Bool constant carries no information for the enumeration; abstracting it would add a variable the SAT solver must assign |
| D7 | `Assertion_Automaton_Builder._project_bound_vars_away` skips variables the automaton does not track | Design §8.2 point 3 anticipated the projection needing care; both backends' `do_projection` assume the variable is one of the automaton's tracks. This is the same assumption `amaya.parse.evaluate_exists_expr` makes and does not check - see the defects below |

## Pre-existing defects encountered

Neither involves this module; both reproduce on a plain `run-amaya.py get-sat` with no new flag, and
neither was fixed.

| # | Defect | Reproduction |
|---|---|---|
| P1 | `amaya.automatons.NFA.union` raises `KeyError` when one operand has no states, which is what an intersection that removed every non-finishing state produces. `amaya.automatons.NFA.rename_states` builds its map from `self.states` but then indexes it with `self.initial_states` | Native backend, a formula of the shape `(or (exists (y) (and A B)) (exists (y) C))` whose first disjunct is unsatisfiable |
| P2 | `amaya.parse.evaluate_exists_expr` projects every bound variable unconditionally; `amaya.mtbdd_transitions.MTBDDTransitionFn.project_variable_away` raises `ValueError: list.index(x): x not in list` when the variable is not one of the automaton's tracks, which happens once a pass has removed the only atom constraining it | MTBDD backend, `(assert (not (exists ((w Int)) (and (<= 0 w) (<= (* -1 x) 0)))))` |

`tests/test_dpllt_automata.py:_compare_verdicts_tolerating_shared_evaluator_defects` skips a
generated formula when the ordinary evaluation raises, for this reason; a formula the ordinary
evaluation decides and the DPLL(T) strategy raises on is a failure, not a skip.

## Verification performed

Commands are given relative to the repository root; every number below was produced by running them.

### Unit and end-to-end tests

- `venv/bin/python -m pytest tests/test_dpllt_automata.py -q`: 77 passed (T1-T22; the end-to-end
  ones are parameterized over the native and MTBDD backends).
- `venv/bin/python -m pytest tests/ -q` (255 passed, 8 skipped, 1 xfailed) with the nine test modules that fail to *collect* on
  `master` excluded (`test_antiprenexing`, `test_div_support`, `test_let_evaluation`,
  `test_nonlinear_term_rewrites`, `test_process_relations_in_ast`, `test_relations`,
  `test_simplification_on_unbound_vars`, `test_state_compression_functions`,
  `test_variable_disambiguation` - all raise `ModuleNotFoundError: No module named
  'amaya.ast_definitions'` before this change): 206 passed, 8 skipped, 1 xfailed.

### Differential benchmark runs

Verdicts of `run-amaya.py get-sat` with and without `--use-dpllt-automata`, 20 s per invocation,
compared per formula.

| Benchmark set | Backend | Formulae | Agree | Disagree | Both timed out |
|---|---|---|---|---|---|
| `benchmarks/formulae/tptp` | native | 46 | 46 | 0 | 0 |
| `benchmarks/formulae/tptp` | MTBDD | 46 | 46 | 0 | 0 |
| `benchmarks/formulae/UltimateAutomizer` | native | 153 | 151 | 0 | 2 |

The two `UltimateAutomizer` timeouts (`Primes_true-unreach-call.c_1657.smt2`,
`Primes_true-unreach-call.c_798.smt2`) timed out under both strategies. One further formula
(`Primes_true-unreach-call.c_276.smt2`) was first recorded as an error from the ordinary
evaluation while other processes were competing for the machine; re-run on an idle machine, both
strategies report `unsat`, and it is counted as an agreement above. No formula produced a verdict
from one strategy and an error or a timeout from the other.

### How often the strategy applies

Parsing, preprocessing and the split only - no automaton constructed. "Engaged" means the split found
at least one positive-existential conjunct and at least one of them contains a disjunction, i.e. the
strategy did not fall through to `amaya.parse.evaluate_prepared_formula_with_automata`.

| Benchmark set | Formulae | Engaged | Fell through | Abstracted literals when engaged (min/median/max) |
|---|---|---|---|---|
| `benchmarks/formulae/tptp` | 46 | 3 | 43 | 3 / 3 / 3 |
| `benchmarks/formulae/UltimateAutomizer` | 153 | 0 | 153 | not applicable |

The `UltimateAutomizer` set exercises the fall-through, not the loop. Every one of its 153
formulae has a positive-existential part without a disjunction, so
`solve_with_dpllt_over_automata` delegates to
`amaya.parse.evaluate_prepared_formula_with_automata` before abstracting anything. What that sweep
establishes is that the split, the eligibility test and the fall-through do not change a verdict on
153 real inputs; it says nothing about the enumeration. On `tptp`, 3 of 46 formulae reach the loop.

The loop's own coverage is therefore carried by the tests: T11-T14 are hand-written for specific
shapes, and T15 compares 120 generated formulae per backend. An additional standalone run of the
same generator over 300 formulae per backend (seed 4242) compared 267 verdicts on the native
backend and 218 on MTBDD - the remainder being formulae the ordinary evaluation itself raised on,
see P1 and P2 - with no disagreement.

### Command-line surface

- Each of `--dpllt-assertion-optimizer {none,full}`, `--dpllt-no-implicant-minimization`,
  `--dpllt-no-bound-var-projection`, `--dpllt-prefix-cache-entries 0` runs and produces the same
  verdict as the default configuration on two hand-written formulae, one satisfiable and one not.
- `--use-dpllt-automata --shard` and `--use-dpllt-automata --use-toplevel-sat` both exit with the
  intended error message.

### The bound reasoning on `Problem10_label59`

Measured on `benchmarks/formulae/20190429-UltimateAutomizerSvcomp2019/Problem10_label59_true-unreach-call.c_98.smt2`,
preprocessed with `-O all`. Its positive-existential part has 118 abstracted literals and 13
disjunctions whose branch counts multiply to 93,312.

| Quantity | Value |
|---|---|
| First 100 assertions refutable by variable bounds alone, in the enumeration order *without* core blocking | 100 |
| Of those, refutable using only the 48 necessary literals | 0 |
| Variable contradictory in all 100 | `Var(id=2)`, bounded below by 219 and above by 0 |
Iterations to exhaust the abstraction, by which rules of design §6.5b are enabled. Every row was run
with no automaton constructed and every theory call assumed to refute - the same assumption
`count_minimal_implicants_of_abstraction` makes - so the theory-call column is what the loop would
spend on automata.

| Rules enabled | Iterations | Theory calls | Refutations | Mean core | Time |
|---|---|---|---|---|---|
| None (block the whole implicant) | > 30,000 | > 30,000 | 0 | - | 237 s, limit reached |
| R1-R3 (unit bounds and interval clash) | 21,884 | 21,875 | 9 | 2.0 | 198 s, exhausted |
| R1-R4 (`--dpllt-bound-propagation-rounds 0`) | 18,386 | 18,375 | 11 | 2.2 | 59 s, exhausted |
| R1-R5, 4 rounds | 982 | 923 | 59 | 5.1 | 5 s, exhausted |
| R0-R5, 4 rounds (default) | **20** | **0** | 20 | 3.0 | < 0.1 s, exhausted |

The reduction in theory calls from the first row to the last is at least 30,000 -> 0. Note the mean
core grows from 2.0 to 5.1 literals between rows 2 and 4 while the iteration count falls by a factor of
22: what a clause removes is governed by the number of disjunctions it spans, not by how few literals
it names (`docs/EAGER_THEORY_LEARNING.md` §2).

The rule that concluded each of the 20 refutations in the last row: `interval-clash` 9,
`relation-minimum` 6, `complementary-pair` 5.

**Wall clock, with automata.** `./reproducer.sh` - `--fast -O all --use-dpllt-automata
--dpllt-assertion-optimizer full --astp-cse` - did not terminate within 900 s before R0, R4 and R5
were added. With them it reports `unsat` in **0.43 s**.

**The `unsat` is verified.** Each of the 20 cores was rebuilt as a conjunction and handed to the
automata backend: all 20 have an empty language. The enumeration exhausted after exactly those 20
blocking clauses, so every model of the abstraction contains one of them, and each is theory
unsatisfiable - which is a complete refutation of the formula that does not rest on the bound rules
being correct. The check is 20 automaton constructions and is the one to repeat if the rules change.

## What this record does not establish

1. That the strategy is faster than the ordinary evaluation on any input. No runtime was compared;
   the sweeps above compare verdicts only.
2. The number of loop iterations, the effect of implicant minimization, and the prefix-cache hit rate
   on real inputs. `--dpllt-report` logs the counters that would measure these; they were read only
   on hand-written formulae.
3. Anything about the `full` assertion-optimizer mode beyond the fact that it runs. Its unsoundness is
   inferred from the contract the passes satisfy and from one identified mechanism
   (`theory_reasoning._simplify_formula_using_model_properties` inventing a value for an unseen Bool
   variable); **no input on which `full` and `none` disagree has been exhibited.** One attempt to
   construct one failed, because whole-formula preprocessing reduced the positive-existential part to
   `False` before the split ran.
4. Whether admitting `linearize` to the `restricted` allowlist changes any verdict or any iteration
   count. It was admitted on the argument recorded in design §7.2; the `tptp` sweeps and the test suite
   show no verdict moving, and no formula has been measured on which it fires inside the loop. Note it
   only fires at all when `-O linearize` is also given and the assertion exceeds the pass's growth
   guard - about twenty nodes.
5. The nine remaining items of design §16.
6. Whether the bound reasoning pays on any formula other than `Problem10_label59`. It fired zero
   times on every `tptp` formula that reaches the loop when only R1-R3 were implemented, and that
   measurement has not been repeated for R4 and R5.
7. Whether the bound reasoning helps on a formula whose conflicts the automata backend detects but
   these six rules do not. On `Problem10_label59` it now refutes every assertion, so that formula
   cannot answer the question.
