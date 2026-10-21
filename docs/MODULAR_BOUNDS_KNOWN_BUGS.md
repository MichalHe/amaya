# Modular bound propagation: known soundness bugs

Status: the five soundness bugs A, B, C, E and G found in the audit are fixed in the commit following
`bb96ac8`; see "Fixed bugs". The defects under "Unfixed defects" remain.

Scope: `amaya/preprocessing/modular_bounds.py`, introduced in commits `3191828`, `22a4a94` and
`1b65796`.

Enablement: the pass is disabled by default (`amaya/config.py:propagate_modular_bounds` defaults to
`False`). It is enabled by `-O modular-bounds`, and also by `-O all`, which sets every
optimization flag (`run-amaya.py`, handling of `'all' in args.optimizations`).

Claimed contract: `amaya/preprocessing/modular_bounds.py:rewrite_quantifier_with_modular_bounds`
states that, with `fold_shared_variables=False`, the rewrite preserves the solution set of the
existential block. Each of bugs A, B, C, E and G violated that contract: the original formula was
false for some assignment and the rewritten formula was true for the same assignment.

## Fixed bugs

Each fix is in `amaya/preprocessing/modular_bounds.py`. Each bug has a regression test in
`tests/test_modular_bounds.py`; every one of these tests fails against `bb96ac8` and passes with the
fix.

| ID | Defect | Counterexample (original false, rewrite true) | Fix | Regression test |
|----|--------|-----------------------------------------------|-----|-----------------|
| A | `collect_congruence_system` collected hard bounds on free variables into `bounds`; the rebuild in `rewrite_quantifier_with_modular_bounds` re-emitted bounds of quantified variables only | `exists y. 0 <= y <= 7 and x + y = 0 (mod 8) and 0 <= x <= 2`, `x = 5` | Hard bounds on variables outside `quantifier.bound_vars` are placed in `other_conjuncts` | `test_hard_bounds_on_free_variables_inside_the_block_are_kept` |
| B | `collect_congruence_system` kept two-sided bounds only; the rebuild deleted one-sided bounds of surviving quantified variables | `exists y, z. 0 <= y <= 7 and x + y = 0 (mod 8) and z >= 3 and z - x <= 0`, `x = 0` | `Congruence_System.hard_bound_relations` keeps every hard-bound `Relation` of each quantified variable as written; the rebuild re-emits them for surviving variables | `test_one_sided_bounds_on_surviving_variables_are_kept` |
| C | Rewritten blocks carry `referenced_vars=()` until `propagate_modular_bounds` repairs them after the traversal; `_referenced_vars_of` read that field, so an outer block eliminated a variable used by a nested rewritten block, leaving it unbound | `exists y. 0 <= y <= 7 and x + y = 0 (mod 8) and (exists w. 0 <= w <= 7 and w + y = 1 (mod 8) and x + y <= 2)`, `x = 1` | `_referenced_vars_of` computes occurring variables from the tree structure | `test_a_variable_used_by_a_rewritten_nested_block_is_not_eliminated` |
| E | `Modular_Bound_Fact.is_vacuous` returned `True` for every fact with an empty term, so a false ground fact was dropped | `exists y. 0 <= y <= 0 and y = 1 (mod 2)` | A fact with an empty term is vacuous only if `interval.contains(constant, modulus)`; a false ground fact is kept and encoded by `encode_fact` | `test_a_false_variable_free_fact_is_not_dropped` |
| G | `solve_congruence_for_variable` and `_substitute_into_congruence` built `dict(zip(vars, coefs))`, keeping only the last coefficient of a repeated variable | `exists y. 0 <= y <= 7 and y + y + x = 0 (mod 8)`, `x = -5` | `_coefficient_of_var_in_congruence` sums the coefficients of repeated occurrences | `test_repeated_variables_in_a_congruence_have_their_coefficients_summed` |

Bug identifiers are those assigned during the audit; D and F were candidate identifiers that were not
confirmed.

End-to-end results for the SMT-LIB inputs of bugs A, B and C (expected result: unsat for all three), from
`./venv/bin/python ./run-amaya.py [FLAGS] get-sat FILE`:

| Input | (none), before / after | `-O modular-bounds`, before / after | `-O all`, before / after |
|-------|------------------------|-------------------------------------|--------------------------|
| `a.smt2` | unsat / unsat | sat / unsat | unsat / unsat |
| `b.smt2` | unsat / unsat | sat / unsat | unsat / unsat |
| `c.smt2` | unsat / unsat | sat / unsat | sat / **sat** |

The remaining `-O all` result on `c.smt2` is not caused by `modular-bounds`; see bug H below.

Input `a.smt2`:

```smt2
(set-logic LIA)
(declare-fun x () Int)
(assert (= x 5))
(assert (exists ((y Int)) (and (<= 0 y) (<= y 7) (= (mod (+ x y) 8) 0) (<= 0 x) (<= x 2))))
(check-sat)
```

Input `b.smt2`:

```smt2
(set-logic LIA)
(declare-fun x () Int)
(assert (= x 0))
(assert (exists ((y Int) (z Int)) (and (<= 0 y) (<= y 7) (= (mod (+ x y) 8) 0) (<= 3 z) (<= z x))))
(check-sat)
```

Input `c.smt2`:

```smt2
(set-logic LIA)
(declare-fun x () Int)
(assert (= x 1))
(assert (exists ((y Int)) (and (<= 0 y) (<= y 7) (= (mod (+ x y) 8) 0) (exists ((w Int)) (and (<= 0 w) (<= w 7) (= (mod (+ w y) 8) 1) (<= (+ x y) 2))))))
(check-sat)
```

## Unfixed defects

### Bug H: wrong `sat` under `-O all`, independent of `modular-bounds`

Status: unfixed; cause not identified.

| Input | Expected | (none) | `-O all` | `-O all -N modular-bounds` | Smallest flag set found that yields `sat` |
|-------|----------|--------|----------|----------------------------|-------------------------------------------|
| `c.smt2` (above) | unsat | unsat | sat | sat | `-O linearize -O opt-bottom-exists -O model-reasoning` |
| `e2.smt2` (below) | unsat | unsat | sat | sat | not reduced |

- `c.smt2`: each pair out of `linearize`, `opt-bottom-exists` and `model-reasoning` yields unsat or
  an exception (`linearize` with `opt-bottom-exists` raises `StopIteration`); no single optimization
  yields `sat`.
- `e2.smt2`: no single optimization yields `sat`, and the three-flag set above yields unsat. A greedy
  reduction (drop one flag at a time from the `-O all` set, excluding `lazy`, keeping the drop when the
  result stays `sat`) removed no flag; this result was not investigated further.
- `e2.smt2` is unsat: `5x + y = 0 (mod 5)` forces `y = 0 (mod 5)`, which no `y` in `[1, 3]` satisfies.
- These were observed at `bb96ac8`, both with and without the fixes for A–G applied.

Input `e2.smt2`:

```smt2
(set-logic LIA)
(declare-fun x () Int)
(assert (exists ((y Int)) (and (<= 1 y) (<= y 3) (= (mod (+ (* 5 x) y) 5) 0))))
(check-sat)
```

### Defects of `modular-bounds` that are not unsoundness

| Symbol | Observation | Status |
|--------|-------------|--------|
| `get_hard_bound_semantics` (called from `collect_congruence_system`) | A hard bound with coefficient 0, e.g. `0*y <= -1`, satisfies `Relation.is_hard_bound`; `get_hard_bound_semantics` raises `ZeroDivisionError` | Crash; reproduced at AST level |
| `rewrite_quantifier_with_modular_bounds` | Witness variables are typed as `next(iter(var_table.values())).type`, i.e. the type of the first declared symbol, which is `BOOL` when the first declaration is a Bool | One end-to-end input with a Bool declared first (rewrite applied) returned the correct result; no wrong result observed |
| `amaya/preprocessing/pipeline.py`, `modular-bounds` descriptor | The commit message of `3191828` places the pass in the NORMALIZE tier; the current descriptor uses `Pass_Tier.HEAVY` | Documentation mismatch |

## Audit method

- Each counterexample was evaluated by a brute-force interpreter over a bounded integer range,
  comparing the formula before and after `propagate_modular_bounds`. The interpreter is a copy of
  the `evaluate` function in `tests/test_conditional_equality_resolution.py`.
- End-to-end results were produced with
  `./venv/bin/python ./run-amaya.py [FLAGS] get-sat FILE` at commit `bb96ac8`, for FLAGS in
  {none, `-O modular-bounds`, `-O all`}.
- A random fuzzer generated 12000 single blocks, of which about 2800 were rewritten. Covered:
  moduli 4, 5, 6, 8, 9, 12; negative and non-coprime coefficients; negative and out-of-range rhs;
  variables shared between congruences; empty windows and windows of a full period. With bug E
  patched in memory it found no mismatches in `_normalise_term`, `solve_congruence_for_variable`,
  `_substitute_into_congruence`, `Modular_Interval.contains` or `encode_fact`. Two reported mismatches
  were artifacts of the interpreter's quantifier search range and disappeared with a wider range.
- With the fixes applied:
  - the same fuzzer, seeds 0, 1 and 2 (3000 blocks each), rewrote 683, 722 and 691 blocks. It reported
    one mismatch for seed 0 and one for seed 2. In both, the original formula is true at the reported
    assignment by exact enumeration (witness `z = 15` lies outside the interpreter's search range), so
    both are interpreter artifacts;
  - an extended fuzzer generating hard bounds on the free variable, one-sided bounds, a general
    inequality, repeated variables in a congruence and one nested block (seeds 0 and 1, 1500 formulas
    each) rewrote 102 and 107 formulas and reported no mismatch and no unbound variable.
- Before the fixes, `tests/test_modular_bounds.py` passed (14 tests), and none of those tests covered
  bugs A, B, C, E or G. With the fixes it has 20 tests, all passing; the 6 regression tests fail against
  `bb96ac8`.
- Full suite with the fixes (`./venv/bin/python -m pytest -q tests --continue-on-collection-errors`):
  278 passed, 8 skipped, 1 xfailed, 9 collection errors. The collection errors are import errors of
  modules that no longer exist (e.g. `amaya.ast_definitions` in `tests/test_antiprenexing.py`) and
  occur without the fixes as well.
- The audit and fuzzing scripts were kept in a session scratch directory and are not part of the
  repository; the inputs in this document reproduce bugs A, B, C and H.

## Not established

- The fuzzers used one free variable, moduli up to 12, and at most one level of block nesting.
  Moduli of the size the pass targets (`2**32`) were not fuzzed.
- Placement of a congruence inside a disjunction was examined by reading the code only. Facts are
  derived from the top-level conjunction of a block; a disjunction containing a congruence is placed
  in `other_conjuncts`, which blocks elimination of its variables. No test exercised this.
- How the solver interprets a `Congruence` whose rhs is not reduced modulo the modulus was not
  audited. The pass emits only reduced rhs values.
- Benchmark impact: no benchmark run measured how often bugs A, B, C, E or G changed a result, nor
  whether the fixes change the number of blocks the pass rewrites.
- Bug H: the pass or pass interaction responsible was not identified.
- Congruence linearization (`amaya/preprocessing/unbound_vars.py`; commits `8f9769c`, `1d87c98`,
  `8764a2f`) and the DPLL(T) bound reasoning and literal/negation refutation
  (`amaya/dpllt_automata.py`; commits `92456c3`, `15bff4f`) were not audited. Audits of both were
  started and stopped before producing results.
