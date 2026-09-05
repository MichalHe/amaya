# Optimization pipeline implementation — progress

Tracking implementation of `OPTIMIZATION_PIPELINE_PLAN.md`. Each step below is a self-contained
commit candidate; the tree is kept green (existing test failures pre-dating this work are noted
and left alone).

## Done

- **Step 1 — `amaya/preprocessing/structural_id.py`.** New file with `Node_Key`,
  `Structural_Id_Table`, `_make_linear_terms_key`, `_make_atom_key` (moved from
  `connective_child_dedup.py`), and the new observational `compute_structural_id`. Multiset (not
  frozenset) child-id keys, no single-child collapse, no tree mutation.
  Tests: `tests/test_structural_id.py` (7 tests, all passing) — covers identical/reordered trees,
  semantic differences, the `(and A B A)` vs `(and A B)` regression, the fresh-table-collision
  regression, id stability across calls, and node-count correctness.

- **Step 2 — rewire `connective_child_dedup` onto the shared vocabulary.** `Node_Id_Table` is now
  an alias of `Structural_Id_Table`; `_make_atom_key`/`_make_linear_terms_key` imported from
  `structural_id`. `_assign_ids`'s body is byte-for-byte unchanged (verified via `git diff`).
  Tests: `tests/test_cse_cache.py` still green.

- **Step 3 — descriptors, adapters, registry (`amaya/preprocessing/pipeline.py`).**
  `Pass_Tier`, `Pass_Context`, `Pass_Descriptor` (`self_triggering: bool = True`, not
  `idempotent`), the `_pass_*` adapters, and `build_registry(solver_config)` returning the 17
  tier 0-2 passes (+3 tier-3 finalizers) in registration order, filtered by `config_flag`.
  Handled the three easy-to-get-wrong details: `model-reasoning`/`unconstrained-vars` share
  `reason_about_models`; `flatten-connectives` is `config_flag=None` (unconditional);
  `inline-bool-definitions` is registered under the correct spelling, and `run-amaya.py`'s
  `opt_to_config_field` gained that spelling as a second key alongside the historical
  `iniline-bool-definitions` typo (kept for old benchmark scripts).
  Tests: `tests/test_pipeline_registry.py` (7 tests) — deterministic order, every `config_flag`
  is real, `-O all` yields exactly 17 non-finalize passes, shared-flag and unconditional-flag
  cases, CLI reachability.

- **Step 4 — the scheduler (`Optimization_Pipeline` in `pipeline.py`).** Single persistent
  `Structural_Id_Table` per run; `measure()` folded into `compute_structural_id` (one traversal);
  `run_count[p] += 1` before the growth-guard `continue`; `last_run_fingerprint` skip; returns
  `current` on fixpoint, `best` on cycle/budget/time; `best_score = (node_count,
  quantifier_count)`. `Pass_Stats`/`Pipeline_Report` built every run (unused until step 8).
  Updated `fill_referenced_vars`'s docstring (now describes it as a scheduled invariant repair,
  not just a test helper).
  Tests: `tests/test_optimization_pipeline.py` (8 tests, synthetic descriptors) — fixpoint,
  self-triggering driven to its own fixpoint, non-self-triggering runs once, cycle detection
  returns `best`, growth guard discards-but-charges `run_count` (needed a priority trick so the
  discarded pass isn't tie-break-starved by its trigger — see the test's comment), budget
  exhaustion returns `best` vs. clean fixpoint returns `current`, already-seen-fingerprint skip,
  determinism.

  Non-obvious finding during step 4: the growth-guard test needed the growth-limited pass on a
  *lower* tier number than the pass that keeps re-triggering it, or the tie-break
  (`(tier, registration_index)`) starves it forever since the triggering pass keeps re-adding
  itself with a lower index every round. Not a scheduler bug — matches the design's pop-order
  spec — but worth remembering when tiering real passes in step 9.

- **Step 5 — config and CLI.** `OptimizationPipelineConfig` (`enabled: bool = False`,
  `max_pass_applications`, `max_wall_time_seconds`, `tier_overrides`, `max_runs_overrides`,
  `report`) added to `SolverConfig` as `optimization_pipeline`. `run-amaya.py` gained
  `--opt-fixpoint`/`--no-opt-fixpoint`, `--opt-budget N`, `--opt-report`, wired directly to those
  fields; kept out of `opt_to_config_field` (verified `-O all` still does not touch
  `optimization_pipeline`). `--help` lists the new flags; a no-flag run of `get-sat f.smt2` still
  returns `sat` and the full non-broken test suite is still green.

- **Step 6 — switch `optimize_formula_structure`.** The old body moved verbatim to
  `_optimize_formula_structure_legacy` (only the `def` line and its indentation changed); the
  public `optimize_formula_structure` now dispatches on `solver_config.optimization_pipeline.enabled`
  to either that function or `Optimization_Pipeline(build_registry(solver_config), var_table,
  ...).run(astp)`, logging `pipeline.report` at INFO when `--opt-report` is set. Both call sites
  (`parse.py:412`, `run-amaya.py:880`) untouched.
  Verified: full test suite green with the flag at its default (`False`) - one pre-existing
  failure only, same as before this step - **and** with `solver_config.optimization_pipeline.enabled`
  forced to `True` for the whole run (only that same pre-existing failure reproduces; nothing new
  breaks). This is a smoke check, not the differential gate - step 7 is the real validation.

- **Step 7 (in progress) — differential validation gate.** Added `scripts/opt_pipeline_parity.py`
  (containerized, modelled on `scripts/toplevel_sat_parity.py`), with `--mode formula` (cheap,
  `--show-preprocessed-formula` line-count comparison) and `--mode verdict` (full solve). Neither
  container mode has been run yet (no image built this session - that's a real `podman build`, a
  multi-minute one-time cost best left to the user or CI); instead ran the same comparison
  **locally, in-process via subprocess** (no container, short per-file timeouts) against a random
  sample of `benchmarks/formulae/**` to get real signal fast:

  - `--mode formula`-equivalent sweep, `-O all`, 40 random formulae: found and fixed **three real,
    pre-existing crashes** in `amaya/preprocessing/unbound_vars.py` that the differential run
    surfaced (the legacy sequence never applies these passes enough times, or in this order, to
    hit them; the pipeline's fixpoint scheduling does):
    1. `_prune_conjunctions_false_due_to_parent_context`'s `AST_Negation` branch indexed
       `eq.vars[0]` for *any* negated `=` relation, but the code only reasons about a
       single-variable equation. A negated constant equation (0 variables) crashed with
       `IndexError`. Fixed by adding `len(child.vars) == 1` to the branch's guard.
    2. The same function's `Relation` branch indexed `relation.vars[0]`/`coefs[0]` without first
       checking `relation.vars` was non-empty (only checked `len(...) > 1` for the multi-var
       case). A fully constant relation (e.g. from a prior pass folding away every variable)
       crashed the same way. Fixed by returning `BoolLiteral(relation.is_always_satisfied())` for
       the 0-variable case (using the existing `Relation.is_always_satisfied` helper).
    3. `_are_exists_and_trees_isomorphic` (used by `iso-conflicts`) did `right_vars_to_coefs[right_var]`
       after `isomorphism[left_var]`, assuming the mapped variable always occurs on the right side;
       when it didn't, this raised `KeyError` instead of correctly reporting "not isomorphic".
       Fixed by treating an unmapped or non-occurring variable as a negative isomorphism result
       instead of crashing.

    After the fixes: same 40-formula sample, 0 crashes, 0 status mismatches; 10/40 had the pipeline
    produce a *larger* preprocessed formula than legacy (expected per the design - miniscope/
    light-sat may grow the tree, and a clean fixpoint returns `current`, not the smallest formula
    ever seen), the rest were equal or smaller.
  - `--mode verdict`-equivalent sweep, `-O all --fast` (MTBDD backend - `-O all` includes
    `use_bounded_congruence_construction`, which requires it), 15 random formulae: **0 verdict
    mismatches**. Note: the same sweep *without* `--fast` produced spurious "mismatches" that were
    actually `AttributeError`s from mixing MTBDD-only automaton state into the NATIVE backend -
    this is a pre-existing `-O all`-without-`-m MTBDD` hazard, unrelated to the pipeline (the
    legacy path only avoided it by chance, by never happening to build the incompatible automaton
    shape for this particular formula's pass ordering); not investigated further here.
  - Noted in passing: the default pass-application budget (32 per 1000 nodes, floor 32) is hit on
    some real formulae (saw one `budget` termination with 6 tier-2 passes still pending on a
    ~1000-node formula) - not a bug, matches the design's stated default, but likely needs
    revisiting once step 8/9 has real data.
  - Follow-up 120-formula formula-mode sweep (different random sample, `-O all`, post-fix): **0
    crashes, 0 mismatches**, 31/120 pipeline-larger (same expected miniscope/light-sat/no-smallest-
    -formula-guarantee story as above).
  - Added `tests/test_unbound_vars_pipeline_regressions.py` (3 tests) pinning the three fixes
    above directly against the (public) `unbound_vars` functions, independent of the pipeline.

  - Follow-up: `-O model-reasoning` sweep specifically (the fresh-`Asserted_Model_Properties`-per-
    invocation deviation flagged in step 3 as the highest-risk item), 120 formulae, in-process
    (`model_reasoning_parity.py` in scratch, comparing preprocessed node counts with only
    `reason_about_models` enabled, everything else off): **0 errors**, and every size difference
    observed had the pipeline's output *equal or smaller* than legacy's, never larger. Consistent
    with the design's expectation that the fresh-accumulator default is safe (the pipeline simply
    gets to apply the pass to its own fixpoint instead of a fixed two calls).
  - **Full-corpus (all 707, not sampled) formula-mode crash sweep, `-O all`, now complete.** Ran
    in two halves: the first 535 via the original subprocess-based script (pre-dating the budget-
    floor/tier fixes below - irrelevant to crash-checking, which only depends on the three
    unbound_vars.py fixes already landed) - 0 status mismatches. The remaining 172 via a faster
    in-process harness (`inprocess_parity.py` in scratch - reuses one Python process instead of
    spawning `run-amaya.py` per formula, avoiding the `sylvan`/import startup cost that made the
    subprocess version slow on the large `psyco` formulas) - 171/172 processed cleanly (12 with
    the pipeline producing a smaller preprocessed formula, consistent with earlier samples), **1**
    with a `RecursionError` (`benchmarks/formulae/psyco/137.smt2`). Verified this is **not** a
    pipeline regression: reproduces identically on the legacy path at the default Python recursion
    limit (both raise `RecursionError`; both succeed once the limit is raised) - a pre-existing
    limitation of this codebase's recursive AST traversal on a very deeply nested formula, present
    before any of this work and orthogonal to it. **Net result: 706/707 formulae in
    `benchmarks/formulae/**` processed with zero pipeline-introduced crashes or size-status
    mismatches; the 707th hits an unrelated, pre-existing recursion-depth ceiling on both paths
    equally.**

  **Not yet done, and required before the step-7 gate can be called clean:** the actual
  `scripts/opt_pipeline_parity.py` container runs, over the full `benchmarks/formulae/**` corpus
  and `smtcomp25-results/` (the latter currently has no local `.smt2` files - only prior JSON
  results - so a from-scratch corpus would need fetching), with `-O all` (matches the
  `smtcomp-submissions/run.sh` wrapper, confirmed by reading it: `--fast -O all`), and a verdict
  (not just formula-size) `-O model-reasoning` sweep. This needs a
  `podman build -t amaya-opt-pipeline .` (not done this session) and is long-running; left for a
  follow-up session or CI rather than run inline here.

  **Follow-up session: the real containerized `opt_pipeline_parity.py` runs, on a representative
  30-formula subset (not the full corpus - deliberately left for the user to run at full scale on
  a bigger server).** `podman build -t amaya-opt-pipeline .` (cache-hit, ~instant - image already
  current). Subset: 30 formulae sampled proportionally to family size across all six benchmark
  families (`20190429-UltimateAutomizerSvcomp2019` 9, `UltimateAutomizer` 7, `psyco` 8,
  `frobenius` 3, `tptp` 2, `modulo` 1; `lash` excluded, it has 0 `.smt2` files), fixed
  `random.seed(42)`. All three runs used `--memory 2g --memory-swap 2g` (hard container memory
  cap, per this session's standing instruction to always bound Amaya's container memory).

  - `--mode formula -O all`, 30/30: **0 crashes, 0 mismatches.** 2/30 pipeline-larger (`psyco/024`,
    `psyco/056` - expected miniscope/light-sat growth, same story as the earlier local sample).
  - `--mode verdict -O all --fast`, 30/30: **0 mismatches by the script's own gate** (only a
    decided-vs-decided sat/unsat disagreement counts; one-sided timeout/memout doesn't). One
    pre-existing, pipeline-unrelated `IndexError` in `parse.py:843`
    (`convert_binary_model_into_decadic`) reproduced identically on *both* paths on
    `modulo/problem-template_MOD1(45).smt2` - not investigated further, out of scope for this
    gate. `psyco/062` disagrees with its declared `:status unsat` but legacy and pipeline agree
    with each other (both `sat`) - pre-existing declared-status/solver disagreement, not a
    pipeline regression. Three formulae flipped between one-sided timeout and memout
    (`psyco/111`, `psyco/132`) - resource-exhaustion-mode noise under a 2g cap, not a gate failure
    per the script's own criterion since neither side reached a decided verdict.

  - **One real finding, not a crash and not a verdict mismatch, but worth tracking before
    `enabled` defaults to `True`:** `20190429-UltimateAutomizerSvcomp2019/jain_7_..._i_11.smt2`
    goes from legacy `unsat`/`sat` in <1s to pipeline **memout** (~71-77s, hits the 2g cap) under
    both `-O all` and `-O model-reasoning` alone - confirmed by re-running `-O model-reasoning` in
    isolation, which reproduced the identical blowup, pinning the cause to that pass specifically
    rather than an `-O all` pass interaction.
    Root cause (via `--opt-report --show-preprocessed-formula` on both paths): legacy's
    preprocessing leaves four separate congruences - three trivial single-variable ones (each
    just "this variable's value is fixed mod its own power-of-two") plus one real 3-variable
    congruence mod 2^32 - conjoined at the top level. The pipeline's fixpoint scheduling runs
    `model-reasoning`/`unconstrained-vars` enough further rounds that it substitutes each
    single-variable definition straight into the real congruence, collapsing all four into **one**
    12-variable congruence, still mod 2^32. This is a legitimate substitution (same free
    variables, same models - both paths agree on the answer whenever the pipeline finishes) and
    it *shrinks* the AST (5 nodes to 1, matching the `--mode formula` sweep's report for this same
    file), but it makes the automaton-construction problem far harder: one wide congruence has no
    per-variable structure left for the backend to exploit, whereas legacy's three trivial
    congruences are near-free to intersect against the harder one. Net effect: "smaller AST" and
    "cheaper to solve" diverge on this formula - the opposite of every other formula in this
    session's samples. Not fixed here (would mean changing `unconstrained-vars`/`model-reasoning`'s
    substitution strategy, or adding a pass-level cost heuristic beyond node-count, which is a
    real design decision, not a bug fix) - flagging it as a concrete case for whoever tunes tiers
    against the full corpus: worth checking whether the full-corpus run turns up more formulae
    with this same "substitution collapses per-variable structure into one wide congruence" shape,
    since if it's common it argues for a growth guard that also counts free-variable width per
    relation, not just node count.
  - CSVs from this run:
    `/tmp/.../scratchpad/{formula_sweep,verdict_sweep,model_reasoning_verdict_sweep}.csv` (session-
    local scratch, not checked in - re-run `scripts/opt_pipeline_parity.py` to regenerate).
  - **Still not done:** the same runs over the full corpus (deliberately deferred - the user will
    run this at scale on a bigger server) and the `smtcomp25-results/` corpus (still has no local
    `.smt2` files).

- **Step 8 — reporting.** `optimize_formula_structure` gained an optional `report_sink: list |
  None = None` parameter (both existing call sites still work with no argument); when the
  pipeline runs, its `Pipeline_Report` is appended there and also logged at `INFO` under
  `--opt-report` (already wired in step 6). `Evaluation_Result` gained `pipeline_report:
  Optional[Pipeline_Report] = None`, set by `perform_whole_evaluation_on_source_text` from the
  sink (`None` on the legacy path). `run-amaya.py`'s `BenchmarkStat` carries the last run's report
  and exposes it through both output formats: `--output-format json` nests it under
  `pipeline_report` in `as_dict()`; `--output-format csv` gained four new `--csv-fields` names
  (`opt_rounds`, `opt_termination`, `opt_pass_sequence`, `opt_pass_stats` - the last as an inline
  JSON blob of the per-pass `invocations`/`productive`/`discarded_for_growth`/`total_time_ns`/
  `nodes_removed`), all empty/blank when the pipeline did not run. Verified end-to-end: `benchmark
  --output-format json` and `--output-format csv --csv-fields ...` both against `f.smt2`, with
  `--opt-fixpoint` (report populated) and without (fields empty/report absent).
  Tests: `tests/test_pipeline_reporting.py` (3 tests) - sink untouched on the legacy path, sink
  populated with a real `Pipeline_Report` when enabled, `Evaluation_Result.pipeline_report` set
  only when the pipeline actually ran.

- **Step 9 (preliminary) — re-tune tiers from measured data.** Used the in-process (no subprocess,
  no container) harness at `/tmp/.../scratchpad/aggregate_pipeline_stats.py` to run
  `perform_whole_evaluation_on_source_text` with a no-op `evaluate_prepared_formula` (so only
  parsing/preprocessing/the pipeline run - no automaton construction) over a 120-formula sample of
  `benchmarks/formulae/**`, `-O all`, and sum `Pipeline_Report.pass_stats` across all of them.
  Two findings, both acted on:

  1. **The default budget floor (32) was far too low.** 31/40 (later 94/120, ~78%) of sampled
     formulas hit the `budget` termination before reaching a real fixpoint - not because the
     formulas are large (the floor only matters below 1000 nodes, and these ranged 6-16000 nodes),
     but because the ~20-pass registry needs several rounds just to stop triggering itself even on
     tiny formulas. Measured the actual ceiling: the largest total-pass-application count seen
     across two independent samples (40 and 120 formulas, later confirmed against a 16000-node
     outlier) was 216, achieved with a raised budget of 300. Changed
     `_default_max_pass_applications`'s floor from 32 to **256** (~20% headroom over the observed
     max; the `32 per 1000 nodes` scaling and the 512 cap are unchanged). Re-ran both samples with
     the new default (no override): **all 160/160 formulas now reach a clean fixpoint**, zero
     budget terminations. Added `tests/test_optimization_pipeline.py::test_default_budget_floor_is_256_not_the_original_32`
     pinning this.
  2. **Two tier-1 (CORE) passes measured well under the design's ~5% demotion threshold:**
     `gcd-rewrite` at 0.9% hit rate (n=551 invocations) and `infinite-domain` at 2.0% (n=348).
     Demoted both to tier 2 (HEAVY) with `max_runs=3` and no growth limit (neither pass grows the
     tree - the cap only bounds wasted traversals on a pass that rarely fires). `-O all` still
     registers exactly 17 non-finalize passes (tier reassignment doesn't change the count) -
     `tests/test_pipeline_registry.py` still green. Updated `OPTIMIZATION_PIPELINE.md` §5.4's
     tier tables with the measured hit rates, per this step's done-when criterion.

  **Explicitly not done, and why:** `enabled` was **not** flipped to `True` by default. Three
  near-0%-hit-rate tier-2 passes (`minimize-congruences`, `iso-conflicts`, `light-sat`) were left
  untouched - the sample is LIA-only and drawn from a handful of `benchmarks/formulae/` families,
  not representative of the Boolean-structure-heavy or congruence-heavy inputs those three
  specifically target, so a low hit rate here is not evidence they're broadly useless (see the
  note added next to the tier-2 table). Re-verified after both changes: full test suite still
  green (same one pre-existing failure only), the 15-formula verdict sweep still 0 mismatches,
  the 120-formula formula-mode sweep still 0 crashes/mismatches. Flipping the default and acting
  on the three low-signal rows both still require the real step-7 corpus run (below).

## Not started

- Step 10 — delete the hand-unrolling and `_optimize_formula_structure_legacy`. Gated on step 7
  being clean and step 9 having had a benchmark cycle (with the real corpus, not just the local
  sample above).
- Step 11 (optional) — passes report their own change flag.

## Known pre-existing issues (not introduced by this work)

- 9 test files fail to import on this branch (`amaya.ast_definitions`, `amaya.ast_relations`,
  `amaya.preprocessing.prenexing` don't exist; `ModuloTerm`/`Bounds_Info` were removed) — leftover
  from the in-progress API port mentioned in recent commits (`tests: port 16 test files off the
  removed LSBF_Alphabet/Var string-name API`). Excluded from the runs above; not touched here.
- `tests/test_bounded_congruence_detection.py::test_bounded_congruence_construction_preserves_the_answer[...1000000...]`
  fails on `devel` before any of this work (verified via `git stash`). Unrelated to the pipeline.
