# Fixpoint optimization pipeline — implementation plan

Companion to `OPTIMIZATION_PIPELINE.md` (the design, as revised by the review).
That document says *what* and *why*; this one says *in what order, in which
files, and how each step is known to be done*.

Each step is meant to be a self-contained commit that leaves the tree green.
Steps 1–2 touch existing code; steps 3–5 add new code without changing any
behaviour; step 6 is the switch-over; step 10 is the cleanup that deletes the
hand-unrolling.

## Step overview

| Step | What | Touches | Behaviour change |
|---|---|---|---|
| 1 | `structural_id.py`: shared keys + observational fingerprint | new file | none |
| 2 | Rewire `connective_child_dedup` onto the shared vocabulary | `connective_child_dedup.py` | none |
| 3 | Pass descriptors, adapters, registry | new `pipeline.py` | none (not called) |
| 4 | The scheduler loop | `pipeline.py` | none (not called) |
| 5 | Config section + CLI flags | `config.py`, `run-amaya.py` | none (defaults off) |
| 6 | Switch `optimize_formula_structure`, legacy body preserved | `parse.py` | **yes, behind a flag** |
| 7 | **Differential validation — stop/go gate** | new `scripts/opt_pipeline_parity.py` | none |
| 8 | `Pipeline_Report` plumbing to the benchmark CSV | `pipeline.py`, `run-amaya.py` | none |
| 9 | Re-tune tiers from the measurements of step 8 | `pipeline.py` registry | yes, data-driven |
| 10 | Delete the hand-unrolling, the legacy body, `purge-twice` | `parse.py`, `config.py`, `run-amaya.py` | removes the escape hatch |
| 11 | *(optional, later)* passes report their own change flag | every pass module | none |

**Stop/go gate: step 7.** Do not proceed to step 10 (which removes the ability
to fall back) until the differential run is clean. Step 7 is also where the two
knowingly-unfaithful adaptations from step 3 — the `Asserted_Model_Properties`
accumulator and unconditional `flatten-connectives` — get their verdict.

**Default posture until step 9:** `optimization_pipeline.enabled` defaults to
`False`. The pipeline is opt-in for the whole of steps 5–8, so a bad merge
cannot affect a benchmark run or an SMT-COMP submission that does not ask for
it. Flip the default in step 9, once there is data.

---

## Step 1 — `amaya/preprocessing/structural_id.py`

**Why:** the pipeline's change detection needs a structural fingerprint. The
keying vocabulary already exists inside `connective_child_dedup.py`, but its
traversal cannot be reused (design §4.1): `_assign_ids` fuses id assignment
with the dedup rewrite, and keys connectives by a `frozenset` of child ids.

**Changes** — new file `amaya/preprocessing/structural_id.py` holding:
- `Node_Key`, `Structural_Id_Table` (`key_to_id`, `next_id`, `get_id`),
  `_make_linear_terms_key`, `_make_atom_key` — moved verbatim from
  `connective_child_dedup.py`, `Node_Id_Table` renamed to
  `Structural_Id_Table`.
- New `compute_structural_id(root, table) -> Tuple[int, int]` returning
  `(root_id, node_count)`. It must:
  - key a connective as `('connective', type, tuple(sorted(child_ids)))` — a
    **multiset**, not a frozenset;
  - **not** collapse single-child connectives and **not** drop duplicate
    children;
  - never write to the tree (no `_id` write-back);
  - count every visited node into the second return value.
- Module docstring stating why this traversal is deliberately separate from
  `_assign_ids`, so the next reader does not "deduplicate" the two.

**Done when** — new `tests/test_structural_id.py` passes:
- (a) structurally identical trees ⇒ equal ids;
- (b) reordered connective children and reordered atom terms ⇒ equal ids;
- (c) any semantic change (different rhs, different predicate, different var)
  ⇒ different ids;
- (d) **`(and A B A)` and `(and A B)` ⇒ different ids** — regression test for
  the frozenset trap; without it `dedup-connective-children` is invisible to
  the scheduler;
- (e) **two structurally different trees with the same number of distinct
  subformulae, fingerprinted against the same table ⇒ different ids** —
  regression test for the fresh-table trap;
- (f) ids for the same subformula are stable across two `compute_structural_id`
  calls sharing one table;
- (g) `node_count` matches an independent recursive count.

---

## Step 2 — rewire `connective_child_dedup` onto the shared vocabulary

**Why:** keep one definition of the atom/term keys, so a future change to the
`Relation`/`Congruence` shape cannot make the fingerprint and the dedup
disagree about what "the same atom" means.

**Changes**
- `connective_child_dedup.py` imports `Node_Key`, `Structural_Id_Table`,
  `_make_atom_key`, `_make_linear_terms_key` from `structural_id`.
- Keep `Node_Id_Table` as a module-level alias of `Structural_Id_Table` so the
  public signature of `remove_duplicit_connective_children(ast, id_table=None)`
  and its callers/tests keep working.
- `_assign_ids` stays exactly as it is — same frozenset key, same single-child
  collapse, same `_id` write-back. This step moves code, it does not change it.

**Done when:** `tests/test_cse_cache.py` and the existing dedup tests pass
unchanged, and `git diff` shows no edit to `_assign_ids`' body beyond the
import rename.

---

## Step 3 — descriptors, adapters, registry

**Why:** get every pass behind one uniform signature so the scheduler has
something to schedule. No pass body is touched.

**Changes** — new file `amaya/preprocessing/pipeline.py`:
- `Pass_Tier(IntEnum)`: `NORMALIZE=0`, `CORE=1`, `HEAVY=2`, `FINALIZE=3`.
- `Pass_Context`: `var_table`, plus a `scratch: dict` reserved for the
  accumulator fallback noted below.
- `Pass_Descriptor` exactly as design §5.1, with `self_triggering: bool = True`
  (**not** the `idempotent` field of the first draft — the default must be
  "re-run", or the 9× CER collapses to one call).
- The `_pass_*` adapters of design §5.2.
- `build_registry(solver_config) -> List[Pass_Descriptor]` returning the 17
  passes of design §5.4 in registration order, filtered by `config_flag`.

Three registry details that are easy to get wrong:
- `model-reasoning` and `unconstrained-vars` both carry
  `config_flag='reason_about_models'` — today they share one `if` block
  (`parse.py:210-222`). Do not invent a second flag.
- `flatten-connectives` is registered with `config_flag=None` (unconditional).
  Today `flatten_bool_nary_connectives` runs inside the `rce` and dedup blocks
  regardless of the `flatten_connectives` flag; gating it would silently starve
  CER of its `nary-shape` triggers. `finalize-flatten` and `finalize-refvars`
  are likewise unconditional; `finalize-dedup` stays gated on
  `deduplicate_connective_children`.
- The `-O` name for `inline_bool_var_definitions` is misspelled
  `iniline-bool-definitions` at `run-amaya.py:205`. Either use that spelling as
  the pass name or fix it and keep the typo as an accepted alias — do not
  silently rename it, benchmark scripts pass it.

**Known deviation from `parse.py`, to be validated in step 7:**
`_pass_model_properties` builds a fresh `Asserted_Model_Properties` per
invocation, whereas `parse.py:211-214` threads **one** accumulator through two
consecutive calls. Fresh is the safer default (the accumulator carries
cross-call state such as `vars_eliminated_via_alias`), but it is a behaviour
change. If step 7 shows a regression, thread one accumulator through
consecutive invocations of the same pass via `Pass_Context.scratch`.

**Done when:** `build_registry` is unit-tested for (a) registration order is
deterministic, (b) each descriptor's `config_flag` names a real
`OptimizationsConfig` attribute, (c) `-O all` yields all 17 passes, (d) every
name in the registry that is user-visible appears in `opt_to_config_field`.

---

## Step 4 — the scheduler

**Why:** the loop is the feature.

**Changes** — `Optimization_Pipeline` in `pipeline.py`, implementing design
§6.3 including the five corrections the review made to that pseudo-code:
- one `Structural_Id_Table` for the whole run (never a fresh table per
  measurement);
- `measure(ast, table)` returns `(fingerprint, node_count)` in one traversal;
- `run_count[p] += 1` immediately after the pass runs, **before** the growth
  guard's `continue`;
- `last_run_fingerprint[p]` skip, which is what actually implements "never
  re-run a pass against a formula it has already processed";
- return `current` on a clean fixpoint, `best` only on cycle/budget exit;
  `best_score` is the `(node_count, quantifier_count)` tuple of §6.5.

Plus `refvars_stale` tracking around `requires_referenced_vars`, the finalizer
phase, and `Pass_Stats`/`Pipeline_Report` accumulation (design §8) — build the
report from the start even though nothing consumes it until step 8.

**Also in this step:** update the docstring of `fill_referenced_vars`
(`conditional_equality_resolution.py:92`), which currently scopes it to
hand-built test trees. It is now a scheduled invariant repair. Note in the
docstring that it mutates in place and that passes share subtrees, so the
repair is visible from every tree still holding the node (design §5.5).

**Done when** — new `tests/test_optimization_pipeline.py`, driven by synthetic
descriptors over hand-built trees (no real passes), covers:
- a fixpoint is reached and reported as `termination='fixpoint'`;
- a pass needing *n* applications is driven to its own fixpoint — the direct
  regression test for the `self_triggering` default and thus for P1;
- cycle detection fires on a deliberately oscillating pass pair and returns
  `best`;
- the growth guard discards a result, leaves `current` untouched, **and still
  charges `run_count`** (so `max_runs` is reachable);
- budget exhaustion returns `best`; a clean fixpoint returns `current`;
- a pass is not re-run against a fingerprint it has already seen;
- determinism: the same input twice ⇒ identical `pass_sequence`.

---

## Step 5 — config and CLI

**Changes**
- `config.py`: `OptimizationPipelineConfig` per design §7.1 with
  `enabled: bool = False` (see "default posture" above), `max_pass_applications`,
  `max_wall_time_seconds`, `tier_overrides`, `max_runs_overrides`, `report`.
  Added to `SolverConfig` as `optimization_pipeline`.
- `run-amaya.py`: `--opt-fixpoint` / `--no-opt-fixpoint`, `--opt-budget N`,
  `--opt-report`. These are **not** `-O` options and must stay out of
  `opt_to_config_field` — `-O all` iterates that table and would otherwise flip
  the pipeline on, exactly the way `--astp-cse` and `--use-toplevel-sat` are
  deliberately kept out of it (`run-amaya.py:487-494`).

**Done when:** `run-amaya.py --help` lists the new flags; a no-flag run is
byte-identical to before.

---

## Step 6 — switch `optimize_formula_structure`

**Changes** — `parse.py`:
```python
def optimize_formula_structure(astp, var_table):
    if not solver_config.optimization_pipeline.enabled:
        return _optimize_formula_structure_legacy(astp, var_table)   # today's body, verbatim
    return Optimization_Pipeline(build_registry(solver_config), var_table).run(astp)
```
Today's body moves to `_optimize_formula_structure_legacy` **unchanged** — it
is both the bisection escape hatch and step 7's reference implementation. Both
call sites (`parse.py:412`, `run-amaya.py:839`) are untouched.

**Done when:** the full test suite passes with the flag off *and* on.

---

## Step 7 — differential validation (**gate**)

**Why:** this is the only thing standing between "the pipeline runs" and "the
pipeline is correct".

**Changes** — new `scripts/opt_pipeline_parity.py`, modelled on
`scripts/toplevel_sat_parity.py` (same container-per-run structure, same
timeout/memout-as-verdict handling, same CSV output).

Run it in two sweeps, cheap first:
1. **Formula-level sweep, whole corpus.** Compare the *preprocessed formula*
   from both paths without evaluating anything, via the `convert` subcommand or
   `--show-preprocessed-formula`. Fast enough for `benchmarks/formulae/**` in
   bulk, and it localises a difference to a pass instead of to a verdict.
   Record node counts for both paths.
2. **Verdict sweep.** Full solve on both paths for the corpus the automata
   backend can actually decide, plus `smtcomp25-results/`. Any sat/unsat
   disagreement is a bug and blocks the gate.

Sweep with `-O all`, with the `-O` sets the `smtcomp-submissions/` wrappers
use, and specifically with `-O model-reasoning` (the accumulator change from
step 3).

**Interpreting the size numbers:** "pipeline output ≤ legacy output" is a
sanity check, **not** an invariant, and must not become an assertion.
`miniscope` and `light-sat` may legitimately grow the tree within their
budgets, and a clean fixpoint returns `current`, not the smallest formula seen.
Treat a size regression as a reason to read the `pass_sequence`; gate on
verdict parity plus aggregate automaton-size and wall-clock numbers.

**Done when:** zero verdict disagreements; wall-clock and automaton size are
not systematically worse; any formula where they are has an explanation
recorded here.

---

## Step 8 — reporting

**Why:** step 9 cannot happen without the numbers.

**Changes**
- Log the `Pipeline_Report` table at `INFO` under `--opt-report`.
- Plumb it to the benchmark CSV. Note `optimize_formula_structure` returns only
  an `ASTp_Node` and runs *before* `Evaluation_Result` is constructed, so
  design §8's "attach to `Evaluation_Result`" needs a channel. Cheapest that is
  not a global: an optional `report_sink: Optional[list] = None` parameter on
  `optimize_formula_structure`, filled by the pipeline and read by the caller
  at `parse.py:412`. Both existing call sites keep working unchanged.

**Done when:** a benchmark run emits per-pass `invocations`, `productive`,
`discarded_for_growth`, `total_time_ns`, `nodes_removed`, plus `rounds`,
`termination` and `pass_sequence`.

---

## Step 9 — re-tune the tiers

Apply design §9's rules to the step-8 data: demote low-hit-rate tier-0/1
passes or narrow their `consumes`, promote high-hit-rate tier-2 passes, set
`self_triggering=False` only where a pass is *measured* to be run-once, and fix
growth limits with high `discarded_for_growth` counts.

Flip `optimization_pipeline.enabled` to `True` by default here, if step 7's
numbers support it — not before.

**Done when:** the tier table in `OPTIMIZATION_PIPELINE.md` §5.4 is updated in
the same commit, with the measured hit rate and yield recorded next to it.

---

## Step 10 — delete the hand-unrolling

Only after step 7 is clean and step 9's defaults have had a benchmark cycle.

**Changes**
- Delete `_optimize_formula_structure_legacy`: the 9× CER block
  (`parse.py:241-262`), the doubled `simplify_formula_using_model_properties`,
  the tripled `remove_atoms_satisfied_by_unconstrained_vars`, the doubled
  `remove_vars_with_no_consequences_on_the_model`.
- Remove `do_interval_reasonining_twice` from `OptimizationsConfig` and
  `purge-twice` from `opt_to_config_field`. **Not before this step** — the flag
  is read by the legacy body at `parse.py:207`, so ignoring it while that body
  is still reachable would make the two paths incomparable for exactly the pass
  whose repetition motivated P2. Keep `purge-twice` accepted-and-ignored at the
  CLI for one release so the submission wrappers do not fail on an unknown
  choice.
- Drop the `optimization_pipeline.enabled=False` branch.

**Done when:** `parse.py` is ~110 lines shorter and the suite is green.

---

## Step 11 — *(optional, later)* passes report their own change flag

Migrate passes one at a time from `f(ast) -> ast` to
`f(ast) -> Pass_Result(ast, changed, facts)`, letting a pass declare the facts
it actually produced instead of the conservative static `produces` set, and
skipping the fingerprint traversal when `changed is False`. The scheduler
accepts either signature and falls back to fingerprinting for un-migrated
passes. Pure optimisation of the pipeline itself; not required for correctness,
which is what keeps steps 1–10 mechanical.

---

## Risks carried through the plan

| Risk | Where it is addressed |
|---|---|
| Fingerprint too coarse ⇒ productive passes silently discarded | Step 1 tests (d) and (e) |
| `self_triggering` default wrong ⇒ P1 not actually fixed | Step 4's *n*-application test |
| Fresh `Asserted_Model_Properties` differs from today's shared one | Step 3 note, step 7 `-O model-reasoning` sweep, `Pass_Context.scratch` fallback |
| Gating `flatten-connectives` starves CER | Step 3 registers it unconditionally; step 7 sweeps the wrappers' `-O` sets |
| Repeatedly growth-discarded heavy pass burns traversals | Step 4's `run_count`-before-guard test |
| Losing the fallback too early | Step 10 is last, gated on step 7 |
| `-O all` accidentally enabling the pipeline | Step 5 keeps the new flags out of `opt_to_config_field` |
