# Design: Unsatisfiable-Core Extraction from the Optimization Pipeline

Status: design proposal. Not implemented. No part of this document reports a measurement of the
proposed mechanism; §11 lists what is not established. The classification in §4 is partly unverified
and each row states which.

Scope: recording, inside `amaya/preprocessing/pipeline.py:Optimization_Pipeline`, why a formula was
rewritten to `BoolLiteral(False)`, and reporting the subset of the input's atoms that the rewriting
depended on.

Consumer: `amaya/dpllt_automata.py:_enumerate_implicants`, which turns such a subset into a blocking
clause. See `docs/DPLLT_WITH_AUTOMATA.md` §6.6 for the clause it builds and
`amaya/dpllt_automata.py:find_bounds_refutation` for the one core-producing mechanism that exists
today.

Related: `OPTIMIZATION_PIPELINE.md` (the scheduler this extends), `docs/DPLLT_PROGRESS.md` (the
measurements motivating it).

---

## 1. What the consumer requires of a core

The DPLL(T) loop asserts a set of literals `A`, and on refutation adds the clause
`OR_{l in C} NOT alpha(l)` for some `C` included in `A`. That clause removes **every literal set that
contains `C`**, not only `A`. It is therefore correct exactly when:

> **(R1)** `AND C` is unsatisfiable.

`AND C` unsatisfiable implies every superset conjunction is unsatisfiable, by entailment alone. So R1
is the whole requirement, and it is a statement about `C`, not about the procedure that found it.

Two properties follow, and they are what makes the difference between the designs in §8:

* A procedure that reports `C` only after **evaluating `AND C` itself** discharges R1 directly.
  `find_bounds_refutation` is of this kind: the two bounds it names contradict each other with no
  reference to the rest of the assertion.
* A procedure that reports `C` by **tracing a derivation performed on the whole assertion** does not
  discharge R1 directly. It has to argue that each step of the derivation remains valid when the
  literals outside `C` are removed - and, since the clause removes supersets, also when other
  literals are added. §3 states the condition under which that argument holds.

---

## 2. The proposed mechanism

A derivation graph recorded while the pipeline runs.

| Element | Content |
|---|---|
| Source node | An atom of the pipeline's *input* formula (`Relation`, `Congruence`, `Var`, or a negation of one), identified by `amaya/preprocessing/structural_id.py:compute_structural_id` against a table that lives for the whole pipeline run |
| Derived node | An atom or a `BoolLiteral` a pass produced |
| Edge | `(derived node) <- (the nodes the pass consulted to produce it, the pass name)` |
| Extraction | On reaching `BoolLiteral(False)` at the root, walk the edges backwards; the source nodes reached are the core |

The extracted core is then mapped back to abstraction ids by
`amaya/dpllt_automata.py:compute_literal_abstraction_key` and handed to `make_blocking_clause`.

---

## 3. The soundness criterion: monotone inference

A derivation step is **monotone** when its conclusion follows from the *presence* of the nodes it
consulted, and from nothing else. Formally, for a step producing `d` from consulted set `S`:
`AND S` entails `d`, for every assignment, irrespective of what else the formula contains.

**Only monotone steps may appear in a core's derivation.** A step that consults the *absence* of
something - "variable `x` occurs in no other atom", "no other conjunct constrains `y`" - is not
monotone: a superset assertion can reintroduce the missing occurrence and be satisfiable, while the
blocking clause has already removed it. The failure is silent and permanent: the search space loses a
region that was never refuted, so a satisfiable formula can be reported UNSAT with no diagnostic.

`find_bounds_refutation` is sound precisely because interval intersection is monotone - adding
literals can only tighten an interval, never widen it.

A second, separate exclusion: a step that is only **satisfiability-preserving** rather than
entailment-preserving cannot appear either, because its conclusion is not entailed by its inputs at
all. `amaya/preprocessing/theory_reasoning.py:_simplify_formula_using_model_properties` invents a
value for a Bool variable it has not seen (its `Var` case) and simplifies the remainder under that
assumption; a `False` derived downstream of that is not a proof that the input is unsatisfiable.

This is the same distinction that keeps
`amaya/dpllt_automata.py:ASSERTION_OPTIMIZER_SOLUTION_SET_PRESERVING_PASSES` empty (see
`docs/DPLLT_WITH_AUTOMATA.md` §7.2). **That classification is a prerequisite of this design, not a
consequence of it.**

---

## 4. Classification of the registry

The 21 passes `build_registry` returns under `-O all`, by what the graph would require of each. The
`Verified` column states whether the classification was established by reading the pass, or is
proposed from its name, its `produces` set and its configuration docstring.

### 4.1 Structural — no provenance needed

| Pass | Implementation | Verified |
|---|---|---|
| `flatten-connectives` | `amaya/preprocessing/__init__.py:flatten_bool_nary_connectives` | Yes |
| `dedup-connective-children` | `amaya/preprocessing/connective_child_dedup.py:remove_duplicit_connective_children` | Yes |
| `miniscope` | `amaya/preprocessing/antiprenexing.py:miniscope_quantifiers` | Proposed |
| `finalize-flatten`, `finalize-dedup`, `finalize-refvars` | as above, plus `conditional_equality_resolution.py:fill_referenced_vars` | Yes |

These rearrange the tree without deriving facts about atoms. A node passing through them keeps its
identity, so the graph needs no edges.

### 4.2 Monotone derivational — provenance required, classification admissible

| Pass | Implementation | Verified |
|---|---|---|
| `stomp-negations` | `unbound_vars.py:push_negations_towards_atoms` | Yes — De Morgan plus `Relation.negate`, one input atom per output atom |
| `var-bounds` | `unbound_vars.py:simplify_bounded_atoms` | Proposed |
| `interval-analysis` | `unbound_vars.py:prune_conjunctions_false_due_to_parent_context` | Proposed — consults ancestor bounds, which are present literals |
| `gcd-rewrite` | `unbound_vars.py:simplify_unbounded_equations` | Proposed |
| `minimize-congruences` | `unbound_vars.py:simplify_congruences_on_unbounded_existential_vars` | Proposed — the name indicates an unboundedness precondition; may belong in §4.3 |
| `linearize` | `unbound_vars.py:linearize_congruences` | Proposed |
| `iso-conflicts` | `unbound_vars.py:detect_conflics_on_isomorphic_fragments` | Proposed — derives `False` from `A` and `NOT A`, both present |
| `light-sat` | `unbound_vars.py:convert_and_or_trees_to_dnf_if_talking_about_similar_atoms` | Proposed |
| `squeeze-elimination` | `inner_quantifier_squeeze_elimination.py:eliminate_inner_quantifier_squeezes` | Proposed |

### 4.3 Absence-based — **excluded**, cannot appear in a core

| Pass | Implementation | Verified |
|---|---|---|
| `unconstrained-vars` | `pipeline.py:_pass_unconstrained_vars` runs `theory_reasoning.py:scan_variable_use` over the **whole formula** and rewrites atoms from the resulting `Variable_Use_Info` | Yes |
| `infinite-domain` | `unbound_vars.py:remove_vars_with_no_consequences_on_the_model`, which takes the whole tree and the var table | Yes (from the signature and call site) |
| `inline-bool-definitions` | `unbound_vars.py:inline_bool_var_definitions` | Proposed — inlining a definition depends on there being no competing one |
| `opt-bottom-exists` | `unbound_vars.py:optimize_bottom_quantifiers` | Proposed — drops a quantifier when the body is satisfiable at an extremum, which depends on no other conjunct constraining the variable |
| `rce` | `conditional_equality_resolution.py:resolve_conditional_equalities` | Proposed — eliminates a variable occurring *only* in conditional equalities |

### 4.4 Satisfiability-preserving only — **excluded**

| Pass | Implementation | Verified |
|---|---|---|
| `model-reasoning` | `theory_reasoning.py:_simplify_formula_using_model_properties`, `Var` case | Yes |

### 4.5 Consequence for the sizing

15 of the 18 non-finalize passes need work: 9 need provenance recording (§4.2), 6 must be excluded
and the exclusion enforced (§4.3, §4.4). The exclusion is not "skip the pass" - the pipeline may
still run it - but any `False` whose derivation passes through one of those passes must be reported
as **no core available**, and the caller must fall back to blocking the whole assertion.

The modules involved total ~4,700 lines, of which `amaya/preprocessing/unbound_vars.py` is 2,749 and
hosts 7 of the 9 passes in §4.2.

---

## 5. Mechanism in detail

### 5.1 Recording obligation

Each §4.2 pass gains an optional `Derivation_Recorder` argument. A pass that produces node `d` from
consulted nodes `S` calls `recorder.record(produced=d, consulted=S, pass_name=...)`. A pass that
leaves a node untouched records nothing; absence of an edge means identity.

Nodes are keyed by `compute_structural_id` against one table held for the pipeline run, so that a
node reconstructed by a later pass is recognised as the same node. `Relation` and `Congruence` are
mutable and unhashable (`amaya/relations_structures.py:Relation` defines `__eq__`, which sets
`__hash__` to None), so object identity is unusable and the structural id is the only available key.

### 5.2 Interaction with the scheduler

`Optimization_Pipeline.run` does three things the recorder must survive:

1. **Discards a pass's result** when `growth_factor_limit` is exceeded. Edges recorded during a
   discarded application must be discarded with it. Proposed handling: the recorder takes a snapshot
   before each application and rolls back on discard.
2. **Keeps a `best` formula** that may not be the last one produced. The graph must correspond to
   the returned formula, so the recorder must snapshot alongside `best`.
3. **Runs to a fixpoint**, so one node can be derived more than once by different routes. The
   backward walk must therefore terminate on revisited nodes, and the extracted core depends on
   which route it follows.

### 5.3 Extraction

```
extract_core(graph, false_node, source_node_ids):
    reached, worklist = set(), [false_node]
    while worklist:
        node = worklist.pop()
        if node in reached: continue
        reached.add(node)
        for edge in graph.edges_producing(node):
            if edge.pass_name not in MONOTONE_PASSES: return None   # no core available
            worklist.extend(edge.consulted)
    return reached & source_node_ids
```

Returning `None` rather than a partial core on a non-monotone edge is required: a core missing a
justification is not a core.

### 5.4 Minimality

The walk yields the sources the recorded derivation used, which is not the smallest set with property
R1. Two derivations of the same `False` can reach different sources, and the fixpoint loop makes
which one is recorded depend on scheduling order. Obtaining a minimal core would require deletion
search on top (§8, option B), at which point the graph's advantage over doing only the deletion
search is reduced to the size of the starting set.

### 5.5 Integration

`optimize_assertion_formula` gains a second return value, `Optional[FrozenSet[int]]` - the abstraction
ids of the core, or `None`. `_enumerate_implicants` blocks the core when one is returned and the whole
asserted set otherwise. The existing bounds refutation runs first and is unaffected.

---

## 6. Risks

| # | Risk | Mitigation |
|---|---|---|
| R1 | An edge from a non-monotone pass is not recognised as such, and a satisfiable region is blocked. The verdict flips to UNSAT with no diagnostic | The §4 classification must be verified pass by pass, not proposed. `extract_core` fails closed on any pass name not in the monotone set, including passes added later |
| R2 | A pass is added without provenance recording; its outputs appear as sources and the core names atoms the assertion does not contain | The mapping back through `compute_literal_abstraction_key` fails for such an atom; treat a failed mapping as "no core available" rather than dropping the atom |
| R3 | The graph is recorded but the pipeline result is discarded (§5.2), leaving edges that describe a formula the caller never sees | Snapshot/rollback tied to the same points where the scheduler snapshots the formula |
| R4 | Provenance recording slows every pipeline run, including the ones on the ordinary evaluation path | The recorder is optional; passes take `None` and skip recording when the caller did not ask for a core |
| R5 | The core is non-minimal (§5.4) and blocks less than a minimal one would | Not mitigated. Measurable only after the fact, by comparing against a deletion-search core |
| R6 | The whole design presupposes the §7.2 pass classification, which does not exist and which also gates using the pipeline on assertions at all | The classification is step 1 of §9 |

---

## 7. What this buys over the existing mechanism

`find_bounds_refutation` covers conflicts between two unit bounds on one variable. A pipeline-derived
core would additionally cover, subject to §4.2 being verified: conflicts a congruence participates in,
conflicts exposed only after `gcd-rewrite` or `linearize` rewrote an atom, contradictions between an
atom and its negation found by `iso-conflicts`, and contradictions found by `light-sat`'s DNF
conversion.

On `Problem10_label59` the measured position is that `find_bounds_refutation` fires 9 times and the
remaining 21,875 iterations reach the theory call (`docs/DPLLT_PROGRESS.md`). Whether those 21,875
conflicts are of a kind any pipeline pass detects is **not established** - the pipeline may simply not
refute them, in which case this design yields nothing on that formula.

---

## 8. Alternatives

### Option A — the conjunction-prefix core (free)

`amaya/dpllt_automata.py:Assertion_Automaton_Builder._build_conjunction_automaton` already stops as
soon as the running intersection has no final states. The conjuncts intersected up to that point are a
set whose conjunction has an empty language, which is R1 directly. Reporting the prefix length is the
whole change; it costs no additional automaton operation.

Properties: no pass changes; no classification needed; discharges R1 by evaluation, so §3 does not
apply; covers every conflict the automata backend can see, including those no pass detects. The core
is as long as the prefix, so its quality depends on the conjunct order, which
`_order_conjuncts_canonically` fixes for cache reasons rather than for core quality. Available only
on the incremental path, which `_is_prefix_caching_applicable` currently declines when the lazy
construction would fire.

### Option B — deletion search (QuickXplain)

Given any refutation check `refutes(subset) -> bool` that never reports `True` for a satisfiable
conjunction, extract a minimal core by deletion. QuickXplain performs `O(k log(n/k))` checks for a
core of size `k` out of `n` literals; for `n = 63` and `k = 2` that is approximately 12 checks.

Properties: no pass changes; no classification needed; §3 does not apply, because every reported core
has been evaluated on its own. The check may be the pipeline, the automata backend, or
`find_bounds_refutation`. Cost is the multiplied check count.

### Comparison

| | Graph (§2) | Option A | Option B |
|---|---|---|---|
| Passes to modify | 15 of 18 | 0 | 0 |
| Requires the §7.2 classification | Yes | No | No |
| Discharges R1 | By argument (§3) | By evaluation | By evaluation |
| Fails silently if a pass is misclassified | Yes | No | No |
| Checks per refutation | 1 | 0 | ~12 for `k=2, n=63` |
| Core minimal | No (§5.4) | No | Yes |
| Covers conflicts no pass detects | No | Yes | Yes, if the check is the automata backend |
| Side benefit | Explains any pipeline simplification, usable for debugging the pipeline independently of this loop | None | None |

---

## 9. Staged plan

| Step | Content | Gate |
|---|---|---|
| 1 | Implement option A and measure how far core blocking reduces the iteration count on `Problem10_label59` | If the reduction is small, the conflicts are not core-shaped and steps 3-6 are not worth starting |
| 2 | Implement option B over the automata check; compare core sizes and iteration counts against step 1 | Establishes whether *minimality* is what matters, or merely *having* a core |
| 3 | Verify the §4 classification pass by pass; publish it as `ASSERTION_OPTIMIZER_SOLUTION_SET_PRESERVING_PASSES` | Prerequisite; also unblocks `--dpllt-assertion-optimizer restricted` |
| 4 | `Derivation_Recorder`, the scheduler snapshot/rollback of §5.2, and extraction on a registry restricted to §4.1 plus `interval-analysis` | Differential test: cores from step 4 must be supersets of the ones `find_bounds_refutation` reports on the same assertions |
| 5 | Extend recording to the remaining §4.2 passes, one at a time | Per pass: the differential test above, plus a brute-force check on small formulae that every reported core is unsatisfiable |
| 6 | Measure against steps 1 and 2 | Retain only if it improves on both |

Steps 1 and 2 are each a day or less and answer whether steps 3-6 are worth doing. Steps 3-6 touch
15 passes across ~4,700 lines and add a standing invariant that every future pass maintains.

---

## 10. Test plan

| # | Subject | Assertion |
|---|---|---|
| C1 | `extract_core` on a hand-built graph | Returns exactly the source nodes reachable from the `False` node |
| C2 | `extract_core` with one non-monotone edge on the path | Returns `None` |
| C3 | `extract_core` with a non-monotone edge *off* the path | Returns the core |
| C4 | Cycle in the graph (fixpoint re-derivation) | Terminates, returns the sources |
| C5 | A pass application discarded for growth | Its edges are not in the graph the caller sees |
| C6 | Brute force over small generated conjunctions | Every reported core is unsatisfiable when evaluated on its own by the automata backend |
| C7 | Brute force, superset direction | For every reported core `C` and every superset `S` of `C` drawn from the abstraction's literals, `AND S` is unsatisfiable |
| C8 | Differential against `find_bounds_refutation` | On assertions that function refutes, the pipeline core is a superset of its core |
| C9 | End-to-end | Verdicts unchanged with core extraction on and off, on the `tptp` set and on generated formulae |

C7 is the test that would catch a misclassified absence-based pass (R1), and it is the only one that
does; C6 alone passes even when the core is not upward-closed.

---

## 11. Quantities this document does not establish

1. Whether any of the 21,875 conflicts remaining on `Problem10_label59` after
   `find_bounds_refutation` is detected by any pipeline pass at all.
2. The iteration-count reduction option A yields - step 1 of §9 exists to measure it.
3. The core sizes any of the three designs produces on a real assertion.
4. The runtime cost of provenance recording on the ordinary evaluation path.
5. The correct classification of the 12 passes marked `Proposed` in §4.
6. Whether non-minimal cores (§5.4) block enough less than minimal ones to matter.
