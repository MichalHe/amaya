# Design: Eager Theory Learning over the Disjunct Choice Structure

Status: design proposal. Not implemented. Every number attributed to
`Problem10_label59_true-unreach-call.c_98.smt2` below is measured and its provenance is
`docs/DPLLT_PROGRESS.md`; every number attributed to this proposal is derived from those by the cost
model of §5 and is **not** measured. §11 lists what is not established.

Scope: reducing the number of theory calls
`amaya/dpllt_automata.py:_enumerate_implicants` makes, by learning clauses before the enumeration
starts instead of deriving one clause per refuted implicant.

Related: `docs/DPLLT_WITH_AUTOMATA.md` (the loop this modifies, in particular §6.3 minimization and
§6.6 blocking), `docs/PIPELINE_UNSAT_CORES.md` (a different route to the same end, assessed there),
`docs/DPLLT_PROGRESS.md` (the measurements).

---

## 1. The problem

On `Problem10_label59`, with the bounds refutation of `docs/DPLLT_WITH_AUTOMATA.md` §6.5b enabled,
the enumeration performs 21,875 theory calls before exhausting the abstraction. The measured
structure of that formula:

| Quantity | Value |
|---|---|
| Abstracted literals | 118 |
| Literals necessary (present in every model of the abstraction) | 48 |
| Disjunction nodes in the skeleton | 13 |
| Branch counts | seven ternary, six binary |
| Product of branch counts | 93,312 |
| Literals in a typical asserted implicant | 63 |

A refuted implicant yields the clause `OR_{l in T} NOT alpha(l)` over its `|T| = 63` literals. Of
those, 48 are necessary, so `NOT alpha(l)` is false in every model of the abstraction for each of
them: those disjuncts are inert and the clause is *effectively* over the remaining ~15 literals.
Those 15 encode one selection in each of the 13 disjunctions.

**A clause therefore removes one point of the 93,312.** That is the measured behaviour: the theory
call count and the number of surviving points agree.

The same arithmetic explains why the bounds refutation is effective where it applies: its clause has
two literals, spans at most two disjunctions, and removes every point agreeing on those two
selections. Nine such clauses removed the region all of the first 100 implicants belonged to.

---

## 2. The quantity that governs clause strength

Let the disjunctions be `D_1 ... D_n` with branch counts `b_1 ... b_n`, and let a **point** be one
selection per disjunction. Write `span(C)` for the set of disjunctions a clause `C` mentions a
literal of.

> A clause removes the fraction `1 / PRODUCT_{i in span(C)} b_i` of the space.

| Clause | Span | Fraction removed on `Problem10_label59` |
|---|---|---|
| Refuted implicant (current, §6.6) | all 13 | 1 / 93,312 |
| Bounds refutation core (§6.5b) | at most 2 | 1/4 to 1/9 |
| A clause spanning one disjunction | 1 | 1/2 or 1/3 |

**The literal width of a clause is not what matters; the number of disjunctions it spans is.** A
five-literal clause spanning two disjunctions removes thousands of times more than a fifteen-literal
clause spanning thirteen.

This design produces clauses of span 1 and span 2, and produces them without first enumerating the
points they remove.

---

## 3. Definitions

| Term | Definition | Computed by |
|---|---|---|
| Necessary literal | An atom `a` such that the skeleton is false when `a` is false and every other atom true | `evaluate_monotone_skeleton(skeleton, every_atom - {a})`; proposed symbol `find_necessary_atom_ids` |
| Mandatory core | The set of necessary literals. Contained in every implicant, by definition | as above |
| Core automaton | The automaton for `phi AND (mandatory core)` | `parse.run_evaluation_procedure` once, then retained |
| Branch | A child of a `Monotone_Skeleton_Node_Type.DISJUNCTION` node | traversal of `Monotone_Literal_Abstraction.skeleton` |
| Branch witness | One minimal implicant of a branch's own subtree | `minimize_asserted_atom_ids` restricted to that subtree |

A branch containing a nested disjunction has more than one minimal implicant. §4.4 states how that is
handled and what it costs in completeness.

---

## 4. The proposal

### 4.1 Build the core automaton once

`NFA(phi AND mandatory core)` is built once and used as the fixed operand of every test below and of
every subsequent theory call. This also removes the per-iteration reconstruction of the 48 mandatory
literals that the loop performs today - on `Problem10_label59`, 48 of the 63 literals in every
assertion are rebuilt on every one of the 21,875 iterations.

Note the core automaton is not small: intermediates of ~56,000 states were observed while building
comparable conjunctions on this formula (`docs/DPLLT_PROGRESS.md`, deviation D3 discussion). The
saving is in not rebuilding it, not in each intersection being cheap.

### 4.2 Unit learning

For each branch `b`, intersect the core automaton with the automaton for `b`'s witness. On an empty
intersection, add the clause

```
OR_{l in witness(b), l not necessary} NOT alpha(l)
```

The necessary literals are omitted because they are true in every model, so including them would add
inert disjuncts. The clause spans one disjunction and removes `1/b_i` of the space.

Cost: one theory call per branch. `Problem10_label59` has 32 branches.

### 4.3 Pairwise learning

For each pair of branches `b, b'` belonging to **different** disjunctions and surviving §4.2,
intersect the core automaton with the automata for both witnesses. On an empty intersection, add the
clause over the union of the two witnesses minus the necessary literals. The clause spans two
disjunctions and removes `1/(b_i * b_j)`.

Cost: at most `(32^2 - SUM b_i^2)/2` calls on `Problem10_label59`, approximately 450. Fewer in
practice, since branches killed by §4.2 are skipped and each disjunction's own branches are not
paired with each other.

### 4.4 Branches with nested disjunctions

The 13 disjunctions of `Problem10_label59` are not all at the top level; some sit inside a branch of
another. For such a branch the witness is one minimal implicant among several, so a test that reports
"satisfiable" has only established that *this* witness is satisfiable.

Consequence: §4.2 and §4.3 are **incomplete** - they can miss a conflict that only some other witness
of the branch exhibits. They are not unsound: a clause is only ever added after an actual empty
intersection, and the clause names exactly the literals that were asserted.

The alternative - enumerating every witness of every branch - reintroduces the blowup this design
exists to avoid, and is not proposed.

### 4.5 The lazy counterpart: minimize over choices, not literals

When a theory call refutes an assertion during the enumeration proper, the current code blocks the
whole implicant (§6.6). Instead: for each disjunction that contributed literals to the assertion, drop
that disjunction's contribution and re-test. Whatever remains after one deletion pass is a set whose
conjunction is still unsatisfiable, spanning fewer disjunctions.

Cost: at most 13 additional theory calls per refutation on `Problem10_label59`, against 63 for a
deletion pass over literals. QuickXplain over the same 13 dimensions reduces this to
`O(k log(13/k))`.

This is the same construction as option B of `docs/PIPELINE_UNSAT_CORES.md` §8, applied at the
granularity §2 identifies as the governing one.

---

## 5. Cost model

Let `n` be the number of disjunctions, `b_i` their branch counts, `P = PRODUCT b_i`, and `B = SUM b_i`.

| Stage | Theory calls | Clause span |
|---|---|---|
| Core automaton | 1 | - |
| Unit learning (§4.2) | `B` | 1 |
| Pairwise learning (§4.3) | at most `(B^2 - SUM b_i^2)/2` | 2 |
| Enumeration of what survives | unknown | 13, or fewer with §4.5 |

For `Problem10_label59`: `n = 13`, `B = 32`, `P = 93,312`; upfront cost `1 + 32 + ~450 < 500` theory
calls, against the 21,875 measured today. **Whether the enumeration that follows is short is the open
question**, and §8 states the condition it depends on.

---

## 6. Worked example

Small enough to check by hand. `core` is the set of literals in every implicant.

```
core:  0 <= x <= 10  and  0 <= y <= 10
D1:    (x <= 2)      |  (x >= 8)
D2:    (y <= 2)      |  (y >= 8)  |  (y >= 20)
D3:    (y = x + 5)   |  (y = x)
```

`P = 2 * 3 * 2 = 12` points, `B = 7` branches.

**Current behaviour.** The solver returns, say, `D1=(x>=8), D2=(y<=2), D3=(y=x+5)`. All seven
literals are asserted, the intersection is empty, and the clause spans all three disjunctions: it
removes that one point of twelve. The next model differing only in `D2` costs another theory call.

**Unit learning (7 calls).**

| Branch | Against `core` | Result |
|---|---|---|
| `y >= 20` | `core` has `y <= 10` | empty - learn `NOT (y>=20)`, removing `2*1*2 = 4` points |
| the other six | | satisfiable |

Space: 12 -> 8.

**Pairwise learning (~16 calls).**

| Pair | Derivation | Result |
|---|---|---|
| `(x>=8)` and `(y=x+5)` | `y >= 13` against `y <= 10` | empty - clause spans `D1,D3`, removes 2 points |
| `(y<=2)` and `(y=x+5)` | `x <= -3` against `0 <= x` | empty - clause spans `D2,D3`, removes 2 points |

The two clauses overlap on one point, so 3 of the 8 are removed. Five remain, reached without
enumerating any of the removed ones.

---

## 7. Correctness

Every clause this design adds is justified by an empty intersection of an explicitly constructed
conjunction. Writing `S` for the literals asserted in a test (core plus one or two witnesses):

1. The intersection being empty means `phi AND (AND S)` has no solutions.
2. Therefore every literal set containing `S` is also unsatisfiable in conjunction with `phi`.
3. The clause removes exactly those sets.

This is the same argument as `docs/DPLLT_WITH_AUTOMATA.md` §6.6 and requirement R1 of
`docs/PIPELINE_UNSAT_CORES.md` §1, discharged by evaluation rather than by reasoning about any
rewriting. In particular this design needs neither the per-pass classification of §7.2 nor the
derivation graph of `docs/PIPELINE_UNSAT_CORES.md`.

Dropping the necessary literals from the clause (§4.2) is sound because a necessary literal is true in
every model of the abstraction, so `NOT alpha(l)` is false in every model and contributes nothing.
Termination is unaffected: the learned clauses are added before the loop starts and the loop's own
clause-per-iteration discipline is unchanged.

**One assumption is load-bearing and must be checked in code, not assumed:** that the mandatory core
is genuinely conjoined into every assertion. It follows from the definition of necessary literal and
from `minimize_asserted_atom_ids` returning a model of the skeleton, but if minimization is disabled
(`--dpllt-no-implicant-minimization`) the asserted set is whatever the SAT solver returned, which is a
superset of some implicant and therefore still contains the core. Both paths hold; a regression in
either invalidates §4.2's clause form.

---

## 8. Where this fails

The design learns clauses of span 1 and 2. A conflict that requires three or more selections is not
found, and each of its points still costs a theory call.

In the example of §6, the point `D1=(x<=2), D2=(y>=8), D3=(y=x)` is unsatisfiable - `y = x <= 2` and
`y >= 8` - but every one of its three pairs is satisfiable against `core`:

| Pair | Witness |
|---|---|
| `(x<=2)` and `(y>=8)` | `x=0, y=8` |
| `(x<=2)` and `(y=x)` | `x=y=0` |
| `(y>=8)` and `(y=x)` | `x=y=8` |

So pairwise learning misses it.

If conflicts on `Problem10_label59` are predominantly of arity three or more, this design spends ~500
theory calls and leaves the enumeration where it started. The available evidence is weak in both
directions: the nine bounds refutations that do fire are all two-literal
(`docs/DPLLT_PROGRESS.md`), which is consistent with low arity, but nothing establishes that the
remaining 21,875 conflicts are of the same shape.

Extending to triples costs `O(B^3)` - approximately 4,900 calls for `B = 32` - which is still below
21,875, but the ratio degrades quickly with `B` and no formula other than this one has been examined.

---

## 9. Module layout

New symbols in `amaya/dpllt_automata.py`:

| Symbol | Role |
|---|---|
| `find_necessary_atom_ids(abstraction) -> FrozenSet[int]` | §3 |
| `Choice_Structure` | The disjunction nodes, their branches, and each branch's witness |
| `extract_choice_structure(abstraction) -> Choice_Structure` | §3, §4.4 |
| `Learned_Clause` | Atom ids plus the span, for the report |
| `learn_unit_conflicts(...) -> List[Learned_Clause]` | §4.2 |
| `learn_pairwise_conflicts(...) -> List[Learned_Clause]` | §4.3 |
| `minimize_refutation_over_choices(...) -> Set[int]` | §4.5 |

Integration: `solve_with_dpllt_over_automata` builds the core automaton and runs the learning stages
after `abstract_chi_into_monotone_sat_formula` and before `_enumerate_implicants`, adding each learned
clause to the solver via the existing `bootstrap_with` formula or `add_clause`.

Configuration, following the existing fields of `amaya/config.py:DpllTAutomataConfig`:

| Field | Default | Flag |
|---|---|---|
| `learn_unit_conflicts` | proposed `False` until measured | `--dpllt-learn-units` |
| `learn_pairwise_conflicts` | proposed `False` until measured | `--dpllt-learn-pairs` |
| `minimize_refutations_over_choices` | proposed `False` until measured | `--dpllt-choice-cores` |

All three default off: this design is unmeasured, and the loop it modifies is itself experimental.

---

## 10. Staged plan

| Step | Content | Gate |
|---|---|---|
| 1 | `find_necessary_atom_ids`, `extract_choice_structure`; report the counts under `--dpllt-report` | Confirms 48 / 13 / 32 against `docs/DPLLT_PROGRESS.md` on `Problem10_label59` |
| 2 | Build the core automaton once and reuse it as the fixed intersection operand | Verdicts unchanged on `tptp` and on the generated formulae of T15 |
| 3 | Unit learning (§4.2), 32 calls | **Decision point.** The number of branches killed says whether the structure is exploitable. If zero, stop |
| 4 | Pairwise learning (§4.3) | Measure the iteration count against the 21,884 baseline |
| 5 | Choice-level refutation minimization (§4.5) | Measure separately; it is independent of steps 3-4 |

Step 3 is the cheap experiment that decides steps 4 and 5. It should be run before any of this is
committed to.

---

## 11. Test plan

| # | Subject | Assertion |
|---|---|---|
| L1 | `find_necessary_atom_ids` | On a hand-built abstraction, returns exactly the atoms whose removal falsifies the skeleton |
| L2 | `extract_choice_structure` | Finds every disjunction node and one witness per branch; a witness satisfies its branch's subtree |
| L3 | `learn_unit_conflicts` | On the §6 example, learns exactly `NOT (y>=20)` |
| L4 | `learn_pairwise_conflicts` | On the §6 example, learns exactly the two clauses of §6 |
| L5 | Clause soundness, brute force | For every learned clause and every point it removes, the corresponding assertion is unsatisfiable when evaluated on its own |
| L6 | Arity-3 conflict | On the §6 example, the point `(x<=2, y>=8, y=x)` is *not* removed by any learned clause - guards against an unsound over-removal that would look like an improvement |
| L7 | `minimize_refutation_over_choices` | The result is still unsatisfiable and spans no more disjunctions than the input |
| L8 | End-to-end | Verdicts unchanged with each stage on and off, on `tptp` and on the T15 generated formulae |

L6 is the test that distinguishes this design working from it being wrong: an implementation that
removed the arity-3 point would report UNSAT faster and incorrectly.

---

## 12. Quantities this document does not establish

1. The arity distribution of the conflicts on `Problem10_label59` - the single quantity that decides
   whether this design pays. Step 3 of §10 measures a lower bound on it cheaply.
2. The number of theory calls remaining after §4.2 and §4.3 on that formula.
3. The cost of one intersection against the core automaton, which sets the price of all ~500 upfront
   calls. Only an unrelated intermediate size (~56,000 states) has been observed.
4. Whether the choice structure of any formula other than `Problem10_label59` has a comparable shape;
   the three `tptp` formulae that reach the loop each perform one iteration
   (`docs/DPLLT_PROGRESS.md`), so they cannot discriminate.
5. Whether §4.5 alone, without §4.2 and §4.3, is enough.
6. The completeness cost of the single-witness rule of §4.4.
