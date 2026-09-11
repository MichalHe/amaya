# Design: DPLL(T)-style Top-Level Solving with an Automata Theory Backend

Status: implemented in `amaya/dpllt_automata.py`, disabled by default, selected by
`--use-dpllt-automata`. The deviations the implementation made from this document, and the
verification performed, are recorded in `docs/DPLLT_PROGRESS.md`. Section 16 lists what remains
unmeasured; no part of this document reports a measurement.

Scope: a new top-level evaluation strategy, plugged into
`amaya.parse.perform_whole_evaluation_on_source_text` through its `evaluate_prepared_formula`
parameter, alongside the two existing strategies
`amaya.parse.evaluate_prepared_formula_with_automata` and
`amaya.sat_toplevel.evaluate_prepared_formula_with_toplevel_sat`.

New module: `amaya/dpllt_automata.py`.

Related documents: `OPTIMIZATION_PIPELINE.md` (the pass scheduler this design invokes per
iteration), `amaya/sat_toplevel.py` module docstring (a different SAT-driven decomposition of the
same top-level problem), `amaya/cse_cache.py` module docstring (the De Bruijn automaton cache this
design reuses).

---

## 1. Statement of the strategy

The input formula, after `amaya.preprocessing.preprocess_ast` and
`amaya.parse.optimize_formula_structure`, is written as `phi AND chi`, where every quantifier in
`chi` occurs in positive polarity (equivalently, since `preprocess_ast` rewrites `forall` into
`not exists not` — see `amaya/preprocessing/__init__.py:replace_forall_with_exists_handler` — no
`AST_Quantifier` node in `chi` has an `AST_Negation` ancestor inside `chi`).

The strategy is:

| Step | Content | Section |
|---|---|---|
| 1 | Split the top-level conjunction into `phi` (the general part) and `chi` (the positive-existential part) | §4 |
| 2 | Rename the bound variables of `chi` apart | §5.1 |
| 3 | Abstract the literals of `chi` into a monotone Boolean formula; drop the quantifiers | §5 |
| 4 | Build the automaton for `phi` with the ordinary evaluator; retain it for the whole run | §6.1 |
| 5 | Ask the SAT solver for a Boolean model `M` of the abstraction | §6.2 |
| 6 | Minimize `M` to a minimal implicant of the abstraction | §6.3 |
| 7 | Assemble the assertion `exists X. AND(asserted literals)` and run the optimization pipeline on it | §6.4, §7 |
| 8 | Build the automaton for the optimized assertion, reusing cached automata for its parts | §8 |
| 9 | Intersect with the automaton for `phi` and search for a model | §6.5 |
| 10 | On an empty intersection, add a blocking clause over the asserted literals and return to step 5 | §6.6 |

The loop reports SAT as soon as one intersection is non-empty and UNSAT when the SAT solver has no
model left.

---

## 2. Relation to the existing top-level SAT driver

`amaya/sat_toplevel.py` already runs a SAT-driven refinement loop at the top level. The two
strategies differ in what is abstracted and what is asserted:

| Property | `amaya/sat_toplevel.py` | This design |
|---|---|---|
| Abstracted objects | Free Bool variables only; every `Relation`, `Congruence` and `AST_Quantifier` becomes an opaque atom the solver may set either way | Every literal of `chi` (`Relation`, `Congruence`, `Var`, and negations thereof) |
| Boolean model used for | Substituting truth values into the original tree (`substitute_bool_vars`) | Selecting a set of literals to assert |
| What the theory backend receives | A residual formula with the same Boolean structure as the input, minus the substituted variables | A conjunction of literals under one existential prefix, intersected against a fixed automaton for `phi` |
| Applicable when | The formula has free Bool parameters (`has_free_bool_vars`) | The formula has a positive-existential conjunct (§4.2) |
| Abstraction relaxes | The theory atoms | The correlation between a literal and its negation (§5.3) |

The two are independent decompositions and are not combined by this design. Both replace the
`evaluate_prepared_formula` callback, so at most one may be selected per run (§11.3).

The parts of `amaya/sat_toplevel.py` reused verbatim are
`amaya.sat_toplevel.isolated_sat_formula_context` (pysat interns atoms in process-global tables
keyed by the active context), `amaya.sat.make_atom_name_for_theory_atom`,
`amaya.sat.make_atom_name_for_bool_var` and `amaya.sat.compute_atom_abstraction_key`.

---

## 3. Notation and properties of the AST relied upon

`ASTp_Node` (`amaya/relations_structures.py`) is the node algebra: `AST_Connective` (types `AND`,
`OR`, `EQUIV`), `AST_Negation`, `AST_Quantifier`, `Relation`, `Congruence`, `BoolLiteral`, `Var`.

Properties this design depends on, each with the source that establishes it:

| # | Property | Source | Status |
|---|---|---|---|
| A1 | Every `AST_Quantifier` is existential | `amaya/preprocessing/__init__.py:replace_forall_with_exists_handler` | Holds after preprocessing |
| A2 | `ite` and `let` are expanded, implications rewritten, atoms condensed into `Relation`/`Congruence` | `amaya/preprocessing/__init__.py:preprocess_ast` | Holds after preprocessing |
| A3 | Each binder receives a globally fresh `Var` id | `amaya/preprocessing/eval.py:Scoper` | Holds after preprocessing; **not** guaranteed after `optimize_formula_structure` — see A4 |
| A4 | Optimization passes may duplicate a binder, producing two `AST_Quantifier` nodes that bind the same `Var` id (for example when a quantifier is pushed into a disjunction by `amaya/preprocessing/antiprenexing.py:miniscope_quantifiers`) | Not audited | **Unverified.** §5.1 removes the dependency instead of relying on it |
| A5 | `VarInfo.is_formula_param` marks the variables a model is reported over | `amaya/preprocessing/eval.py:VarInfo`, `amaya/parse.py:convert_binary_model_into_decadic` | Holds |
| A6 | `Relation.negate` produces a `<=` relation and is correct only for `<=` operands | `amaya/relations_structures.py:Relation.negate` | Holds |

Definitions used throughout:

* **Literal.** A node of one of the forms: `Relation`, `Congruence`, `Var`, `BoolLiteral`,
  `AST_Negation(Relation)`, `AST_Negation(Congruence)`, `AST_Negation(Var)`.
* **`matrix(f)`.** The result of replacing every `AST_Quantifier` node in `f` by its `child`.
* **`bound_vars(f)`.** The union of `AST_Quantifier.bound_vars` over all quantifier nodes of `f`.
* **Polarity.** As defined in `amaya/sat_toplevel.py:Polarity`: the number of `AST_Negation`
  ancestors, with `EQUIV` placing its children in both polarities at once.

---

## 4. Splitting the formula

### 4.1 Eligibility

A node is **chi-eligible** when it is generated by the grammar

```
eligible ::= literal
           | AST_Connective(AND, eligible+)
           | AST_Connective(OR,  eligible+)
           | AST_Quantifier(bound_vars, eligible)
```

`AST_Connective(EQUIV, ...)` is not eligible, and neither is `AST_Negation` over a non-literal.
Both exclusions are for the same reason: they place a subformula in negative or in mixed polarity,
which breaks the monotonicity the assertion rule of §5.3 requires. No expansion of `EQUIV` into
`(a AND b) OR (NOT a AND NOT b)` is performed.

Note that an eligible node may contain `AST_Negation`, but only directly above a `Relation`, a
`Congruence` or a `Var`. Running `amaya/preprocessing/unbound_vars.py:push_negations_towards_atoms`
before the split increases the number of nodes that qualify: that pass moves negations down through
`AND`/`OR` and stops at quantifiers, so what it leaves behind is either a literal negation
(eligible) or a `NOT exists` (not eligible). This design specifies that pass as a precondition of
the split, run on the whole formula regardless of the `push_negation_towards_atoms` configuration
flag.

### 4.2 The split procedure

```
split_formula_into_phi_and_chi(root) -> (phi_conjuncts, chi_conjuncts):
    conjuncts = root.children if root is AST_Connective(AND) else [root]
    chi_conjuncts = [c for c in conjuncts if is_chi_eligible_subformula(c)]
    phi_conjuncts = [c for c in conjuncts if c not in chi_conjuncts]   # by position, not by value
```

The top-level `AND` is assumed flattened; `amaya/preprocessing/__init__.py:flatten_bool_nary_connectives`
is run before the split regardless of the `flatten_connectives` configuration flag, for the same
reason as `push_negations_towards_atoms`: without it a binary `AND` chain hides conjuncts that would
otherwise be split apart.

Outcomes:

| Case | Action |
|---|---|
| `chi_conjuncts` is empty | The strategy does not apply. Delegate to `amaya.parse.evaluate_prepared_formula_with_automata` and report the delegation in the log |
| `phi_conjuncts` is empty | `phi` is the constant `True`; its automaton is `NFA.trivial_accepting(ctx.get_alphabet())` |
| Both non-empty | `phi = AND(phi_conjuncts)`, `chi = AND(chi_conjuncts)` |

A second applicability condition is worth applying before committing to the strategy: if `chi`
contains no `OR` node, then the abstraction of §5 has exactly one minimal implicant (the set of all
its literals) and the loop performs one iteration that does the same work as the ordinary evaluator,
plus the cost of the abstraction. This design specifies falling back to
`evaluate_prepared_formula_with_automata` in that case. The threshold is a plain
`chi contains at least one AST_Connective(OR)` test; no tuning is proposed and none is measured.

---

## 5. The monotone Boolean abstraction of `chi`

### 5.1 Renaming bound variables apart

Before abstraction, every binder in `chi` is given fresh `Var` ids and the substitution is applied
to its subtree; new `VarInfo` entries (`is_formula_param=False`, type copied from the original) are
added to `ctx.var_table`. Proposed symbol: `freshen_bound_variables_in_subformula`.

This step exists because §6.4 hoists the bound variables of the asserted literals into a single
existential prefix. If two `AST_Quantifier` nodes of `chi` bound the same `Var` id (A4), a hoisted
prefix would force one shared value on two binders that the formula keeps independent, which would
turn satisfiable formulae into UNSAT verdicts. Renaming apart makes the hoisting valid without
depending on an invariant no pass currently states.

Renaming apart also enlarges the alphabet: `LSBF_Alphabet.from_vars(var_table.keys())` is built in
`amaya.parse.perform_whole_evaluation_on_source_text` before the evaluation strategy is invoked, so
either the alphabet is rebuilt after freshening, or freshening happens before the alphabet is
constructed. This design places the split and the freshening inside the strategy callback and
rebuilds `ctx.alphabet` from the extended var table as the first action of the callback. The
consequence for the MTBDD backend — `MTBDDTransitionFn.union_of` asserts that operands agree on
`alphabet_variables` (see `amaya/cse_cache.py:_renamed_copy`) — is that the rebuild must happen
before any automaton is constructed, including the one for `phi`.

### 5.2 Literal identity

Each literal occurrence is mapped to a Boolean variable through an abstraction key:

| Literal form | Key |
|---|---|
| `Relation`, `Congruence` | `amaya.sat.compute_atom_abstraction_key` (structural) |
| `Var` | `('bool-var', var.id)` |
| `AST_Negation(child)` | `('neg',) + key(child)` |
| `BoolLiteral` | Not abstracted; mapped to `pysat.formula.PYSAT_TRUE` / `PYSAT_FALSE` |

Two occurrences that share a key denote the same relation over the same variables (A3 plus §5.1
guarantee that equal `Var` ids are the same variable), so sharing one Boolean variable between them
is exact, not an approximation.

A literal and its negation receive **different** Boolean variables. The abstraction therefore does
not record that they are complementary. §5.3 states why this does not affect the result, and §6.6
states what it costs.

`amaya.sat.Theory_Abstraction_Manager` provides the key-to-id table; the extension needed is a key
function covering `Var` and `AST_Negation`, which `compute_atom_abstraction_key` does not currently
handle (it falls through to `('subformula', id(node))`, keyed on object identity, which would give
two occurrences of the same negated atom two different Boolean variables). Proposed symbol:
`compute_literal_abstraction_key`, in the new module, delegating to
`compute_atom_abstraction_key` for `Relation` and `Congruence`.

### 5.3 The abstraction and the assertion rule

Let `L` be the set of literal keys of `chi` and `alpha: L -> Boolean variables` the injective map of
§5.2. The **skeleton** `S` is `matrix(chi)` with every literal replaced by its Boolean variable and
every quantifier node replaced by its child. `S` is built from Boolean variables and constants using
`AND` and `OR` only, so `S` is monotone: if `N >= M` pointwise and `M |= S`, then `N |= S`.

For a Boolean model `M` of `S`, define

* `asserted(M) = { l in L : M(alpha(l)) = true }`
* `X(M) = bound_vars(chi) intersected with the variables occurring in asserted(M)`
* `Gamma(M) = exists X(M) . AND(asserted(M))` (the **assertion**; the conjunction is over the
  literal nodes, not over their Boolean images)

**Claim S (soundness of one iteration).** `Gamma(M)` entails `chi`.

*Proof.* Let `nu` assign the free variables of `chi` and let `nu |= Gamma(M)`, witnessed by an
extension `nu'` over `X(M)`. Extend `nu'` arbitrarily over the remaining variables of
`bound_vars(chi)`, giving `nu''`. Let `N` be the Boolean assignment induced by `nu''`, that is
`N(alpha(l)) = 1` exactly when `l` evaluates to true under `nu''`. Every `l` in `asserted(M)` is
true under `nu''`, so `N >= M` pointwise. `S` is monotone and `M |= S`, hence `N |= S`, hence
`matrix(chi)` evaluates to true under `nu''`. Finally, `chi` is obtained from `matrix(chi)` by
re-inserting existential binders in positive positions only; by induction over `chi`, if
`matrix(f)` is true under `nu''` then `f` is true under `nu''` restricted to the free variables of
`f` — the literal case is the identity, `AND` and `OR` are monotone in the truth values of their
children, and for `exists Y. psi` the value `nu''(Y)` is the required witness. Applying this at the
root gives `chi` true under `nu`. []

Claim S is what makes asserting only the *positively* assigned literals correct, and it is the sole
place monotonicity is used. It also explains §5.2's separate Boolean variables for `l` and `NOT l`:
if the SAT solver sets both to true, `Gamma(M)` contains a contradictory pair of literals, the
theory call returns an empty automaton, and §6.6 blocks the pair. The abstraction is weaker than one
that links them, never incorrect.

**Claim C (completeness of the enumeration).** If `phi AND chi` has a model `nu`, then some Boolean
model `M` of `S` satisfies "`phi AND Gamma(M)` is satisfiable", and no blocking clause added by §6.6
removes every such `M`.

*Proof.* From `nu |= chi` and A1 plus §5.1 (all binders distinct), an extension `nu''` over
`bound_vars(chi)` exists with `matrix(chi)` true under `nu''`: by induction, `AND` takes the union
of the extensions of its children (disjoint domains), `OR` takes the extension of one true child and
arbitrary values elsewhere (`OR` is monotone, so making another disjunct true does no harm), and
`exists Y. psi` records the witness for `Y`. Let `N` be the Boolean assignment induced by `nu''`;
`N |= S` and `nu''` satisfies every literal of `asserted(N)`, so `phi AND Gamma(N)` is satisfiable.
For the second part, §6.6 adds only clauses of the form `OR_{l in asserted(M_r)} NOT alpha(l)` for
refuted `M_r`. Such a clause excludes `N` only if `asserted(N)` contains `asserted(M_r)`, in which
case `Gamma(N)` entails `Gamma(M_r)` (a conjunction of a superset of literals, under a prefix that
binds a superset of variables none of which occur in `phi`), so `phi AND Gamma(M_r)` would be
satisfiable too, contradicting that `M_r` was refuted. []

**Claim T (termination).** Each iteration adds a clause falsified by the current `M`, over a fixed
variable set of size `|L|`, so the loop performs at most `2^|L|` theory calls and terminates.

---

## 6. The loop

### 6.1 The automaton for `phi`

`nfa_for_phi = run_evaluation_procedure(phi, ctx)` is built once, before the loop, and held for its
duration. `NFA.trivial_accepting(ctx.get_alphabet())` is used when `phi_conjuncts` is empty.

The automaton is used only as an operand of `intersection`, which allocates a new automaton and does
not modify its operands (`amaya/automatons.py:NFA.intersection`,
`amaya/mtbdd_automatons.py:MTBDD_NFA.intersection`). §8.3 states the rule that keeps this true for
every other cached automaton.

### 6.2 Structure

```
solve_with_dpllt_over_automata(root, ctx):
    phi, chi = split_formula_into_phi_and_chi(root)
    if chi is empty: delegate to evaluate_prepared_formula_with_automata

    chi = freshen_bound_variables_in_subformula(chi, ctx.var_table)
    ctx.alphabet = LSBF_Alphabet.from_vars(ctx.var_table.keys())

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula(chi)
        nfa_for_phi = run_evaluation_procedure(phi, ctx)

        with pysat.solvers.Solver(bootstrap_with=abstraction.sat_formula) as sat_solver:
            while sat_solver.solve():
                asserted = collect_asserted_literals_from_sat_model(abstraction, sat_solver.get_model())
                asserted = minimize_asserted_literal_set(abstraction, asserted)        # §6.3

                assertion = build_assertion_formula_for_literal_set(asserted, chi)     # §6.4
                assertion = optimize_assertion(assertion, ctx)                         # §7
                nfa_for_assertion = build_automaton_for_assertion(assertion, ctx)      # §8

                nfa = nfa_for_phi.intersection(nfa_for_assertion)
                binary_model = nfa.find_model()
                if binary_model is not None:
                    return sat result built from binary_model                          # §6.5

                blocking_clause = [-abstraction.solver_var_id(l) for l in asserted]     # §6.6
                if not blocking_clause: break
                sat_solver.add_clause(blocking_clause)

        return unsat result
```

`run_evaluation_procedure` is looked up on the `amaya.parse` module at call time, not imported by
value, so that `amaya.cse_cache.cse_enabled` can replace it (see
`amaya/sat_toplevel.py:_solve_residual_with_automata` for the same requirement and the reason
`ctx.enc_table` has to be cleared between iterations).

### 6.3 Implicant minimization

A monotone `S` is satisfied by the all-true assignment, so an unminimized SAT model tends to assert
every literal of `chi`, which makes the theory call at least as expensive as evaluating `chi`
directly. Minimization reduces `asserted(M)` to a minimal implicant:

```
minimize_asserted_literal_set(abstraction, asserted):
    for l in some order over asserted:
        if evaluate_monotone_skeleton(abstraction.skeleton, asserted - {l}) is true:
            asserted = asserted - {l}
    return asserted
```

`evaluate_monotone_skeleton` is a linear-time evaluation of `S` under the set-as-assignment; no SAT
call is involved. The result is minimal with respect to set inclusion (removing any remaining
element falsifies `S`), and it is a model of `S`, so Claims S, C and T apply to it unchanged.
Different removal orders give different minimal implicants; no order is specified and none is
measured. Proposed removal order: descending estimated automaton size, using
`amaya.parse.estimate_automaton_size`, so that the literals whose automata are largest are the
first candidates for removal.

Minimization also strengthens the blocking clause of §6.6: a clause over a smaller `asserted` set
excludes a larger set of Boolean models.

Two alternatives are rejected here and recorded in §14: setting the solver's default phase to false
(`pysat.solvers.Solver.set_phases`) biases the model but gives no minimality guarantee; asking the
SAT solver for a minimal model directly costs one solver call per removal.

### 6.4 Assembling the assertion

```
build_assertion_formula_for_literal_set(asserted, chi):
    conjunction = AST_Connective(AND, tuple(asserted))          # or the single literal if |asserted| == 1
    bound = tuple(v for v in bound_vars(chi) if v occurs in conjunction.referenced_vars)
    return AST_Quantifier(bound_vars=bound, child=conjunction) if bound else conjunction
```

`referenced_vars` must be filled bottom-up on the freshly built nodes; the evaluator and several
passes read that field (`amaya/preprocessing/conditional_equality_resolution.py:fill_referenced_vars`
is the pipeline's repair pass for it).

The single hoisted prefix is retained rather than dropped. Dropping it and leaving the former bound
variables free would also be correct — emptiness of the final intersection is unaffected by
projecting variables that do not occur in `phi` — but the retained prefix is what makes the assertion
match the shapes the evaluator's specialized constructions require, each of which pattern-matches
`AST_Quantifier` with an `AND` child:

| Construction | Source |
|---|---|
| Lazy conjunction construction (MTBDD only, `do_lazy_evaluation`) | `amaya/parse.py:try_lazy_construct_conjunction` |
| Bounded congruence construction (MTBDD, integers, `use_bounded_congruence_construction`) | `amaya/parse.py:try_construct_bounded_congruence` |
| Lazy child selection | `amaya/parse.py:select_children_to_lazily_evaluate` |

The same prefix is what the quantifier-aware optimization passes consume (§7).

A configuration knob `dpllt_project_bound_vars: bool = True` selects between the two; with it off,
`build_assertion_formula_for_literal_set` returns the conjunction alone and the final verdict is
read off the unprojected intersection. Which setting produces smaller automata is not measured.

### 6.5 Reporting a model

The intersection's `find_model` returns a tuple of alphabet symbols or `None`; an empty tuple is a
model and is not falsy, so the test is `is not None` (the same trap is noted in
`amaya/sat_toplevel.py:solve_with_toplevel_sat`). The decadic model is produced by
`amaya.parse.convert_binary_model_into_decadic(binary_model, nfa.used_variables, formula_params)`
with `formula_params` taken from `is_formula_param` (A5). Variables freshened in §5.1 are not
formula parameters and are therefore not reported.

The returned `Evaluation_Result` (`amaya/parse.py:Evaluation_Result`) carries `solutions_nfa` set to
the intersection automaton of the successful iteration. Note that this automaton represents the
solutions of `phi AND Gamma(M)`, which is a subset of the solutions of `phi AND chi`: the strategy
does not produce an automaton for the whole formula, and any caller that reads `solutions_nfa` as
"all solutions" would be reading something else. The `convert` subcommand of `run-amaya.py` and the
`--vis-only` paths are the callers to check before this field is populated; this design specifies
leaving `solutions_nfa=None` and documenting it, rather than returning an automaton whose language
is a proper subset of what the field's name states.

### 6.5b Refuting an assertion by its variable bounds

Before the theory call, the asserted literals are scanned once for a pair of unit bounds on one
variable that cannot both hold (`find_bounds_refutation`). For each variable the strongest lower and
upper bound seen so far is tracked *together with the literal that imposed it*; the first time a
variable's lower bound exceeds its upper bound, those two literals are reported.

| | |
|---|---|
| Reads | `Relation.is_hard_bound()` (one variable, `<=`) and `Relation.specifies_a_single_value_for_var()` (one variable, `=`), via `amaya/relations_structures.py:get_hard_bound_semantics` |
| Ignores | `Congruence` (constrains a residue, not a range), relations over two or more variables, and every non-`Relation` literal |
| Also reports | A unit equality `c*x = r` with `r` not divisible by `c`, as a single-literal core |
| Cost | One dictionary update per unit-bound literal; no automaton |
| Completeness | None. An assertion it accepts may still be unsatisfiable, and the caller proceeds to the theory call |

The reported core is unsatisfiable *on its own* - independently of `phi` and of every other asserted
literal - which is what §6.6 uses. `Value_Interval.apply_assertion` performs the same intersection but
keeps no provenance, and the provenance is the point: it turns "this assertion is unsatisfiable" into
"these two literals are unsatisfiable".

The check runs on the **unminimized** literal set, and only there. Minimization can only remove
literals, and removing a bound cannot create a clash, so a set the check accepts has no clashing pair
in any subset either - re-running it after minimization could find nothing. Checking first also skips
the minimization and the theory call outright on a hit.

Configured by `use_bounds_refutation` (default on); `--dpllt-no-bounds-refutation` turns it off, which
exists to measure what it buys.

### 6.6 Blocking

When §6.5b refuted the assertion, the clause is built over the **core** rather than over the asserted
set: `OR_{l in core} NOT alpha(l)`. This is sound for a stronger reason than the general case - every
literal set containing the core is unsatisfiable by itself, so no theory call is needed to justify
removing it, and Claim C's argument applies with `Gamma(core)` in place of the refuted assertion. It
removes strictly more than blocking the whole implicant would, since the core is a subset of it. The
core is never empty, so the empty-clause case below is unreachable on this path.

Termination is unaffected: the core is a subset of the asserted set, so the current model still
falsifies the clause and is still excluded, and Claim T's `2**|L|` bound stands. What does change is
that the loop no longer enumerates only minimal implicants - a core clause removes literal sets that
were never minimal implicants of the abstraction - so the minimal-implicant count of §12 becomes an
upper bound on the iteration count rather than an exact prediction of it.

Otherwise the clause is `OR_{l in asserted} NOT alpha(l)`, over the solver variable ids obtained from the
pysat variable pool (`pysat.formula.Formula.export_vpool(active=True)`, as in
`amaya/sat_toplevel.py:Bool_Skeleton.resolve_solver_var_ids`). It excludes exactly the Boolean models
whose asserted set contains the refuted one; Claim C shows none of them is satisfiable.

An empty `asserted` set means `S` is satisfied by the all-false assignment, which happens when `chi`
reduces to a constant `True`. The clause would be empty; the loop instead stops and reports the
verdict of `phi` alone. Some pysat backends reject an empty clause, which is the same reason
`amaya/sat_toplevel.py:solve_with_toplevel_sat` handles the case directly.

Not proposed: extracting an unsatisfiable core from the automata backend to shrink the clause
further. The backend returns an empty automaton, not a core, and deriving one would require
re-running the intersection over subsets. §14 records this.

---

## 7. Interaction with the optimization pipeline

### 7.1 The requirement

`amaya.parse.optimize_formula_structure` runs the pass scheduler
(`amaya/preprocessing/pipeline.py:Optimization_Pipeline`) over a formula. In the ordinary evaluation
path it is applied once, to the whole formula. This design applies it per iteration, to the
assertion alone, which is a different contract:

> A pass applied to the assertion must preserve the assertion's solution set over the variables it
> shares with `phi` — that is, `exists X. A` and `exists X. pass(A)` must denote the same relation
> over the formula parameters, not merely have the same satisfiability.

Satisfiability-preserving rewriting is not sufficient here, because the result is intersected with
`nfa_for_phi` afterwards. A concrete violation exists in the current registry:
`amaya/preprocessing/theory_reasoning.py:_simplify_formula_using_model_properties`, in its `Var`
case, asserts a value for a Bool variable it has not seen and simplifies the rest of the formula
under that assumption. Applied to the whole formula that is satisfiability-preserving; applied to
the assertion it can fix a Bool parameter that `phi` constrains the other way, which would report
UNSAT for a satisfiable formula. `amaya/sat_toplevel.py:substitute_bool_vars` documents the same
distinction from the other side.

### 7.2 The specified handling

A configuration field `dpllt_assertion_optimizer` with three values:

| Value | Behaviour | Status |
|---|---|---|
| `none` | The assertion is handed to the evaluator unoptimized | Correct by construction |
| `restricted` (default) | The pipeline runs with a registry filtered to an allowlist of passes classified as solution-set-preserving | Allowlist **not yet determined**; see below |
| `full` | The pipeline runs with the registry `build_registry(solver_config)` returns | **Known to be unsound** for at least the pass named above; provided for measurement only and gated behind an explicit flag |

The allowlist is a per-pass classification that this document does not perform. Each of the passes
registered in `amaya/preprocessing/pipeline.py:_registry_definition` needs one of three verdicts:
preserves the solution set over free variables; preserves it only for existentially quantified
variables (therefore admissible only for variables in the assertion's own prefix); preserves
satisfiability only (therefore excluded). Until that classification exists, `restricted` is
specified to contain no passes, making it equal to `none` — an implementation that ships a
non-empty allowlist without the classification would be shipping the `full` risk under a different
name.

An alternative that avoids the classification entirely: run the pipeline on
`phi AND Gamma(M)` — the whole per-iteration formula — instead of on the assertion. This restores
the pipeline's original contract. Its costs are that `phi` is re-optimized on every iteration, and
that `nfa_for_phi` can no longer be built once, because the pipeline may rewrite `phi` differently
per iteration. This is recorded in §14 as the fallback if the classification turns out to be mostly
negative.

### 7.3 Pipeline cost per iteration

`Optimization_Pipeline.run` computes a structural id for the formula, runs passes to a fixpoint and
applies a default application budget derived from the formula size
(`amaya/preprocessing/pipeline.py:_default_max_pass_applications`). Running it once per iteration
adds that cost per iteration. A per-run cap on the total number of pipeline applications across the
loop is proposed as `dpllt_max_optimizer_invocations`, after which the mode drops to `none`. No
value is proposed; the quantity that would set it is not measured.

---

## 8. Automaton caching

Three caches are specified, in decreasing order of expected reuse and increasing order of
implementation cost. All three are optional; the loop is correct with all of them disabled.

### 8.1 C1 — the automaton for `phi`

One entry, built before the loop (§6.1), used as an intersection operand on every iteration.

### 8.2 C2 — the conjunction prefix cache

The assertion is (after §6.4 and §7) a conjunction, possibly under one existential prefix.
Consecutive iterations differ in a few literals, so their conjunctions share sub-conjunctions.

```
Assertion_Automaton_Builder:
    intersection_prefix_cache: OrderedDict[Tuple[int, ...], NFA]      # LRU, bounded

    build(conjuncts, bound_vars, ctx):
        keys = sorted(structural id of c for c in conjuncts)          # canonical order
        longest cached prefix p of keys -> nfa (a clone of the cached automaton)
        for each remaining key k in keys:
            nfa = nfa.intersection(automaton for the conjunct of k)
            store clone of nfa under keys[:len(p)+1]
        project bound_vars away from nfa (pad closure after the last one)
        return nfa
```

Points of specification:

1. **Keys.** `amaya/preprocessing/structural_id.py:compute_structural_id` with a table that lives
   for the whole run: id equality is then equivalent to structural equality across every formula
   seen in the run. The table must not be re-created per iteration
   (`compute_structural_id`'s docstring states why).
2. **Canonical order.** Sorting by structural id makes the prefix set depend only on the conjunct
   set, not on the order the SAT solver produced. It also fixes the order in which intersections are
   performed, which the ordinary evaluator does not do — `amaya/parse.py:reorder_conjunction_to_derive_conflict_more_quickly`
   reorders for a different objective. The two objectives conflict; this design chooses the
   cache-friendly order and records the conflict in §13.
3. **The projection is never cached.** Only the unprojected conjunction automata enter the prefix
   cache. Projecting a cached automaton would violate §8.3, and the projection depends on
   `bound_vars`, which differs between assertions that share a prefix.
4. **The intersection with `phi` is not part of the prefix cache** either, so that a single stored
   prefix serves iterations with different assertions.

### 8.3 C3 — the De Bruijn subformula cache

`amaya/cse_cache.py` already memoizes automata for alpha-equivalent subformulae, keyed by
`amaya.debruijn.encode_formula`, and is enabled by wrapping the loop in
`amaya.cse_cache.cse_enabled()`. It applies to whatever the ordinary evaluator constructs inside
each `run_evaluation_procedure` call, and it is content-keyed, so it survives the rewriting the
optimizer performs (unlike C2's keys, which are computed after optimization for exactly this
reason). Its documented limitation is that it is a no-op on any backend other than MTBDD
(`amaya/cse_cache.py` module docstring), because `NFA` has no track renaming.

`ctx.enc_table` must be cleared at the start of every iteration: it is keyed by `id(node)` and the
assertion trees are allocated and discarded per iteration, so a stale entry could be matched by a
new node at a recycled address. `amaya/sat_toplevel.py:_solve_residual_with_automata` performs
exactly this clearing and states the same reason.

### 8.4 The in-place mutation rule

**A cached automaton is never passed to an operation that modifies its operand.** The operations
that do modify their operand are:

| Operation | Source | Effect |
|---|---|---|
| `NFA.do_projection` | `amaya/automatons.py:NFA.do_projection` | Assigns `self.transition_fn` to the result and calls `project_bit_away` on it, so the operand's transition function is modified |
| `MTBDD_NFA.do_projection` | `amaya/mtbdd_automatons.py:MTBDD_NFA.do_projection` | Modifies `self` and returns `self` |
| `NFA.perform_pad_closure`, `MTBDD_NFA.perform_pad_closure` | `amaya/automatons.py`, `amaya/mtbdd_automatons.py` | In place |
| `NFA.remove_nonfinishing_states` | `amaya/automatons.py:NFA.remove_nonfinishing_states` | In place |

`NFA.intersection`, `MTBDD_NFA.intersection` and `NFA.union` allocate a new automaton and leave
their operands unchanged.

The rule is enforced by cloning on every cache read and on every cache write. For MTBDD the clone is
`renamed_copy({})`, which `amaya/cse_cache.py:_renamed_copy` installs on `MTBDD_NFA` at import time
and which `amaya/cse_cache.py:run_evaluation_procedure_cse` already uses for the same purpose. For
the native backend no clone method exists; C2 is therefore specified as MTBDD-only, matching C3's
existing restriction, and the strategy logs a warning on other backends (as
`amaya/sat_toplevel.py:evaluate_prepared_formula_with_toplevel_sat` does).

### 8.5 What is not cached

An assertion set never recurs exactly: §6.6 blocks each asserted set, so a later iteration's set is
never equal to and never a superset of an earlier one. A cache keyed on the whole asserted set would
therefore never hit, and none is specified. C2 hits on shared *prefixes*, which do recur.

---

## 9. Module layout

New module `amaya/dpllt_automata.py`. Symbols, as implemented:

| Symbol | Role |
|---|---|
| `is_literal_node(node) -> bool` | §4.1 |
| `is_chi_eligible_subformula(node) -> bool` | §4.1 |
| `does_subformula_contain_disjunction(node) -> bool` | §4.2, the second applicability condition |
| `normalize_formula_for_splitting(root) -> ASTp_Node` | §4.1/§4.2 preconditions, applied unconditionally |
| `split_formula_into_phi_and_chi(root) -> Formula_Split` | §4.2 |
| `Formula_Split` | Dataclass: `phi_conjuncts`, `chi_conjuncts` |
| `Fresh_Variable_Allocator` | §5.1; allocates `Var` ids and records them in the var table |
| `freshen_bound_variables_in_subformula(node, var_table) -> ASTp_Node` | §5.1 |
| `collect_bound_vars_of_subformula(node) -> FrozenSet[Var]` | §6.4, the prefix candidates |
| `compute_literal_abstraction_key(literal) -> Hashable` | §5.2 |
| `Literal_Abstraction_Manager` | §5.2; `atom_id_by_literal_key`, `literal_by_atom_id` |
| `Monotone_Skeleton_Node`, `Monotone_Skeleton_Node_Type` | §5.3; a representation that cannot express a negation |
| `Monotone_Literal_Abstraction` | Dataclass: `sat_formula`, `skeleton`, `manager`, `pysat_atom_by_atom_id`, `solver_var_id_by_atom_id`; methods `resolve_solver_var_ids`, `collect_asserted_atom_ids_from_sat_model`, `make_blocking_clause` |
| `abstract_chi_into_monotone_sat_formula(chi_conjuncts) -> Monotone_Literal_Abstraction` | §5.3 |
| `evaluate_monotone_skeleton(skeleton, asserted_atom_ids) -> bool` | §6.3 |
| `minimize_asserted_atom_ids(abstraction, asserted_atom_ids) -> Set[int]` | §6.3 |
| `build_assertion_formula_for_atom_ids(abstraction, asserted_atom_ids, chi_bound_vars, project_bound_vars) -> ASTp_Node` | §6.4 |
| `optimize_assertion_formula(assertion, ctx, mode) -> ASTp_Node` | §7.2 |
| `ASSERTION_OPTIMIZER_SOLUTION_SET_PRESERVING_PASSES` | §7.2; empty until the pass classification exists |
| `clone_automaton(nfa) -> Optional[NFA]` | §8.4 |
| `intersect_automata(first, second, ctx) -> NFA` | §8.4; see the note below |
| `Assertion_Automaton_Builder` | §8.2; holds `intersection_prefix_cache`, `structural_id_table`, hit/miss/eviction counters |
| `Dpllt_Run_Statistics` | §12 |
| `solve_with_dpllt_over_automata(root, ctx, config) -> Evaluation_Result` | §6.2 |
| `evaluate_prepared_formula_with_dpllt_automata(astp, ctx, config) -> Evaluation_Result` | Strategy callback; wraps the loop in `cse_enabled()` |
| `perform_whole_evaluation_on_source_text_with_dpllt_automata(source_text, emit_introspect)` | Convenience wrapper, mirroring the one in `amaya/sat_toplevel.py` |

The asserted literals are carried as abstraction ids rather than as nodes; the node is recovered
through `Literal_Abstraction_Manager.literal_by_atom_id`. The ids are what the blocking clause and
the skeleton evaluation are written in terms of, so passing them is what the three steps between the
SAT model and the assertion actually need.

`intersect_automata` is not in the design as originally written. It is required because
`amaya.automatons.NFA.intersection` asserts that its result uses at least one variable, and this
strategy produces two trackless operands whenever `phi` is empty (a trivially accepting automaton)
and an assertion had every variable projected away. An automaton over no tracks accepts either every
word or none, so the intersection with it is either the identity on the other operand or the empty
language, and no product construction is needed.

No existing module is edited except `amaya/config.py` and `run-amaya.py` (§10). `amaya/parse.py` is
not edited: the strategy is injected through the existing `evaluate_prepared_formula` parameter of
`perform_whole_evaluation_on_source_text`, and the recursive-evaluation hook is the existing
module-attribute rebinding performed by `cse_enabled`.

---

## 10. Configuration and command line

New dataclass in `amaya/config.py`:

```python
@dataclass
class DpllTAutomataConfig:
    enabled: bool = False
    assertion_optimizer: str = 'restricted'      # 'none' | 'restricted' | 'full'
    minimize_implicants: bool = True
    use_bounds_refutation: bool = True
    project_bound_vars: bool = True
    prefix_cache_max_entries: int = 4096
    max_optimizer_invocations: Optional[int] = None
    report: bool = False
    show_positive_existential_part: bool = False
    count_abstraction_models: bool = False
    abstraction_model_enumeration_limit: int = 1000000
```

Command-line flags on `run-amaya.py`, following the placement of `--use-toplevel-sat`: these are not
`-O` optimizations and must stay out of the `opt_to_config_field` table, since `-O all` iterates
that table and would otherwise enable the strategy on every run (the comment above
`--opt-fixpoint` in `run-amaya.py` records this constraint).

| Flag | Effect |
|---|---|
| `--use-dpllt-automata` | Selects the strategy |
| `--dpllt-assertion-optimizer {none,restricted,full}` | §7.2; `full` is marked unsound in the help text |
| `--dpllt-no-implicant-minimization` | §6.3 off |
| `--dpllt-no-bounds-refutation` | §6.5b off; every asserted set goes to the automata engine |
| `--dpllt-no-bound-var-projection` | §6.4 off |
| `--dpllt-prefix-cache-entries N` | §8.2 bound |
| `--dpllt-report` | Log the counters of §12 |
| `--dpllt-show-existential-part` | Print `chi` and exit without evaluating; implies `--use-dpllt-automata`. See below |
| `--dpllt-count-abstraction-models` | Print the model and minimal-implicant counts of `chi`'s abstraction and exit; implies `--use-dpllt-automata`. See below |
| `--dpllt-abstraction-model-limit N` | Cap either enumeration of the previous option (default 1000000) |

Mutual exclusions, checked at argument-parsing time with an error message, following the existing
check between `--use-toplevel-sat` and `--shard`:

* `--use-dpllt-automata` with `--use-toplevel-sat`: two strategies for the same callback.
* `--use-dpllt-automata` with `--shard`: `--shard` decomposes the same top-level conjunction.

`python-sat` is imported lazily inside `get_evaluation_strategy`, as `amaya.sat_toplevel` already is.

`--dpllt-show-existential-part` prints the positive-existential part the split found and terminates
the process (`display_positive_existential_part_and_exit`), mirroring
`preprocessing.show_preprocessed_formula` and `preprocessing.display_var_table`
(`amaya/parse.py:perform_whole_evaluation_on_source_text`). Two properties of where it sits:

1. It prints the split's own output, before `freshen_bound_variables_in_subformula` (§5.1) renames
   the binders apart, so the variable ids shown are those of the input formula and not those the
   per-iteration logs carry.
2. It runs before both fall-throughs of §4.2, so a formula the strategy would decline prints an empty
   part rather than being evaluated. That is what makes the option answer "why did this input not
   engage the loop".

`--dpllt-count-abstraction-models` (`display_abstraction_model_counts_and_exit`) sits in the same
place and reports two counts over the abstraction of §5.3:

| Count | Meaning | Computed by |
|---|---|---|
| models | Truth assignments to the abstracted literals satisfying the abstraction. Bounded by `2**(abstracted literals)` | `count_models_of_abstraction`, blocking each model exactly so the auxiliary variables clausification introduces are projected out |
| minimal implicants | Assertions the loop constructs; the number of theory calls it makes when every one of them is refuted, which is its worst case on this formula | `count_minimal_implicants_of_abstraction`, which is §6.2's enumeration with the theory calls left out |

Each count is printed as soon as it is known, and the implicants are counted first. On any formula
large enough to be worth asking about, the limit binds and the enumeration runs for the whole budget;
computing both before printing anything would spend that budget on the model count - the less useful
of the two - and report neither.

The minimal implicant count is exact rather than an over-count: every iteration yields an implicant
not yet seen, because a model containing an already-blocked one would have been excluded by its
blocking clause, and the enumeration stops only once every minimal implicant has been blocked. It is
the quantity §16 item 2 leaves unmeasured, obtainable without constructing a single automaton - so it
is available on formulae the loop itself cannot finish. Both enumerations stop at
`abstraction_model_enumeration_limit` and report a lower bound.

Unlike `--dpllt-show-existential-part`, this option renames the binders apart before abstracting
(§5.1): the abstraction merges equal literals, so counting over an unfreshened `chi` would count the
models of a different abstraction than the loop enumerates.

---

## 11. Correctness summary

| Property | Argument | Depends on |
|---|---|---|
| A reported SAT verdict is correct | The model is read off an automaton for `phi AND Gamma(M)`; Claim S gives `Gamma(M)` entails `chi`, so it is a model of `phi AND chi` | §5.3, and the evaluator being correct on the assertion |
| A reported UNSAT verdict is correct | Claim C: every model of `phi AND chi` induces a Boolean model of `S` that the enumeration reaches | §5.1 (binders distinct), §4.1 (positive polarity), §6.6 (clause form) |
| The loop terminates | Claim T: one clause per iteration over `|L|` variables | §6.6 |
| The pipeline does not change the answer | Only under §7.2's requirement | **Open**: the pass classification of §7.2 does not exist |
| Caches do not change the answer | C1/C2/C3 store automata keyed by content and are cloned on every read and write | §8.4, and `renamed_copy` availability (MTBDD only) |

---

## 12. Instrumentation

The counters to record per run, reported under `--dpllt-report`:

| Counter | Purpose |
|---|---|
| `chi_conjunct_count`, `phi_conjunct_count`, `abstracted_literal_count` | Describe the split that was found |
| `iteration_count` | Theory calls performed |
| `asserted_literals_before_minimization`, `asserted_literals_after_minimization` (totals) | The effect of §6.3 |
| `theory_calls`, `bounds_refutations`, `bounds_refutation_core_literals` | The effect of §6.5b: how many iterations avoided a theory call, and how short the cores were |
| `prefix_cache_hits`, `prefix_cache_misses`, `prefix_cache_evictions`, `longest_prefix_hit_length` | The effect of §8.2 |
| `optimizer_invocations`, `optimizer_total_time_ns` | The cost of §7 |
| `phi_automaton_states`, `max_assertion_automaton_states`, `max_intersection_states` | Automaton sizes |

The existing `EvaluationContext.stats` (`amaya/solver_core.py:EvaluationContext.stats_operation_ends`)
already records every automaton operation with its operands and runtime; these counters are the ones
that layer above it and are not derivable from it.

Alongside the counters, every formula the strategy hands to the automata engine is logged through
`amaya.relations_structures.format_formula`, in the same form the optimization pipeline's `trace`
uses:

| Level | Content | Frequency |
|---|---|---|
| INFO | The general part, or a note that it is empty | Once per run |
| INFO | The assertion as handed to the evaluator, prefixed by its iteration number | Once per iteration |
| DEBUG | The assertion before optimization, only when the optimizer changed it | Once per iteration at most |
| DEBUG | Each conjunct of the positive-existential part, after its binders have been renamed apart | Once per run |

The positive-existential part is never evaluated as it stands - the per-iteration assertions are what
reaches the evaluator - but it is what those assertions are drawn from, hence the DEBUG entry.
`--verbose` makes the INFO entries visible, `--debug` the DEBUG ones.

---

## 13. Risks

| # | Risk | Mitigation in this design |
|---|---|---|
| R1 | The assertion-level optimizer is applied with a pass that is only satisfiability-preserving, producing wrong verdicts | §7.2 defaults to an empty allowlist; `full` is a separate, labelled flag |
| R2 | Two binders sharing a `Var` id are hoisted into one prefix, producing wrong UNSAT verdicts | §5.1 renames apart unconditionally |
| R3 | A cached automaton is projected in place and corrupts the cache | §8.4 states the rule and the clone-on-read/write discipline; the operations that violate it are enumerated |
| R4 | The number of minimal implicants of `S` is exponential in `|L|`, and the loop enumerates them one by one | Not mitigated. The strategy is opt-in and the fallback in §4.2 excludes the `OR`-free case where it is certainly not worthwhile. No iteration budget is specified |
| R5 | The canonical conjunct order of §8.2 conflicts with `reorder_conjunction_to_derive_conflict_more_quickly`, which orders conjuncts to reach an empty automaton sooner | Not resolved. The two are alternative orderings of the same intersections; which produces less work is not measured |
| R6 | `solutions_nfa` in the returned `Evaluation_Result` would describe a subset of the formula's solutions | §6.5 specifies leaving it `None` |
| R7 | The alphabet is rebuilt after freshening (§5.1), which changes track positions for every automaton built afterwards | The rebuild happens before any automaton is constructed, including `nfa_for_phi` |
| R8 | On the native backend, C2 and C3 are unavailable, so every iteration rebuilds the assertion from scratch | Logged as a warning; the strategy still terminates with correct verdicts |

---

## 14. Alternatives considered and not specified

| Alternative | Reason it is not specified |
|---|---|
| Assert the full literal assignment (both polarities), as in textbook DPLL(T) | The assertion then contains one literal per abstracted atom on every iteration, instead of one per literal of a minimal implicant. §5.3's monotonicity argument is what removes the negative half |
| Abstract the whole formula uniformly, treating each non-eligible subformula (for example `NOT exists ...`) as an opaque literal whose automaton is built by the ordinary evaluator | A generalization of this design in which `phi` disappears as a special case. It changes the split of §4 and the cache structure of §8; it is compatible with §5.3, since such a subformula enters as a literal in positive polarity. Recorded as the natural extension once the `phi AND chi` form is measured |
| Expand `EQUIV` into `(a AND b) OR (NOT a AND NOT b)` to make more conjuncts eligible | Doubles the subformula and introduces negations over non-literals, which then have to be pushed down or abstracted; not justified without a measurement of how often `EQUIV` blocks the split |
| Bias the SAT solver toward small models with `set_phases` instead of §6.3 | Gives no minimality guarantee, so the blocking clause is not strengthened |
| Compute an unsatisfiable core from the automata backend to shrink the blocking clause | The backend returns an empty automaton, not a core; deriving one requires re-running intersections over subsets. Superseded for one class of conflict by §6.5b, which obtains a core without the backend. Three further designs, including one that needs no additional intersection at all, are assessed in `docs/PIPELINE_UNSAT_CORES.md` |
| Learn clauses before the enumeration starts, by testing each disjunct branch and each cross-disjunction branch pair against a once-built automaton for the general part and the mandatory core | Not rejected - proposed in `docs/EAGER_THEORY_LEARNING.md`, which identifies the number of disjunctions a clause spans, rather than its literal width, as what governs how much it removes |
| Run the pipeline on `phi AND Gamma(M)` per iteration | Restores the pipeline's whole-formula contract but re-optimizes `phi` per iteration and prevents caching its automaton. Kept as the fallback for §7.2 |
| Drop the existential prefix and leave the former bound variables free | Correct (they do not occur in `phi`), but the assertion no longer matches the `AST_Quantifier(AND(...))` shapes the specialized constructions of §6.4 require. Available as `--dpllt-no-bound-var-projection` |

---

## 15. Test plan

Unit tests, in `tests/test_dpllt_automata.py`:

| # | Subject | Assertion |
|---|---|---|
| T1 | `is_chi_eligible_subformula` | Accepts literals, `AND`/`OR`/`exists` over eligible nodes; rejects `EQUIV`, `NOT` over a connective, `NOT exists` |
| T2 | `split_formula_into_phi_and_chi` | On a flattened top-level `AND`, every conjunct lands in exactly one part; on a non-`AND` root, one part is empty |
| T3 | `freshen_bound_variables_in_subformula` | Bound var ids after the call are pairwise distinct across binders and disjoint from the pre-existing var table; the var table gains one entry per renamed variable with `is_formula_param=False` |
| T4 | `compute_literal_abstraction_key` | Equal for two structurally equal `Relation`s; different for a literal and its negation; different for two `Congruence`s differing only in modulus |
| T5 | `abstract_chi_into_monotone_sat_formula` | The skeleton contains no negation node |
| T6 | `minimize_asserted_literal_set` | The result satisfies the skeleton and no proper subset of it does |
| T7 | `build_assertion_formula_for_literal_set` | The prefix contains exactly the bound variables occurring in the asserted literals; `referenced_vars` is accurate on every produced node |
| T8 | `Assertion_Automaton_Builder` | Two assertions sharing a prefix produce one stored entry per prefix length; the automaton returned for the second is language-equivalent to one built without the cache |
| T9 | Cache mutation | After building an assertion that projects bound variables away, the automaton stored in the prefix cache accepts the same language it did before the projection (guards R3) |

End-to-end tests, comparing the verdict of `--use-dpllt-automata` against
`evaluate_prepared_formula_with_automata` on the same input:

| # | Input shape | Purpose |
|---|---|---|
| T10 | `phi` empty, `chi` a single conjunction of literals | One iteration, no `OR` — exercises the §4.2 fallback |
| T11 | `chi` a disjunction of two contradictory literals conjoined with a `phi` that decides it | Exercises blocking and a second iteration |
| T12 | `chi` with nested `exists` under `OR` | Exercises prefix hoisting (§6.4) and R2 |
| T13 | A formula where two binders in `chi` share a `Var` id after miniscoping | Exercises §5.1; expected to fail without freshening |
| T14 | A formula with a free Bool parameter occurring in both `phi` and `chi` | Exercises R1: the verdict must not change between `--dpllt-assertion-optimizer none` and `restricted` |
| T15 | A randomized differential test over small generated LIA formulae, comparing verdicts against the ordinary evaluator | Coverage of the enumeration as a whole |

Benchmark inputs exist under `benchmarks/formulae`; `scripts/check_correctness.py` compares
verdicts against a reference and is the harness a differential run would use.

---

## 16. Quantities this document does not establish

None of the following is measured, estimated or asserted anywhere above:

1. The fraction of `benchmarks/formulae` inputs that admit a non-empty `chi` under §4.1, and the
   size of `chi` relative to the whole formula when they do.
2. The number of iterations the loop performs on any input, and its relation to `|L|`.
3. Whether §6.3's minimization reduces total runtime, and the effect of the removal order.
4. The hit rate and the average hit length of the prefix cache (§8.2), and whether it exceeds the
   reuse the De Bruijn cache (§8.3) already provides on the same assertions.
5. Automaton sizes for `phi`, for the assertions and for their intersections, relative to the
   automaton the ordinary evaluator builds for the whole formula.
6. The per-iteration cost of the optimization pipeline (§7.3) relative to the theory call it
   precedes.
7. Which of `project_bound_vars` on or off produces smaller automata (§6.4).
8. Whether the canonical conjunct order of §8.2 or the conflict-first order of
   `reorder_conjunction_to_derive_conflict_more_quickly` performs fewer intersection steps (R5).
9. The classification of each registered pass as solution-set-preserving or not (§7.2) — the one
   open item that blocks a correct default other than `none`.
10. Any comparison against `--use-toplevel-sat` or against other solvers.
