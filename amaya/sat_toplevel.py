"""
(EXPERIMENTAL) Top-level SAT solving over the formula's free Bool variables - see `SAT_TOP_LEVEL.md`.

A CEGAR-style loop that is SAT-solver-driven at the top and automata-driven underneath:

1. Abstract the formula's Boolean skeleton, replacing every maximal non-Boolean subformula
   (`Relation`, `Congruence`, quantified subformula) by an opaque, unconstrained Boolean atom.
2. Ask a SAT solver for a model of that abstraction and project it onto the *free* Bool vars.
3. Substitute that assignment into the formula, constant-fold, and hand the residual LIA formula to
   the ordinary automata-based evaluator.
4. If the residual is unsatisfiable, add a clause blocking that projection and go back to 2. If the
   SAT solver runs out of models, the whole formula is unsatisfiable.

Correctness rests on three facts, each maintained by the code below:

* *Relaxation.* Every model of the original formula induces a model of the abstraction (evaluate
  each abstracted subformula and give its atom that truth value). Hence an assignment the SAT solver
  never enumerates cannot satisfy the formula either, and "the solver ran out of models" is a sound
  UNSAT. This holds only as long as distinct subformulae never share an atom - see
  `amaya.sat.compute_atom_abstraction_key`.
* *Per-assignment soundness.* `substitute_bool_vars` is equivalence-preserving (not merely
  satisfiability-preserving), so the residual has exactly the models of the formula restricted to the
  assignment. A satisfiable residual therefore yields a model of the original formula, and an
  unsatisfiable one rules out exactly the assignment that the blocking clause removes.
* *Termination.* Every iteration adds a clause over the `k` free-Bool-var literals which removes at
  least the current projection, so the loop performs at most `2**k` theory calls. The clause usually
  removes a great deal more than that one projection - see `Polarity` and `solve_with_toplevel_sat`'s
  `use_generalized_blocking`.

This module is entirely off the default evaluation path: nothing in `parse.py` reaches it unless the
user asks for it via `run-amaya.py --use-toplevel-sat`.
"""
from __future__ import annotations

import contextlib
import itertools
from enum import Enum
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Generator, Iterable, List, Optional, Set, Tuple

import pysat.formula
import pysat.solvers

from amaya import logger
from amaya import parse
from amaya.config import BackendType, solver_config
from amaya.cse_cache import cse_enabled
from amaya.parse import Evaluation_Result, convert_binary_model_into_decadic
from amaya.preprocessing.eval import VarInfo
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Node,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
)
from amaya.sat import (
    Theory_Abstraction_Manager,
    make_atom_name_for_bool_var,
    make_atom_name_for_theory_atom,
)
from amaya.solver_core import EvaluationContext


# ---------------------------------------------------------------------------------------------
# pysat global state
# ---------------------------------------------------------------------------------------------

_sat_context_counter = itertools.count()


@contextlib.contextmanager
def isolated_sat_formula_context() -> Generator[str, None, None]:
    """
    Run the block in a private `pysat.formula.Formula` context, discarding it afterwards.

    `pysat` interns atoms and allocates their solver variable ids in *process-global* tables keyed by
    the currently active context. Without isolation, two skeletons built in one process (two runs in a
    test session, say) would share atoms, so `var:3` from an earlier formula would silently be the same
    solver variable as `var:3` from a later one. Yields the name of the context that is active inside
    the block.
    """
    context_name = f'amaya-toplevel-sat-{next(_sat_context_counter)}'
    previous_context = pysat.formula.Formula._context

    pysat.formula.Formula.set_context(context_name)
    try:
        yield context_name
    finally:
        pysat.formula.Formula.set_context(previous_context)
        pysat.formula.Formula.cleanup(context_name)


# ---------------------------------------------------------------------------------------------
# The Boolean abstraction
# ---------------------------------------------------------------------------------------------

def is_assignable_free_bool_var(var: Var, var_table: Dict[Var, VarInfo]) -> bool:
    """ Whether `var` is a Bool-typed parameter of the whole formula, i.e. one the SAT layer may assign. """
    var_info = var_table.get(var)
    if var_info is None:
        return False
    return var_info.type == VariableType.BOOL and var_info.is_formula_param


def abstract_to_sat_formula(node: ASTp_Node,
                            var_table: Dict[Var, VarInfo],
                            abstraction_manager: Theory_Abstraction_Manager,
                            free_bool_var_atoms: Dict[Var, pysat.formula.Atom]) -> pysat.formula.Formula:
    """
    Build the Boolean abstraction of `node`: Boolean connectives are kept, every maximal non-Boolean
    subformula becomes an opaque atom the SAT solver may set either way.

    Atoms standing for free Bool `Var`s are recorded into `free_bool_var_atoms` - those, and only
    those, are the variables the SAT layer assigns and later substitutes into the formula. Bound Bool
    vars still become atoms (the abstraction must model them) but are never assigned.

    This is a superset of `amaya.sat.convert_to_sat_formula`, which handles neither `Congruence`,
    `BoolLiteral`, nor `AST_Quantifier` - i.e. none of the formulae this feature exists for. That
    function is left alone because the (unrelated) BDD experiment in `amaya/sat.py` builds on it.
    """
    match node:
        case AST_Connective():
            subformulae = [
                abstract_to_sat_formula(child, var_table, abstraction_manager, free_bool_var_atoms)
                for child in node.children
            ]
            match node.type:
                case Connective_Type.AND:
                    return pysat.formula.And(*subformulae)
                case Connective_Type.OR:
                    return pysat.formula.Or(*subformulae)
                case Connective_Type.EQUIV:
                    return pysat.formula.Equals(*subformulae)
            raise ValueError(f'Unhandled connective type when abstracting a formula: {node.type}')

        case AST_Negation():
            subformula = abstract_to_sat_formula(node.child, var_table, abstraction_manager, free_bool_var_atoms)
            return pysat.formula.Neg(subformula)

        case BoolLiteral():
            return pysat.formula.PYSAT_TRUE if node.value else pysat.formula.PYSAT_FALSE

        case Var():
            atom = pysat.formula.Atom(make_atom_name_for_bool_var(node))
            if is_assignable_free_bool_var(node, var_table):
                free_bool_var_atoms[node] = atom
            return atom

        case Relation() | Congruence() | AST_Quantifier():
            atom_id = abstraction_manager.get_id_for_atom(node)
            return pysat.formula.Atom(make_atom_name_for_theory_atom(atom_id))

    raise ValueError(f'Unhandled formula node when abstracting a formula into SAT: {type(node)}')


@dataclass
class Bool_Skeleton:
    """ The Boolean abstraction of a formula, together with everything needed to talk to the SAT solver about it. """

    sat_formula: pysat.formula.Formula
    abstraction_manager: Theory_Abstraction_Manager
    free_bool_var_atoms: Dict[Var, pysat.formula.Atom]
    """ Free (unbound) Bool vars occurring in the skeleton - the only vars the SAT layer ever assigns. """

    solver_var_id_of_free_bool_var: Dict[Var, int] = field(default_factory=dict)
    """
    Free Bool var -> the DIMACS variable the SAT solver actually sees.

    These are *not* the abstraction ids handed out by `Theory_Abstraction_Manager` (those are names
    internal to the abstraction); they come from the `pysat` variable pool that clausification uses.
    """

    def resolve_solver_var_ids(self):
        """ Fill in `solver_var_id_of_free_bool_var`. Must run in the context the skeleton was built in. """
        vpool = pysat.formula.Formula.export_vpool(active=True)
        self.solver_var_id_of_free_bool_var = {
            var: vpool.id(atom) for var, atom in self.free_bool_var_atoms.items()
        }

    def decode_free_bool_vars(self, sat_model: Iterable[int]) -> Dict[Var, bool]:
        """
        Project a `pysat` model onto the free Bool vars.

        The solver hands back a *total* assignment over every variable in the clausified abstraction,
        including the opaque theory atoms and the auxiliary variables introduced by clausification.
        Everything but the free Bool vars is dropped: those values are choices the relaxation was free
        to make, not facts about the theory.
        """
        value_of_solver_var = {abs(literal): (literal > 0) for literal in sat_model}
        return {
            var: value_of_solver_var[solver_var_id]
            for var, solver_var_id in self.solver_var_id_of_free_bool_var.items()
            if solver_var_id in value_of_solver_var
        }

    def make_blocking_clause(self,
                             assignment: Dict[Var, bool],
                             restrict_to_vars: Optional[FrozenSet[Var]] = None) -> List[int]:
        """
        The clause forbidding `assignment` - the negation of the conjunction of its literals.

        Blocking the *projection* rather than the solver's full model is what bounds the loop: were the
        opaque theory atoms part of the clause, the solver could hand back the same free Bool var
        assignment once per combination of them and re-solve an identical residual every time.

        `restrict_to_vars` blocks a *generalization* of the assignment instead - every assignment that
        agrees with it on those vars. See `solve_with_toplevel_sat` for why that is sound; passing a set
        that does not satisfy the condition stated there would block satisfiable assignments and turn
        SAT formulae into UNSAT verdicts.
        """
        blocked_vars = assignment.items() if restrict_to_vars is None else [
            (var, value) for var, value in assignment.items() if var in restrict_to_vars
        ]
        return [
            (-1 if value else 1) * self.solver_var_id_of_free_bool_var[var]
            for var, value in blocked_vars
        ]


def extract_bool_skeleton(root: ASTp_Node, ctx: EvaluationContext) -> Bool_Skeleton:
    """ Abstract `root` into a SAT formula. Must be called inside `isolated_sat_formula_context`. """
    abstraction_manager = Theory_Abstraction_Manager()
    free_bool_var_atoms: Dict[Var, pysat.formula.Atom] = {}

    sat_formula = abstract_to_sat_formula(root, ctx.var_table, abstraction_manager, free_bool_var_atoms)

    skeleton = Bool_Skeleton(sat_formula=sat_formula,
                             abstraction_manager=abstraction_manager,
                             free_bool_var_atoms=free_bool_var_atoms)
    skeleton.resolve_solver_var_ids()
    return skeleton


def has_free_bool_vars(ctx: EvaluationContext) -> bool:
    """
    Whether the formula has any Bool-typed parameter at all - the cheap upfront check that lets
    formulae this feature cannot help fall straight through to the ordinary evaluator.

    Reads the var table rather than walking the AST; note a parameter may survive in the var table
    without occurring in the formula any more, in which case the skeleton simply will not contain it
    and it will never be assigned.
    """
    return any(is_assignable_free_bool_var(var, ctx.var_table) for var in ctx.var_table)


# ---------------------------------------------------------------------------------------------
# Substituting a Boolean assignment into the formula
# ---------------------------------------------------------------------------------------------

class Polarity(Enum):
    """
    How the surrounding formula uses a subformula's truth value - the key to generalized blocking.

    The CEGAR loop only ever needs relevance sets in order to justify *keeping a formula unsatisfiable*,
    so a subformula sitting in a monotone position may be allowed to get **stronger** when the blocked-out
    variables move, without the whole formula becoming satisfiable. That is what lets a `True` conjunct be
    forgotten entirely: whatever else it might have become, the surviving conjuncts alone are already
    unsatisfiable.

    * `POSITIVE` - the subformula occurs under an even number of negations; the analysis guarantees that
      the subformula obtained from any assignment agreeing with the blocked one *entails* the one actually
      built.
    * `NEGATIVE` - odd number of negations; the guarantee is the other way round.
    * `NEUTRAL` - the subformula occurs in both polarities at once (under `EQUIV`); the analysis
      guarantees the two are syntactically identical, which is the strongest and cheapest thing to say.
    """
    POSITIVE = 'positive'
    NEGATIVE = 'negative'
    NEUTRAL = 'neutral'

    def flipped(self) -> 'Polarity':
        if self == Polarity.POSITIVE:
            return Polarity.NEGATIVE
        if self == Polarity.NEGATIVE:
            return Polarity.POSITIVE
        return Polarity.NEUTRAL


Substituted_Node = Tuple[ASTp_Node, FrozenSet[Var]]
""" A substituted subtree, paired with the assigned vars the analysis says the loop must keep blocking. """


def _collect_referenced_vars(node: ASTp_Node) -> Tuple[Var, ...]:
    match node:
        case Relation() | Congruence():
            return tuple(node.vars)
        case Var():
            return (node,)
        case BoolLiteral():
            return tuple()
        case _:
            return tuple(node.referenced_vars)


def _make_connective(connective_type: Connective_Type, children: Tuple[ASTp_Node, ...]) -> AST_Connective:
    referenced_vars: Set[Var] = set()
    for child in children:
        referenced_vars.update(_collect_referenced_vars(child))
    return AST_Connective(referenced_vars=tuple(sorted(referenced_vars)), type=connective_type, children=children)


def _union_of_relevant_vars(substituted_children: Iterable[Substituted_Node]) -> FrozenSet[Var]:
    relevant_vars: FrozenSet[Var] = frozenset()
    for _, child_relevant_vars in substituted_children:
        relevant_vars |= child_relevant_vars
    return relevant_vars


def _relax_trivially_satisfied_relevance(substituted_node: Substituted_Node, polarity: Polarity) -> Substituted_Node:
    """
    Drop the relevance set of a subformula whose guarantee holds for free.

    In a positive position the analysis owes "whatever it becomes, it entails what was built"; if what was
    built is `True`, every formula entails it and nothing needs blocking. A negative position owes the
    converse, so `False` is the free case there.
    """
    node, _ = substituted_node
    if polarity == Polarity.POSITIVE and node == BoolLiteral(True):
        return node, frozenset()
    if polarity == Polarity.NEGATIVE and node == BoolLiteral(False):
        return node, frozenset()
    return substituted_node


def _fold_and_or(connective_type: Connective_Type,
                 substituted_children: Tuple[Substituted_Node, ...],
                 polarity: Polarity) -> Substituted_Node:
    """ Constant-fold an AND/OR whose children have already been substituted into. """
    annihilator = BoolLiteral(False) if connective_type == Connective_Type.AND else BoolLiteral(True)
    identity = BoolLiteral(True) if connective_type == Connective_Type.AND else BoolLiteral(False)

    annihilating_relevant_vars = [relevant_vars for child, relevant_vars in substituted_children
                                  if child == annihilator]
    if annihilating_relevant_vars:
        # One annihilating child decides the whole connective, so only the vars that made *it* annihilate
        # need blocking; every other child is discarded whatever it was substituted to. The smallest such
        # set is picked, since a shorter blocking clause rules out more assignments at once.
        return _relax_trivially_satisfied_relevance((annihilator, min(annihilating_relevant_vars, key=len)),
                                                    polarity)

    # A child that folded to the connective's identity is dropped from the result, and in a monotone
    # position the vars that made it fold need not be blocked: were they assigned otherwise, that child
    # would become some other formula, but the surviving children are unchanged, and in a positive
    # position an AND only gets stronger by regaining a conjunct (dually for OR in a negative position).
    # In the opposite polarity that reasoning does not hold and the vars stay in the set.
    identity_children_may_be_forgotten = (
        (connective_type == Connective_Type.AND and polarity == Polarity.POSITIVE)
        or (connective_type == Connective_Type.OR and polarity == Polarity.NEGATIVE)
    )

    relevant_vars = _union_of_relevant_vars(
        substituted_child for substituted_child in substituted_children
        if not (identity_children_may_be_forgotten and substituted_child[0] == identity)
    )

    surviving_children = tuple(child for child, _ in substituted_children if child != identity)

    if not surviving_children:
        return _relax_trivially_satisfied_relevance((identity, relevant_vars), polarity)
    if len(surviving_children) == 1:
        return surviving_children[0], relevant_vars
    return _make_connective(connective_type, surviving_children), relevant_vars


def _fold_equiv(substituted_children: Tuple[Substituted_Node, ...], polarity: Polarity) -> Substituted_Node:
    """
    Constant-fold an EQUIV (an n-ary "all children have the same truth value") over substituted children.

    `AST_Connective`'s existing fold helpers deliberately bail out on EQUIV, so this is done here: a
    `True` child is simply dropped (every remaining child must then be true, i.e. the rest is an AND),
    while a `False` child forces the negation of every other child.

    The "all children share one truth value" reading agrees with `evaluate_bool_equivalence_expr`
    (`parse.py:1170`) on the binary case, which is the only one the evaluator supports at all - the
    n-ary handling here is a superset that simply never comes up.

    An EQUIV uses its children in both polarities, so they are analysed under `Polarity.NEUTRAL` by the
    caller and no relaxation is available inside; only the equivalence as a whole may be relaxed against
    the polarity it sits in.
    """
    relevant_vars_by_literal_value: Dict[bool, List[FrozenSet[Var]]] = {}
    non_literal_children: List[Substituted_Node] = []
    for child, relevant_vars in substituted_children:
        if isinstance(child, BoolLiteral):
            relevant_vars_by_literal_value.setdefault(child.value, []).append(relevant_vars)
        else:
            non_literal_children.append((child, relevant_vars))

    all_relevant_vars = _union_of_relevant_vars(substituted_children)

    if len(relevant_vars_by_literal_value) > 1:  # Both True and False are demanded of the same equivalence class
        # Two conflicting children alone force the contradiction; the rest is irrelevant, so blame the
        # cheapest witness for each polarity.
        witness_relevant_vars = frozenset().union(*(min(candidates, key=len)
                                                    for candidates in relevant_vars_by_literal_value.values()))
        return _relax_trivially_satisfied_relevance((BoolLiteral(False), witness_relevant_vars), polarity)

    if not relevant_vars_by_literal_value:
        if len(non_literal_children) <= 1:
            return _relax_trivially_satisfied_relevance((BoolLiteral(True), all_relevant_vars), polarity)
        folded = _make_connective(Connective_Type.EQUIV, tuple(child for child, _ in non_literal_children))
        return folded, all_relevant_vars

    forced_value = next(iter(relevant_vars_by_literal_value))
    if not non_literal_children:
        return _relax_trivially_satisfied_relevance((BoolLiteral(True), all_relevant_vars), polarity)

    # The literal children are about to disappear (a `True` one is dropped, a `False` one flips the rest),
    # so their own relevance has to be carried through the fold - without it, `EQUIV(x, rel)` under
    # `x=True` would fold to `rel` while claiming `x` did not matter.
    literal_relevant_vars = frozenset().union(*(vars
                                                for candidates in relevant_vars_by_literal_value.values()
                                                for vars in candidates))

    # The residual conjunction inherits the equivalence's own polarity: it *is* what the equivalence
    # became, so an unsatisfiable-preserving relaxation of it is one of the equivalence too.
    if forced_value:
        folded_node, folded_relevant_vars = _fold_and_or(Connective_Type.AND, tuple(non_literal_children), polarity)
    else:
        negated_children = tuple(_fold_negation(child, relevant_vars)
                                 for child, relevant_vars in non_literal_children)
        folded_node, folded_relevant_vars = _fold_and_or(Connective_Type.AND, negated_children, polarity)

    return _relax_trivially_satisfied_relevance((folded_node, folded_relevant_vars | literal_relevant_vars),
                                               polarity)


def _fold_negation(child: ASTp_Node, relevant_vars: FrozenSet[Var]) -> Substituted_Node:
    if isinstance(child, BoolLiteral):
        return BoolLiteral(not child.value), relevant_vars
    return AST_Negation(referenced_vars=tuple(sorted(_collect_referenced_vars(child))), child=child), relevant_vars


def _substitute_bool_vars_tracking_relevance(node: ASTp_Node,
                                             assignment: Dict[Var, bool],
                                             polarity: Polarity = Polarity.POSITIVE) -> Substituted_Node:
    """
    `substitute_bool_vars`, additionally reporting which assigned vars the CEGAR loop still has to block.

    The substituted node is exactly what `substitute_bool_vars` returns - the polarity affects only the
    reported set. Writing `f[a]` for the substitution of assignment `a` into `f`, and `S` for the reported
    set, the analysis maintains, for every assignment `b` that agrees with `a` on `S`:

        polarity POSITIVE:  node[b] entails node[a]
        polarity NEGATIVE:  node[a] entails node[b]
        polarity NEUTRAL:   node[b] and node[a] are the same tree

    Called at the root under `POSITIVE`, that gives the loop what it needs: if `root[a]` has no models,
    neither does `root[b]` for any `b` agreeing with `a` on `S`, so a clause blocking just `S` blocks
    nothing satisfiable. See `solve_with_toplevel_sat`.
    """
    match node:
        case Var():
            substituted_value = assignment.get(node)
            if substituted_value is None:
                return node, frozenset()
            return _relax_trivially_satisfied_relevance((BoolLiteral(substituted_value), frozenset((node,))),
                                                       polarity)

        case Relation() | Congruence() | BoolLiteral():
            return node, frozenset()

        case AST_Negation():
            substituted_child, relevant_vars = _substitute_bool_vars_tracking_relevance(
                node.child, assignment, polarity.flipped())
            return _fold_negation(substituted_child, relevant_vars)

        case AST_Connective():
            if node.type == Connective_Type.EQUIV:
                # An equivalence uses each child in both polarities at once, so nothing below it may be
                # relaxed; only the equivalence as a whole can be, against the polarity it sits in.
                substituted_children = tuple(
                    _substitute_bool_vars_tracking_relevance(child, assignment, Polarity.NEUTRAL)
                    for child in node.children
                )
                return _fold_equiv(substituted_children, polarity)

            substituted_children = tuple(
                _substitute_bool_vars_tracking_relevance(child, assignment, polarity) for child in node.children
            )
            return _fold_and_or(node.type, substituted_children, polarity)

        case AST_Quantifier():
            # Both quantifiers are monotone in their body, so the polarity carries straight through.
            substituted_child, relevant_vars = _substitute_bool_vars_tracking_relevance(
                node.child, assignment, polarity)
            if isinstance(substituted_child, BoolLiteral):
                return substituted_child, relevant_vars  # Quantifying over a constant body is vacuous

            childs_referenced_vars = _collect_referenced_vars(substituted_child)
            surviving_bound_vars = tuple(var for var in node.bound_vars if var in childs_referenced_vars)
            if not surviving_bound_vars:
                return substituted_child, relevant_vars

            quantifier = AST_Quantifier(referenced_vars=tuple(sorted(childs_referenced_vars)),
                                        bound_vars=surviving_bound_vars,
                                        child=substituted_child)
            return quantifier, relevant_vars

    raise ValueError(f'Unhandled formula node when substituting Bool vars: {type(node)}')


def substitute_bool_vars(node: ASTp_Node, assignment: Dict[Var, bool]) -> ASTp_Node:
    """
    Replace every Bool `Var` listed in `assignment` by the corresponding `BoolLiteral` and constant-fold.

    Equivalence-preserving: the result has exactly the models of `node` that agree with `assignment`.
    That is stronger than what `simplify_formula_using_model_properties` offers (which invents values
    for Bool vars it has not seen, rewrites equations into aliases and is only satisfiability-preserving)
    and it is what makes both directions of the CEGAR loop's correctness argument trivial - a
    satisfiable residual gives a model of the original formula, an unsatisfiable one rules out exactly
    the assignment being blocked.

    Never mutates `node`: the loop substitutes into the same root on every iteration, so an in-place
    edit would poison every later iteration. Freshly built nodes get their `referenced_vars` recomputed
    bottom-up, since the evaluator relies on that field being accurate.
    """
    substituted_node, _ = _substitute_bool_vars_tracking_relevance(node, assignment)
    return substituted_node


# ---------------------------------------------------------------------------------------------
# The CEGAR loop
# ---------------------------------------------------------------------------------------------

def _make_sat_evaluation_result(ctx: EvaluationContext,
                                bool_assignment: Dict[Var, bool],
                                binary_model: Optional[Tuple],
                                solutions_nfa=None) -> Evaluation_Result:
    """
    Assemble the model reported for a satisfiable formula.

    The residual's automaton is built over the *whole* alphabet, the substituted-away Bool vars
    included, so it hands back arbitrary values for them - the SAT layer's assignment overwrites those.
    The result always carries a `model` dict (never `None`) since callers read `model is not None` as
    the sat/unsat verdict.
    """
    formula_params = tuple(var for var, var_info in ctx.var_table.items() if var_info.is_formula_param)

    if binary_model is None:
        model: Dict[Var, int] = {var: 0 for var in formula_params}
    else:
        model = convert_binary_model_into_decadic(binary_model, formula_params)

    for var, value in bool_assignment.items():
        model[var] = int(value)

    return Evaluation_Result(run_stats=ctx.stats, solutions_nfa=solutions_nfa, model=model, var_table=ctx.var_table)


def _make_unsat_evaluation_result(ctx: EvaluationContext) -> Evaluation_Result:
    return Evaluation_Result(run_stats=ctx.stats, solutions_nfa=None, model=None, var_table=ctx.var_table)


def _solve_residual_with_automata(residual: ASTp_Node, ctx: EvaluationContext):
    """
    Evaluate a residual formula with the ordinary automata engine.

    `parse.run_evaluation_procedure` is looked up on the module (not imported by value) on purpose:
    `cse_enabled()` swaps that very attribute out for the cache-aware evaluator, and only a dynamic
    lookup picks the replacement up.

    `ctx.enc_table` is dropped first. That table memoizes De Bruijn encodings keyed by `id(node)` and
    lives on the context, which this loop deliberately reuses across iterations for the sake of
    `ctx.automaton_cache`; since every iteration builds a fresh residual tree that dies at the end of
    the iteration, a stale entry could be matched by a *new* node that happens to be allocated at a
    recycled address. The automaton cache itself is keyed by content and is what we want to keep.
    """
    if getattr(ctx, 'enc_table', None) is not None:
        ctx.enc_table = {}

    return parse.run_evaluation_procedure(residual, ctx)


def solve_with_toplevel_sat(root: ASTp_Node,
                            ctx: EvaluationContext,
                            use_generalized_blocking: bool = True) -> Evaluation_Result:
    """
    Decide `root` by enumerating assignments of its free Bool vars with a SAT solver and handing the
    residual formulae to the automata engine. See the module docstring for the correctness argument.

    `use_generalized_blocking` controls how much each refuted assignment rules out.

    With it off, an unsatisfiable residual blocks exactly the assignment that produced it - correct, but
    weak: every free Bool var that had no bearing on the conflict gets re-explored under every future
    combination of the others, and the loop runs up to `2**k` theory calls.

    With it on, `_substitute_bool_vars_tracking_relevance` reports, alongside the residual, the set `S`
    of assigned vars the refutation actually depended on, and the clause blocks every assignment agreeing
    with the refuted one on `S` alone. Its guarantee at the root is

        for every assignment `b` agreeing with the refuted `a` on `S`:  root[b] entails root[a]

    and `root[a]` is the residual just shown to have no models, so `root[b]` has none either. Nothing
    satisfiable is ever blocked, and the clause still removes the current assignment, so the `2**k`
    termination bound survives.

    Note `S` is *not* "the vars still occurring in the residual". A var whose subtree was annihilated
    away no longer occurs in the residual yet decided it, and `S` keeps it - that is precisely the
    unsoundness `SAT_TOP_LEVEL.md` warns about. `S` is also not "the vars whose substitution changed the
    tree": that criterion is sound but nearly useless, because it never forgets a satisfied Bool unit of
    a top-level conjunction, which is the shape that dominates real inputs. See `Polarity`.

    An empty `S` means no Boolean assignment can rescue the formula, so the loop stops there with UNSAT
    instead of enumerating the rest.
    """
    with isolated_sat_formula_context():
        skeleton = extract_bool_skeleton(root, ctx)

        if not skeleton.free_bool_var_atoms:
            logger.info('Top-level SAT: no free Bool vars in the formula, evaluating it directly.')
            nfa = _solve_residual_with_automata(root, ctx)
            binary_model = nfa.find_model()
            if binary_model is None:
                return _make_unsat_evaluation_result(ctx)
            return _make_sat_evaluation_result(ctx, {}, binary_model, solutions_nfa=nfa)

        logger.info('Top-level SAT: %d free Bool vars, %d abstracted theory atoms.',
                    len(skeleton.free_bool_var_atoms), len(skeleton.abstraction_manager.abstrations))

        iteration_count = 0
        blocked_literal_count = 0
        exactly_blocked_literal_count = 0
        with pysat.solvers.Solver(bootstrap_with=skeleton.sat_formula) as sat_solver:
            while sat_solver.solve():
                iteration_count += 1
                bool_assignment = skeleton.decode_free_bool_vars(sat_solver.get_model())

                residual, relevant_vars = _substitute_bool_vars_tracking_relevance(root, bool_assignment)
                logger.debug('Top-level SAT: iteration %d, assignment %s', iteration_count, bool_assignment)

                if isinstance(residual, BoolLiteral):
                    # The Boolean part alone decided the formula; no theory call needed.
                    if residual.value:
                        return _make_sat_evaluation_result(ctx, bool_assignment, binary_model=None)
                else:
                    nfa = _solve_residual_with_automata(residual, ctx)
                    binary_model = nfa.find_model()
                    if binary_model is not None:  # An empty model is a *satisfiable* one - not falsy-testable
                        return _make_sat_evaluation_result(ctx, bool_assignment, binary_model, solutions_nfa=nfa)

                blocking_clause = skeleton.make_blocking_clause(
                    bool_assignment, restrict_to_vars=relevant_vars if use_generalized_blocking else None)
                blocked_literal_count += len(blocking_clause)
                exactly_blocked_literal_count += len(bool_assignment)

                if not blocking_clause:
                    # No assigned var mattered, so the residual just refuted *is* the whole formula's
                    # residual under every assignment: the formula is UNSAT and there is nothing left to
                    # enumerate. (Without generalized blocking this is only reachable when pysat simplifies
                    # every free Bool var out of the skeleton.) Adding the empty clause would say the same
                    # thing; some solver backends refuse it, so say it directly.
                    break
                sat_solver.add_clause(blocking_clause)

        logger.info('Top-level SAT: no Boolean assignment left to try after %d iterations, formula is UNSAT. '
                    'Blocking clauses spent %d literals, against the %d exact blocking would have spent - '
                    'the cheapest way to see how much of the search generalized blocking actually folded away.',
                    iteration_count, blocked_literal_count, exactly_blocked_literal_count)
        return _make_unsat_evaluation_result(ctx)


# ---------------------------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------------------------

def evaluate_prepared_formula_with_toplevel_sat(astp: ASTp_Node,
                                                ctx: EvaluationContext,
                                                use_generalized_blocking: bool = True) -> Evaluation_Result:
    """
    Evaluation strategy plugging `solve_with_toplevel_sat` into `perform_whole_evaluation_on_source_text`.

    The whole loop runs inside `cse_enabled()`: the case for this feature rests on residual formulae
    being nearly identical across iterations, so the automaton built for a subformula untouched by the
    changed assignment gets reused instead of rebuilt. `cse_enabled()` patches the module-global
    `parse.run_evaluation_procedure`, which is what makes *recursive* evaluations inside `parse.py`
    cached too; calling the cache-aware entry point directly would only ever cache the root, which
    differs every iteration and is therefore worthless.
    """
    if solver_config.backend_type != BackendType.MTBDD:
        logger.warning('Top-level SAT solving is running on the %s backend, where the automaton cache is a '
                       'no-op (it is MTBDD-only). Every iteration will rebuild the residual from scratch; '
                       'pass --backend MTBDD for this feature to have a chance of paying off.',
                       solver_config.backend_type.name)

    with cse_enabled():
        return solve_with_toplevel_sat(astp, ctx, use_generalized_blocking=use_generalized_blocking)


def perform_whole_evaluation_on_source_text_with_toplevel_sat(source_text: str, emit_introspect=None) -> Optional[Evaluation_Result]:
    """ Convenience wrapper: `perform_whole_evaluation_on_source_text` driven by the top-level SAT loop. """
    return parse.perform_whole_evaluation_on_source_text(
        source_text,
        emit_introspect=emit_introspect,
        evaluate_prepared_formula=evaluate_prepared_formula_with_toplevel_sat,
    )
