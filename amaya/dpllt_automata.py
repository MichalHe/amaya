"""
(EXPERIMENTAL) DPLL(T)-style top-level solving with an automata theory backend - see
`docs/DPLLT_WITH_AUTOMATA.md` for the design this implements.

The formula is written as `phi AND chi`, where `chi` collects the top-level conjuncts in which every
quantifier occurs in positive polarity (equivalently, since `preprocess_ast` rewrites `forall` into
`not exists not`, no `AST_Quantifier` of `chi` has an `AST_Negation` ancestor inside `chi`). The
strategy is:

1. Rename the binders of `chi` apart, then abstract its literals into a *monotone* Boolean formula:
   `AND`/`OR` are kept, quantifiers are dropped, and every literal - `Relation`, `Congruence`, `Var`,
   or a negation of one of those - becomes a Boolean variable of its own. A literal and its negation
   receive *different* Boolean variables, which is what keeps the abstraction monotone.
2. Ask a SAT solver for a model of the abstraction, and reduce the set of literals it sets to true to
   a minimal implicant of the abstraction.
3. Assert exactly those literals: build `exists X. AND(asserted literals)`, where `X` are the binders
   of `chi` that the asserted literals mention. Optimize that assertion and evaluate it with the
   ordinary automata engine, reusing cached automata for its parts.
4. Intersect with the automaton for `phi`, which is built once and retained for the whole run. A
   non-empty intersection is a model of the whole formula.
5. Otherwise add the clause forbidding every literal set that contains the refuted one, and go back
   to 2. When the SAT solver runs out of models, the formula is unsatisfiable.

Correctness rests on three facts, each argued in full in `docs/DPLLT_WITH_AUTOMATA.md` §5.3:

* *Soundness of one iteration.* The asserted conjunction entails `chi`. Asserting only the
  *positively* assigned literals is enough precisely because the abstraction is monotone: any
  assignment satisfying the asserted literals induces a Boolean assignment pointwise above the SAT
  model, which therefore still satisfies the abstraction; the positive-polarity existentials of `chi`
  are then re-introduced by taking the witnesses from that very assignment.
* *Completeness of the enumeration.* Every model of `phi AND chi` induces a Boolean model of the
  abstraction whose asserted set is satisfiable, and the blocking clauses only ever remove literal
  sets that contain an already-refuted one - each of which entails the refuted conjunction.
* *Termination.* Each iteration adds a clause falsified by the current model, over a variable set
  fixed at abstraction time, so the loop performs at most `2**|literals|` theory calls.

Two properties of the formula are established by this module rather than assumed, because no pass
guarantees them: negations sit directly above atoms (`push_negations_towards_atoms`, run
unconditionally here), and no two binders of `chi` share a `Var` id
(`freshen_bound_variables_in_subformula`). The second is not a cosmetic normalization - hoisting the
binders of two `AST_Quantifier` nodes that share an id into one prefix would force a single value on
two independent binders and report UNSAT for satisfiable formulae.
"""
from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass, field
from enum import IntEnum
import sys
from typing import Dict, FrozenSet, Hashable, List, Optional, Sequence, Set, Tuple

import pysat.formula
import pysat.solvers

from amaya import logger, parse
from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.config import (
    ASSERTION_OPTIMIZER_MODE_FULL,
    ASSERTION_OPTIMIZER_MODE_NONE,
    ASSERTION_OPTIMIZER_MODE_RESTRICTED,
    BackendType,
    DpllTAutomataConfig,
    SolutionDomain,
    solver_config,
)
from amaya.cse_cache import cse_enabled
from amaya.parse import Evaluation_Result, convert_binary_model_into_decadic
from amaya.preprocessing import flatten_bool_nary_connectives
from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars
from amaya.preprocessing.eval import VarInfo
from amaya.preprocessing.pipeline import Optimization_Pipeline, build_registry
from amaya.preprocessing.structural_id import Structural_Id_Table, compute_structural_id
from amaya.preprocessing.unbound_vars import push_negations_towards_atoms
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Leaf_Type_List,
    ASTp_Node,
    BoolLiteral,
    Bound_Type,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    format_formula,
    get_hard_bound_semantics,
)
from amaya.sat import compute_atom_abstraction_key
from amaya.sat_toplevel import isolated_sat_formula_context
from amaya.solver_core import EvaluationContext
from amaya.stats import ParsingOperation


ASSERTION_OPTIMIZER_SOLUTION_SET_PRESERVING_PASSES: FrozenSet[str] = frozenset()
"""
Names of the passes that may be applied to a single assertion rather than to the whole formula.

The pipeline's passes are whole-formula rewrites, and the contract they satisfy - preserving
satisfiability of the formula they are handed - is *not* enough here: the assertion's automaton is
afterwards intersected with the automaton for `phi`, so a pass must preserve the assertion's solution
set over the variables it shares with `phi`, not merely its satisfiability. At least one registered
pass violates this: `amaya.preprocessing.theory_reasoning._simplify_formula_using_model_properties`
asserts a value for a Bool variable it has not seen and simplifies the rest under that assumption,
which can fix a Bool parameter that `phi` constrains the other way.

Populating this set requires classifying every pass in
`amaya.preprocessing.pipeline._registry_definition` as one of: preserves the solution set over free
variables; preserves it only for existentially quantified variables; preserves satisfiability only.
That classification has not been performed, so the set is empty and the `restricted` mode behaves as
`none`. See `docs/DPLLT_WITH_AUTOMATA.md` §7.2.
"""


# ---------------------------------------------------------------------------------------------
# Splitting the formula into the general part and the positive-existential part
# ---------------------------------------------------------------------------------------------

def is_literal_node(node: ASTp_Node) -> bool:
    """
    Whether `node` is a literal: an atom, a Bool variable, a Bool constant, or a negation of one of
    those.

    A negated `Relation` is a literal in its own right even though `Relation.negate` could turn a
    negated `<=` into a plain `Relation`; that rewriting is `push_negations_towards_atoms`'s business,
    and the two negated forms that survive it - a disequality `NOT (= ...)` and a negated
    `Congruence` - have no single-atom equivalent at all.
    """
    match node:
        case Relation() | Congruence() | Var() | BoolLiteral():
            return True
        case AST_Negation():
            return isinstance(node.child, ASTp_Leaf_Type_List)
        case _:
            return False


def is_chi_eligible_subformula(node: ASTp_Node) -> bool:
    """
    Whether `node` is built from literals using `AND`, `OR` and `exists` only.

    `EQUIV` and a negation over a non-literal are both rejected, for the same reason: they place a
    subformula in negative or in mixed polarity, and the assertion rule of this module
    (`build_assertion_formula_for_atom_ids`) is correct only for an abstraction that is monotone in
    its literals.
    """
    if is_literal_node(node):
        return True

    match node:
        case AST_Connective():
            if node.type not in (Connective_Type.AND, Connective_Type.OR):
                return False
            return all(is_chi_eligible_subformula(child) for child in node.children)
        case AST_Quantifier():
            return is_chi_eligible_subformula(node.child)

    return False


def does_subformula_contain_disjunction(node: ASTp_Node) -> bool:
    """
    Whether `node` contains an `OR`.

    A `chi` without one has a single minimal implicant - all of its literals - so the loop would
    perform one iteration doing the same work as the ordinary evaluator, plus the cost of the
    abstraction. `split_formula_into_phi_and_chi`'s caller uses this to fall through instead.
    """
    match node:
        case AST_Connective():
            if node.type == Connective_Type.OR:
                return True
            return any(does_subformula_contain_disjunction(child) for child in node.children)
        case AST_Quantifier() | AST_Negation():
            return does_subformula_contain_disjunction(node.child)
        case _:
            return False


@dataclass
class Formula_Split:
    """ The top-level conjuncts of a formula, partitioned by `is_chi_eligible_subformula`. """

    phi_conjuncts: Tuple[ASTp_Node, ...]
    """ The conjuncts the ordinary evaluator handles; their automaton is built once. """

    chi_conjuncts: Tuple[ASTp_Node, ...]
    """ The positive-existential conjuncts, whose literals are abstracted and enumerated. """


def split_formula_into_phi_and_chi(root: ASTp_Node) -> Formula_Split:
    """
    Partition the top-level conjunction of `root` into the general part and the positive-existential
    part. A non-conjunction root is treated as a one-element conjunction.

    The caller is responsible for having flattened the top-level `AND` beforehand: a binary `AND`
    chain hides conjuncts that would otherwise be split apart.
    """
    if isinstance(root, AST_Connective) and root.type == Connective_Type.AND:
        conjuncts: Tuple[ASTp_Node, ...] = root.children
    else:
        conjuncts = (root,)

    phi_conjuncts: List[ASTp_Node] = []
    chi_conjuncts: List[ASTp_Node] = []
    for conjunct in conjuncts:
        if is_chi_eligible_subformula(conjunct):
            chi_conjuncts.append(conjunct)
        else:
            phi_conjuncts.append(conjunct)

    return Formula_Split(phi_conjuncts=tuple(phi_conjuncts), chi_conjuncts=tuple(chi_conjuncts))


def make_conjunction_of_conjuncts(conjuncts: Tuple[ASTp_Node, ...]) -> ASTp_Node:
    """
    The conjunction of `conjuncts`, with `referenced_vars` filled in.

    A single conjunct is returned as it is, rather than wrapped in a one-child `AND`: the evaluator
    handles that shape (`amaya.parse.evaluate_binary_conjunction_expr` has a case for it) but several
    passes and this module's own `Assertion_Automaton_Builder` read a conjunction as a list of two or
    more operands.
    """
    if len(conjuncts) == 1:
        return conjuncts[0]

    conjunction = AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND, children=conjuncts)
    fill_referenced_vars(conjunction)
    return conjunction


def display_positive_existential_part_and_exit(split: Formula_Split):
    """
    Print the positive-existential part of the split and terminate the process.

    The formula printed is the one the split produced, i.e. *before*
    `freshen_bound_variables_in_subformula` renames its binders apart, so its variable ids are those of
    the input formula rather than those the per-iteration logs show.

    Terminating here rather than returning a verdict mirrors
    `preprocessing.show_preprocessed_formula` and `preprocessing.display_var_table`
    (`amaya/parse.py:perform_whole_evaluation_on_source_text`), and it is what makes the option usable
    on an input the strategy would decline: the display happens before either fall-through, so it
    reports an empty part instead of silently handing the formula to the ordinary evaluator.
    """
    print('----- Positive-existential part (chi) -----')
    if not split.chi_conjuncts:
        print('<empty - no top-level conjunct of the formula is positive-existential>')
    else:
        print(format_formula(make_conjunction_of_conjuncts(split.chi_conjuncts)))
    sys.exit(0)


def _format_count(count: int, hit_limit: bool) -> str:
    return f'>= {count} (enumeration stopped at the limit)' if hit_limit else str(count)


def display_abstraction_model_counts_and_exit(split: Formula_Split,
                                              var_table: Dict[Var, VarInfo],
                                              enumeration_limit: int):
    """
    Print what the Boolean abstraction of the positive-existential part admits, and terminate.

    Constructs no automaton, so this reports on formulae the strategy itself could not finish. It does
    rename the binders apart first (`freshen_bound_variables_in_subformula`), which extends `var_table`
    - harmless, since the process ends here - because the abstraction merges equal literals and the
    count would otherwise be that of a different abstraction than the loop enumerates.

    Placed next to `display_positive_existential_part_and_exit` and, like it, run before either
    fall-through of the split, so an input the strategy would decline is reported on rather than
    evaluated.
    """
    print('----- Boolean abstraction of the positive-existential part (chi) -----')
    if not split.chi_conjuncts:
        print('<empty - no top-level conjunct of the formula is positive-existential>')
        sys.exit(0)

    chi_conjuncts = tuple(freshen_bound_variables_in_subformula(conjunct, var_table)
                          for conjunct in split.chi_conjuncts)

    # Each count is printed as soon as it is known, and the implicants are counted first. The model
    # count is bounded by `2**(abstracted literals)` and the implicant count by the number of
    # antichains over the same set, so on any formula large enough to be worth asking about, the limit
    # binds and the enumeration runs for the whole budget. Computing both before printing anything
    # would spend that budget on the model count - the less useful of the two - and report neither.
    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula(chi_conjuncts)
        print(f'abstracted literals:  {abstraction.atom_count}', flush=True)

        implicant_count, implicant_hit_limit = count_minimal_implicants_of_abstraction(abstraction,
                                                                                       enumeration_limit)
        print(f'minimal implicants:   {_format_count(implicant_count, implicant_hit_limit)}')
        print('The minimal implicants are the assertions the loop constructs; their count is the number '
              'of theory calls it makes when every assertion is refuted.', flush=True)

        model_count, model_hit_limit = count_models_of_abstraction(abstraction, enumeration_limit)
        print(f'models:               {_format_count(model_count, model_hit_limit)}')

    sys.exit(0)


def normalize_formula_for_splitting(root: ASTp_Node) -> ASTp_Node:
    """
    Push negations towards atoms and flatten binary connective chains, unconditionally.

    Both rewrites are gated by `-O` flags on the ordinary path
    (`push_negation_towards_atoms`, `flatten_connectives`) and both are preconditions of the split
    rather than optimizations here: without the first, a `NOT (AND ...)` conjunct is not eligible even
    when every negation it contains would end up above an atom; without the second, the top-level
    conjunction is not visible as a list of conjuncts.
    """
    normalized_root = push_negations_towards_atoms(root)
    normalized_root = flatten_bool_nary_connectives(normalized_root)
    fill_referenced_vars(normalized_root)
    return normalized_root


# ---------------------------------------------------------------------------------------------
# Renaming the binders of chi apart
# ---------------------------------------------------------------------------------------------

@dataclass
class Fresh_Variable_Allocator:
    """ Hands out `Var` ids not present in `var_table`, recording each one in it. """

    var_table: Dict[Var, VarInfo]
    next_var_id: int

    @staticmethod
    def for_var_table(var_table: Dict[Var, VarInfo]) -> 'Fresh_Variable_Allocator':
        next_var_id = max((var.id for var in var_table), default=0) + 1
        return Fresh_Variable_Allocator(var_table=var_table, next_var_id=next_var_id)

    def allocate_copy_of_variable(self, original_var: Var) -> Var:
        fresh_var = Var(id=self.next_var_id)
        self.next_var_id += 1

        original_var_info = self.var_table.get(original_var)
        if original_var_info is None:
            raise ValueError(f'Cannot rename a variable that is not present in the var table: {original_var}')

        self.var_table[fresh_var] = VarInfo(name=f'{original_var_info.name}#{fresh_var.id}',
                                            type=original_var_info.type,
                                            comment=original_var_info.comment,
                                            is_formula_param=False)
        return fresh_var


def _substitute_vars_in_atom_terms(atom: Relation | Congruence,
                                   substitution: Dict[Var, Var]) -> Relation | Congruence:
    """
    Rebuild `atom` with its variables renamed, keeping its linear terms sorted by variable.

    Never mutates `atom`: `Relation` and `Congruence` are mutable dataclasses shared with the tree the
    caller was handed. The re-sorting matters because fresh ids are larger than the ones they replace,
    so a plain substitution would leave the term list unsorted and break
    `Relation.is_in_canoical_form`, which several passes and constructions rely on.
    """
    renamed_terms = sorted((substitution.get(var, var), coef) for coef, var in zip(atom.coefs, atom.vars))
    renamed_vars = [var for var, _ in renamed_terms]
    renamed_coefs = [coef for _, coef in renamed_terms]

    if isinstance(atom, Relation):
        return Relation(vars=renamed_vars, coefs=renamed_coefs, rhs=atom.rhs,
                        predicate_symbol=atom.predicate_symbol)
    return Congruence(vars=renamed_vars, coefs=renamed_coefs, rhs=atom.rhs, modulus=atom.modulus)


def _freshen_bound_variables(node: ASTp_Node,
                             substitution: Dict[Var, Var],
                             allocator: Fresh_Variable_Allocator) -> ASTp_Node:
    """ `freshen_bound_variables_in_subformula`'s recursion; returns `node` itself when nothing changes. """
    match node:
        case Var():
            return substitution.get(node, node)

        case BoolLiteral():
            return node

        case Relation() | Congruence():
            if not any(var in substitution for var in node.vars):
                return node
            return _substitute_vars_in_atom_terms(node, substitution)

        case AST_Negation():
            renamed_child = _freshen_bound_variables(node.child, substitution, allocator)
            if renamed_child is node.child:
                return node
            return AST_Negation(referenced_vars=node.referenced_vars, child=renamed_child)

        case AST_Connective():
            renamed_children = tuple(_freshen_bound_variables(child, substitution, allocator)
                                     for child in node.children)
            if all(renamed is original for renamed, original in zip(renamed_children, node.children)):
                return node
            return AST_Connective(referenced_vars=node.referenced_vars, type=node.type,
                                  children=renamed_children)

        case AST_Quantifier():
            # A binder always allocates, so that two `AST_Quantifier` nodes sharing a `Var` id (which
            # miniscoping can produce) end up binding different variables. The extended substitution
            # shadows the outer one for the duration of the subtree, as scoping requires.
            substitution_inside_binder = dict(substitution)
            fresh_bound_vars: List[Var] = []
            for bound_var in node.bound_vars:
                fresh_bound_var = allocator.allocate_copy_of_variable(bound_var)
                substitution_inside_binder[bound_var] = fresh_bound_var
                fresh_bound_vars.append(fresh_bound_var)

            renamed_child = _freshen_bound_variables(node.child, substitution_inside_binder, allocator)
            return AST_Quantifier(referenced_vars=node.referenced_vars,
                                  bound_vars=tuple(fresh_bound_vars),
                                  child=renamed_child)

    raise ValueError(f'Unhandled formula node while renaming bound variables apart: {type(node)}')


def freshen_bound_variables_in_subformula(node: ASTp_Node, var_table: Dict[Var, VarInfo]) -> ASTp_Node:
    """
    Return `node` with every binder rebound to freshly allocated variables, extending `var_table` with
    one entry per allocated variable (`is_formula_param=False`, type copied from the original).

    Needed because `build_assertion_formula_for_atom_ids` hoists the binders of the asserted literals
    into a single existential prefix. `Scoper` (`amaya/preprocessing/eval.py`) gives every binder a
    globally fresh id, but nothing re-establishes that after `optimize_formula_structure`: pushing a
    quantifier into a disjunction duplicates the binder, leaving two `AST_Quantifier` nodes that bind
    the same `Var` id and mean different variables. Hoisting those into one prefix would force them to
    take the same value.
    """
    allocator = Fresh_Variable_Allocator.for_var_table(var_table)
    freshened_node = _freshen_bound_variables(node, {}, allocator)
    fill_referenced_vars(freshened_node)
    return freshened_node


def collect_bound_vars_of_subformula(node: ASTp_Node) -> FrozenSet[Var]:
    """ The variables bound by any `AST_Quantifier` inside `node`. """
    match node:
        case AST_Quantifier():
            return frozenset(node.bound_vars) | collect_bound_vars_of_subformula(node.child)
        case AST_Negation():
            return collect_bound_vars_of_subformula(node.child)
        case AST_Connective():
            collected: FrozenSet[Var] = frozenset()
            for child in node.children:
                collected |= collect_bound_vars_of_subformula(child)
            return collected
        case _:
            return frozenset()


# ---------------------------------------------------------------------------------------------
# The monotone Boolean abstraction
# ---------------------------------------------------------------------------------------------

def compute_literal_abstraction_key(literal: ASTp_Node) -> Hashable:
    """
    A hashable stand-in for a literal, equal exactly for two occurrences that denote the same literal.

    Delegates to `amaya.sat.compute_atom_abstraction_key` for `Relation`/`Congruence` (whose meaning is
    determined by their own fields once variables have been disambiguated) and extends it to the two
    literal forms that function does not cover: a Bool variable, and a negation. Note that
    `compute_atom_abstraction_key` would key both of those on *object identity*, which would give two
    occurrences of one and the same negated atom two different Boolean variables - sound, but it turns
    every shared literal into two independent ones.
    """
    match literal:
        case Relation() | Congruence():
            return compute_atom_abstraction_key(literal)
        case Var():
            return ('bool-var', literal.id)
        case BoolLiteral():
            return ('bool-literal', literal.value)
        case AST_Negation():
            return ('neg', compute_literal_abstraction_key(literal.child))

    raise ValueError(f'Cannot compute an abstraction key for a non-literal node: {type(literal)}')


class Monotone_Skeleton_Node_Type(IntEnum):
    ATOM = 0x01
    CONJUNCTION = 0x02
    DISJUNCTION = 0x03
    CONSTANT = 0x04


@dataclass(frozen=True)
class Monotone_Skeleton_Node:
    """
    A node of the Boolean abstraction of `chi`, in a form that can be evaluated against a set of
    asserted atom ids without going through the SAT solver (see `evaluate_monotone_skeleton`).

    The skeleton contains no negation node - that is the property the assertion rule depends on, and
    keeping the skeleton in a representation that cannot express one makes it checkable (T5).
    """
    type: Monotone_Skeleton_Node_Type
    atom_id: int = -1
    constant_value: bool = False
    children: Tuple['Monotone_Skeleton_Node', ...] = tuple()


@dataclass
class Literal_Abstraction_Manager:
    """ Assigns an id to every distinct literal, keyed by `compute_literal_abstraction_key`. """

    atom_id_by_literal_key: Dict[Hashable, int] = field(default_factory=dict)
    literal_by_atom_id: Dict[int, ASTp_Node] = field(default_factory=dict)

    def get_id_for_literal(self, literal: ASTp_Node) -> int:
        abstraction_key = compute_literal_abstraction_key(literal)

        atom_id = self.atom_id_by_literal_key.get(abstraction_key)
        if atom_id is not None:
            return atom_id

        atom_id = len(self.atom_id_by_literal_key)
        self.atom_id_by_literal_key[abstraction_key] = atom_id
        self.literal_by_atom_id[atom_id] = literal
        return atom_id


@dataclass
class Monotone_Literal_Abstraction:
    """ The monotone Boolean abstraction of `chi`, plus what it takes to talk to the SAT solver about it. """

    sat_formula: pysat.formula.Formula
    skeleton: Monotone_Skeleton_Node
    manager: Literal_Abstraction_Manager
    pysat_atom_by_atom_id: Dict[int, pysat.formula.Atom] = field(default_factory=dict)
    solver_var_id_by_atom_id: Dict[int, int] = field(default_factory=dict)
    """
    Atom id -> the DIMACS variable the SAT solver sees. These are *not* the abstraction ids: they come
    from the `pysat` variable pool that clausification uses.
    """

    @property
    def atom_count(self) -> int:
        return len(self.manager.literal_by_atom_id)

    def resolve_solver_var_ids(self):
        """ Fill in `solver_var_id_by_atom_id`. Must run in the context the abstraction was built in. """
        vpool = pysat.formula.Formula.export_vpool(active=True)
        self.solver_var_id_by_atom_id = {
            atom_id: vpool.id(pysat_atom) for atom_id, pysat_atom in self.pysat_atom_by_atom_id.items()
        }

    def collect_asserted_atom_ids_from_sat_model(self, sat_model: Sequence[int]) -> Set[int]:
        """
        The ids of the literals the model sets to true.

        An atom the clausification simplified away does not occur in the model; it is reported as *not*
        asserted, and `minimize_asserted_atom_ids` re-checks the resulting set against the skeleton, so
        a set that turns out not to satisfy the abstraction is repaired rather than trusted.
        """
        value_of_solver_var = {abs(literal): (literal > 0) for literal in sat_model}
        return {
            atom_id for atom_id, solver_var_id in self.solver_var_id_by_atom_id.items()
            if value_of_solver_var.get(solver_var_id, False)
        }

    def make_blocking_clause(self, asserted_atom_ids: Set[int]) -> List[int]:
        """
        The clause forbidding every literal set that contains `asserted_atom_ids`.

        Every such set's assertion entails the assertion just refuted (it is a conjunction over a
        superset of literals, under a prefix binding a superset of variables, none of which occur in
        `phi`), so nothing satisfiable is blocked.
        """
        return [-self.solver_var_id_by_atom_id[atom_id] for atom_id in sorted(asserted_atom_ids)]

    def make_exact_blocking_clause(self, asserted_atom_ids: Set[int]) -> List[int]:
        """
        The clause forbidding exactly the assignment `asserted_atom_ids` describes, and no other.

        Unlike `make_blocking_clause` this mentions *every* abstracted literal, not only the asserted
        ones, so it removes one assignment per call rather than an up-set. It is what
        `count_models_of_abstraction` enumerates with; the loop itself must not use it, since blocking a
        single assignment at a time would re-derive the same assertion once per irrelevant literal.

        Mentioning every literal also makes the enumeration exact when the clausification simplified one
        away: such a literal is unconstrained, and naming it in a clause is what makes the solver
        enumerate both of its values instead of only the one `collect_asserted_atom_ids_from_sat_model`
        reads off a model that does not carry it.
        """
        return [
            (-solver_var_id if atom_id in asserted_atom_ids else solver_var_id)
            for atom_id, solver_var_id in sorted(self.solver_var_id_by_atom_id.items())
        ]


def _abstract_subformula(node: ASTp_Node,
                         manager: Literal_Abstraction_Manager,
                         pysat_atom_by_atom_id: Dict[int, pysat.formula.Atom],
                         ) -> Tuple[pysat.formula.Formula, Monotone_Skeleton_Node]:
    """ Build the pysat formula and the evaluable skeleton for `node` in one traversal. """
    constant_value = _constant_value_of_node(node)
    if constant_value is not None:
        pysat_formula = pysat.formula.PYSAT_TRUE if constant_value else pysat.formula.PYSAT_FALSE
        return pysat_formula, Monotone_Skeleton_Node(type=Monotone_Skeleton_Node_Type.CONSTANT,
                                                     constant_value=constant_value)

    if is_literal_node(node):
        atom_id = manager.get_id_for_literal(node)
        pysat_atom = pysat_atom_by_atom_id.get(atom_id)
        if pysat_atom is None:
            pysat_atom = pysat.formula.Atom(make_atom_name_for_abstracted_literal(atom_id))
            pysat_atom_by_atom_id[atom_id] = pysat_atom
        return pysat_atom, Monotone_Skeleton_Node(type=Monotone_Skeleton_Node_Type.ATOM, atom_id=atom_id)

    match node:
        case AST_Quantifier():
            # The quantifier is dropped; its binders are re-introduced per assertion by
            # `build_assertion_formula_for_atom_ids`.
            return _abstract_subformula(node.child, manager, pysat_atom_by_atom_id)

        case AST_Connective():
            abstracted_children = [_abstract_subformula(child, manager, pysat_atom_by_atom_id)
                                   for child in node.children]
            child_formulae = [child_formula for child_formula, _ in abstracted_children]
            child_skeletons = tuple(child_skeleton for _, child_skeleton in abstracted_children)

            if node.type == Connective_Type.AND:
                return (pysat.formula.And(*child_formulae),
                        Monotone_Skeleton_Node(type=Monotone_Skeleton_Node_Type.CONJUNCTION,
                                               children=child_skeletons))
            if node.type == Connective_Type.OR:
                return (pysat.formula.Or(*child_formulae),
                        Monotone_Skeleton_Node(type=Monotone_Skeleton_Node_Type.DISJUNCTION,
                                               children=child_skeletons))

    raise ValueError(f'Unhandled formula node while building the monotone abstraction: {type(node)}')


def _constant_value_of_node(node: ASTp_Node) -> Optional[bool]:
    """ The truth value of `node` if it is a Bool constant (possibly negated), None otherwise. """
    if isinstance(node, BoolLiteral):
        return node.value
    if isinstance(node, AST_Negation) and isinstance(node.child, BoolLiteral):
        return not node.child.value
    return None


def make_atom_name_for_abstracted_literal(atom_id: int) -> str:
    """
    Name of the `pysat` atom standing for an abstracted literal.

    `pysat` interns atoms by name, so the namespace must not collide with the one
    `amaya.sat.make_atom_name_for_theory_atom` uses - both number their atoms from zero, and the two
    abstractions can be built in one process.
    """
    return f'dpllt-literal:{atom_id}'


def abstract_chi_into_monotone_sat_formula(chi_conjuncts: Sequence[ASTp_Node]) -> Monotone_Literal_Abstraction:
    """
    Abstract the conjunction of `chi_conjuncts` into a monotone Boolean formula.

    Must be called inside `isolated_sat_formula_context`. Every literal becomes a Boolean variable of
    its own; a literal and its negation are two different variables, so the abstraction does not record
    that they are complementary. That is a relaxation, never an error: if the solver sets both, the
    assertion contains a contradictory pair, the theory call returns an empty automaton and the pair is
    blocked.
    """
    manager = Literal_Abstraction_Manager()
    pysat_atom_by_atom_id: Dict[int, pysat.formula.Atom] = {}

    abstracted_conjuncts = [_abstract_subformula(conjunct, manager, pysat_atom_by_atom_id)
                            for conjunct in chi_conjuncts]
    conjunct_formulae = [conjunct_formula for conjunct_formula, _ in abstracted_conjuncts]
    conjunct_skeletons = tuple(conjunct_skeleton for _, conjunct_skeleton in abstracted_conjuncts)

    if len(conjunct_formulae) == 1:
        sat_formula = conjunct_formulae[0]
        skeleton = conjunct_skeletons[0]
    else:
        sat_formula = pysat.formula.And(*conjunct_formulae)
        skeleton = Monotone_Skeleton_Node(type=Monotone_Skeleton_Node_Type.CONJUNCTION,
                                          children=conjunct_skeletons)

    abstraction = Monotone_Literal_Abstraction(sat_formula=sat_formula, skeleton=skeleton, manager=manager,
                                               pysat_atom_by_atom_id=pysat_atom_by_atom_id)
    abstraction.resolve_solver_var_ids()
    return abstraction


def evaluate_monotone_skeleton(skeleton: Monotone_Skeleton_Node, asserted_atom_ids: Set[int]) -> bool:
    """ Evaluate the abstraction treating exactly the atoms in `asserted_atom_ids` as true. """
    match skeleton.type:
        case Monotone_Skeleton_Node_Type.ATOM:
            return skeleton.atom_id in asserted_atom_ids
        case Monotone_Skeleton_Node_Type.CONSTANT:
            return skeleton.constant_value
        case Monotone_Skeleton_Node_Type.CONJUNCTION:
            return all(evaluate_monotone_skeleton(child, asserted_atom_ids) for child in skeleton.children)
        case Monotone_Skeleton_Node_Type.DISJUNCTION:
            return any(evaluate_monotone_skeleton(child, asserted_atom_ids) for child in skeleton.children)

    raise ValueError(f'Unhandled monotone skeleton node type: {skeleton.type}')


def minimize_asserted_atom_ids(abstraction: Monotone_Literal_Abstraction,
                               asserted_atom_ids: Set[int]) -> Set[int]:
    """
    Reduce `asserted_atom_ids` to a subset that still satisfies the abstraction and none of whose
    proper subsets does.

    A monotone abstraction is satisfied by the all-true assignment, so an unminimized SAT model tends
    to assert every literal of `chi`, which makes the theory call at least as expensive as evaluating
    `chi` directly. The reduction is a greedy deletion driven by `evaluate_monotone_skeleton`, which is
    a linear evaluation of the abstraction - no SAT call is involved. Removal is attempted in
    descending order of `amaya.parse.estimate_automaton_size`, so the literals whose automata are
    largest are the first candidates to go.

    The result is still a model of the abstraction, so it carries the same guarantees as the SAT
    solver's own; it additionally shortens the blocking clause, which then excludes more literal sets.
    """
    surviving_atom_ids = set(asserted_atom_ids)

    if not evaluate_monotone_skeleton(abstraction.skeleton, surviving_atom_ids):
        # The clausification can drop an atom the abstraction does not depend on, in which case the
        # model does not mention it and it was not collected. Starting from the all-true set is always
        # a model of a monotone abstraction that the solver just reported satisfiable.
        logger.debug('DPLL(T): the literal set reported by the SAT solver does not satisfy the abstraction; '
                     'starting the minimization from the set of all literals.')
        surviving_atom_ids = set(abstraction.manager.literal_by_atom_id)

    removal_order = sorted(surviving_atom_ids,
                           key=lambda atom_id: parse.estimate_automaton_size(abstraction.manager.literal_by_atom_id[atom_id]),
                           reverse=True)

    for atom_id in removal_order:
        candidate_atom_ids = surviving_atom_ids - {atom_id}
        if evaluate_monotone_skeleton(abstraction.skeleton, candidate_atom_ids):
            surviving_atom_ids = candidate_atom_ids

    return surviving_atom_ids


# ---------------------------------------------------------------------------------------------
# Refuting an assertion by its variable bounds alone
# ---------------------------------------------------------------------------------------------

@dataclass
class Bounds_Refutation:
    """
    An unsatisfiable subset of the asserted literals, found by intersecting their unit bounds.

    `atom_ids` holds one or two literals - a single unit equality that has no integer solution, or a
    lower and an upper bound on one variable that cannot both hold. It is unsatisfiable on its own,
    independently of the general part and of every other asserted literal, which is what lets the
    caller block it instead of the whole implicant.
    """

    var: Var
    atom_ids: FrozenSet[int]
    reason: str
    """ Human-readable statement of the clash, for the log. """


@dataclass
class _Bound_With_Provenance:
    """ A bound on one variable, together with the asserted literal that imposed it. """
    limit: int
    atom_id: int


def _derive_unit_bounds_of_literal(literal: ASTp_Node) -> Optional[Tuple[Var, Optional[int], Optional[int], bool]]:
    """
    The bounds a single literal imposes on a single variable, as `(var, lower, upper, is_unsatisfiable)`.

    Returns None for a literal that constrains no single variable by a bound - anything but a `<=` or
    an `=` over one variable. `is_unsatisfiable` marks a unit equality with no integer solution
    (`c*x = r` with `r` not divisible by `c`), which is a refutation on its own.

    A `Congruence` is deliberately not read as a bound: it constrains a residue, not a range.
    """
    if not isinstance(literal, Relation):
        return None

    if literal.is_hard_bound():
        bound_type, var, implied_value = get_hard_bound_semantics(literal)
        if bound_type == Bound_Type.LOWER:
            return var, implied_value, None, False
        return var, None, implied_value, False

    if literal.specifies_a_single_value_for_var():
        var, coefficient = literal.vars[0], literal.coefs[0]
        if coefficient == 0:
            return None
        if literal.rhs % coefficient != 0:
            return var, None, None, True
        implied_value = literal.rhs // coefficient
        return var, implied_value, implied_value, False

    return None


def find_bounds_refutation(asserted_atom_ids: Set[int],
                           abstraction: Monotone_Literal_Abstraction) -> Optional[Bounds_Refutation]:
    """
    Look for an unsatisfiable pair of unit bounds among the asserted literals, and report which
    literals form it.

    One pass over the asserted literals, tracking for each variable the strongest lower and upper
    bound seen so far *and the literal that imposed it*; the first time a variable's lower bound
    exceeds its upper bound, those two literals are the refutation. `Value_Interval` performs the same
    intersection (`amaya/relations_structures.py:Value_Interval.apply_assertion`) but keeps no
    provenance, and the provenance is the whole point here - it is what turns "this assertion is
    unsatisfiable" into "these two literals are unsatisfiable", which blocks every literal set
    containing them rather than only the supersets of this one implicant.

    Costs one dictionary update per unit-bound literal and no automaton. Incomplete by construction:
    it sees only bounds on a single variable, so an assertion it accepts may still be unsatisfiable,
    and the caller must go on to the theory call.
    """
    lower_bound_of_var: Dict[Var, _Bound_With_Provenance] = {}
    upper_bound_of_var: Dict[Var, _Bound_With_Provenance] = {}

    for atom_id in sorted(asserted_atom_ids):
        derived_bounds = _derive_unit_bounds_of_literal(abstraction.manager.literal_by_atom_id[atom_id])
        if derived_bounds is None:
            continue
        var, lower_limit, upper_limit, is_unsatisfiable = derived_bounds

        if is_unsatisfiable:
            return Bounds_Refutation(var=var, atom_ids=frozenset((atom_id,)),
                                     reason=f'{var} is constrained by a unit equality with no integer solution')

        if lower_limit is not None:
            known_lower = lower_bound_of_var.get(var)
            if known_lower is None or lower_limit > known_lower.limit:
                lower_bound_of_var[var] = _Bound_With_Provenance(limit=lower_limit, atom_id=atom_id)

        if upper_limit is not None:
            known_upper = upper_bound_of_var.get(var)
            if known_upper is None or upper_limit < known_upper.limit:
                upper_bound_of_var[var] = _Bound_With_Provenance(limit=upper_limit, atom_id=atom_id)

        strongest_lower, strongest_upper = lower_bound_of_var.get(var), upper_bound_of_var.get(var)
        if strongest_lower is None or strongest_upper is None:
            continue
        if strongest_lower.limit <= strongest_upper.limit:
            continue

        return Bounds_Refutation(
            var=var,
            atom_ids=frozenset((strongest_lower.atom_id, strongest_upper.atom_id)),
            reason=f'{var} is bounded below by {strongest_lower.limit} and above by {strongest_upper.limit}',
        )

    return None


# ---------------------------------------------------------------------------------------------
# Counting what the abstraction admits
# ---------------------------------------------------------------------------------------------

@dataclass
class Abstraction_Model_Counts:
    """
    What the Boolean abstraction of `chi` admits, as counted by `count_abstraction_models`.

    The two counts answer different questions. `total_model_count` is the size of the search space the
    abstraction describes - the number of truth assignments to the abstracted literals that satisfy it.
    `minimal_implicant_count` is the number of assertions the loop would actually construct if every
    theory call refuted its assertion, i.e. the worst-case number of theory calls on this formula; it
    is the iteration count design §16 item 2 leaves unmeasured.

    Either enumeration stops at the configured limit, in which case the corresponding
    `..._hit_limit` flag is set and the count is a lower bound.
    """

    abstracted_literal_count: int = 0
    total_model_count: int = 0
    total_model_enumeration_hit_limit: bool = False
    minimal_implicant_count: int = 0
    minimal_implicant_enumeration_hit_limit: bool = False


def count_models_of_abstraction(abstraction: Monotone_Literal_Abstraction,
                                enumeration_limit: int) -> Tuple[int, bool]:
    """
    The number of truth assignments to the abstracted literals that satisfy the abstraction.

    Returns `(count, hit_limit)`. Each model is blocked exactly
    (`Monotone_Literal_Abstraction.make_exact_blocking_clause`), so the count is over the abstracted
    literals alone - the auxiliary variables clausification introduces are projected out and never
    inflate it, which is what a plain `pysat.solvers.Solver.enum_models` would do instead.

    The count is at most `2**abstraction.atom_count` and can reach it, hence the limit.
    """
    model_count = 0
    with pysat.solvers.Solver(bootstrap_with=abstraction.sat_formula) as sat_solver:
        while sat_solver.solve():
            if model_count >= enumeration_limit:
                return model_count, True

            asserted_atom_ids = abstraction.collect_asserted_atom_ids_from_sat_model(sat_solver.get_model())
            model_count += 1

            blocking_clause = abstraction.make_exact_blocking_clause(asserted_atom_ids)
            if not blocking_clause:
                break  # The abstraction has no literals at all, so its single model has just been counted
            sat_solver.add_clause(blocking_clause)

    return model_count, False


def count_minimal_implicants_of_abstraction(abstraction: Monotone_Literal_Abstraction,
                                            enumeration_limit: int) -> Tuple[int, bool]:
    """
    The number of minimal implicants of the abstraction. Returns `(count, hit_limit)`.

    This runs `_enumerate_implicants`'s enumeration with the theory calls left out: take a model,
    reduce it to a minimal implicant, block that implicant's up-set, repeat. The count is exact, not an
    over-count: every iteration yields a minimal implicant not yet seen, because a model containing an
    already-blocked one would have been excluded by its blocking clause; and the enumeration stops only
    once every minimal implicant has been blocked.

    It is therefore the number of theory calls the loop makes on a formula whose every assertion is
    refuted - the worst case - and an upper bound on the number it makes on any formula.
    """
    minimal_implicant_count = 0
    with pysat.solvers.Solver(bootstrap_with=abstraction.sat_formula) as sat_solver:
        while sat_solver.solve():
            if minimal_implicant_count >= enumeration_limit:
                return minimal_implicant_count, True

            asserted_atom_ids = abstraction.collect_asserted_atom_ids_from_sat_model(sat_solver.get_model())
            asserted_atom_ids = minimize_asserted_atom_ids(abstraction, asserted_atom_ids)
            minimal_implicant_count += 1

            blocking_clause = abstraction.make_blocking_clause(asserted_atom_ids)
            if not blocking_clause:
                break  # The abstraction is satisfied by asserting nothing; that implicant is the only one
            sat_solver.add_clause(blocking_clause)

    return minimal_implicant_count, False


def count_abstraction_models(chi_conjuncts: Sequence[ASTp_Node],
                             enumeration_limit: int) -> Abstraction_Model_Counts:
    """
    Build the abstraction of `chi_conjuncts` and count what it admits. Constructs no automaton.

    `chi_conjuncts` must already have had their binders renamed apart: the abstraction merges two
    occurrences of one literal into a single Boolean variable, so counting over an unfreshened `chi`
    would count the models of a different abstraction than the loop enumerates.
    """
    if not chi_conjuncts:
        return Abstraction_Model_Counts()

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula(chi_conjuncts)

        total_model_count, total_hit_limit = count_models_of_abstraction(abstraction, enumeration_limit)
        minimal_implicant_count, implicant_hit_limit = count_minimal_implicants_of_abstraction(
            abstraction, enumeration_limit)

        return Abstraction_Model_Counts(
            abstracted_literal_count=abstraction.atom_count,
            total_model_count=total_model_count,
            total_model_enumeration_hit_limit=total_hit_limit,
            minimal_implicant_count=minimal_implicant_count,
            minimal_implicant_enumeration_hit_limit=implicant_hit_limit,
        )


# ---------------------------------------------------------------------------------------------
# Assembling the assertion
# ---------------------------------------------------------------------------------------------

def build_assertion_formula_for_atom_ids(abstraction: Monotone_Literal_Abstraction,
                                         asserted_atom_ids: Set[int],
                                         chi_bound_vars: FrozenSet[Var],
                                         project_bound_vars: bool = True) -> ASTp_Node:
    """
    Assemble `exists X. AND(asserted literals)`, where `X` are the binders of `chi` the asserted
    literals mention.

    The hoisted prefix is retained rather than dropped, even though leaving the former bound variables
    free would decide the formula just as well (emptiness of the final intersection is unaffected by
    projecting variables that do not occur in `phi`). It is what makes the assertion match the shapes
    the evaluator's specialized constructions require, each of which pattern-matches an
    `AST_Quantifier` over an `AND`: `amaya.parse.try_lazy_construct_conjunction`,
    `amaya.parse.try_construct_bounded_congruence` and
    `amaya.parse.select_children_to_lazily_evaluate`. `project_bound_vars=False` drops it.
    """
    asserted_literals = tuple(abstraction.manager.literal_by_atom_id[atom_id]
                              for atom_id in sorted(asserted_atom_ids))

    if not asserted_literals:
        return BoolLiteral(True)

    if len(asserted_literals) == 1:
        conjunction: ASTp_Node = asserted_literals[0]
    else:
        conjunction = AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND,
                                     children=asserted_literals)
    fill_referenced_vars(conjunction)

    if not project_bound_vars:
        return conjunction

    referenced_vars = _referenced_vars_of_node(conjunction)
    prefix_vars = tuple(sorted(var for var in chi_bound_vars if var in referenced_vars))
    if not prefix_vars:
        return conjunction

    assertion = AST_Quantifier(referenced_vars=tuple(), bound_vars=prefix_vars, child=conjunction)
    fill_referenced_vars(assertion)
    return assertion


def _referenced_vars_of_node(node: ASTp_Node) -> FrozenSet[Var]:
    match node:
        case Relation() | Congruence():
            return frozenset(node.vars)
        case Var():
            return frozenset((node,))
        case BoolLiteral():
            return frozenset()
        case _:
            return frozenset(node.referenced_vars)


# ---------------------------------------------------------------------------------------------
# Optimizing the assertion
# ---------------------------------------------------------------------------------------------

def optimize_assertion_formula(assertion: ASTp_Node,
                               ctx: EvaluationContext,
                               assertion_optimizer_mode: str) -> ASTp_Node:
    """
    Run the fixpoint pipeline over a single assertion, with the registry filtered according to
    `assertion_optimizer_mode`.

    `ASSERTION_OPTIMIZER_MODE_RESTRICTED` filters to
    `ASSERTION_OPTIMIZER_SOLUTION_SET_PRESERVING_PASSES`, which is empty, so it currently returns the
    assertion unchanged. `ASSERTION_OPTIMIZER_MODE_FULL` runs the whole enabled registry and is known
    to be unsound here - see `ASSERTION_OPTIMIZER_SOLUTION_SET_PRESERVING_PASSES`.

    Note this ignores `solver_config.optimization_pipeline.enabled`: the legacy hand-unrolled sequence
    (`amaya.parse._optimize_formula_structure_legacy`) is not factored to accept a registry, so there
    is nothing to filter there.
    """
    if assertion_optimizer_mode == ASSERTION_OPTIMIZER_MODE_NONE:
        return assertion

    if assertion_optimizer_mode not in (ASSERTION_OPTIMIZER_MODE_RESTRICTED, ASSERTION_OPTIMIZER_MODE_FULL):
        raise ValueError(f'Unknown assertion optimizer mode: {assertion_optimizer_mode}')

    registry = build_registry(solver_config)
    if assertion_optimizer_mode == ASSERTION_OPTIMIZER_MODE_RESTRICTED:
        registry = [descriptor for descriptor in registry
                    if descriptor.name in ASSERTION_OPTIMIZER_SOLUTION_SET_PRESERVING_PASSES]

    if not registry:
        return assertion

    pipeline = Optimization_Pipeline(
        registry,
        ctx.var_table,
        max_pass_applications=solver_config.optimization_pipeline.max_pass_applications,
        max_wall_time_seconds=solver_config.optimization_pipeline.max_wall_time_seconds,
    )
    return pipeline.run(assertion)


# ---------------------------------------------------------------------------------------------
# Building the automaton for an assertion
# ---------------------------------------------------------------------------------------------

def clone_automaton(nfa: NFA) -> Optional[NFA]:
    """
    An independent copy of `nfa`, or None if the backend cannot make one.

    Every automaton entering or leaving a cache must be cloned: projection and padding closure modify
    their operand in place (`amaya.automatons.NFA.do_projection` reassigns and then mutates the
    operand's transition function; `amaya.mtbdd_automatons.MTBDD_NFA.do_projection` mutates and returns
    `self`), so handing a cached automaton to one of them would corrupt the cache. Intersection and
    union do allocate a new automaton and leave their operands alone.

    Only the MTBDD backend can clone: `renamed_copy` is installed onto `MTBDD_NFA` by
    `amaya.cse_cache`, and the native `NFA` has no equivalent.
    """
    renamed_copy = getattr(nfa, 'renamed_copy', None)
    if renamed_copy is None:
        return None
    return renamed_copy({})


def intersect_automata(first_nfa: NFA, second_nfa: NFA, ctx: EvaluationContext) -> NFA:
    """
    Language intersection of two automata, handling operands that use no variables.

    `amaya.automatons.NFA.intersection` asserts that its result uses at least one variable, so it
    cannot be handed two trackless operands - which is exactly what this loop produces whenever the
    general part is empty (a trivially accepting automaton) and an assertion had every one of its
    variables projected away. No product construction is needed in that case anyway: an automaton over
    no tracks accepts either every word or none, so intersecting with it is either the identity on the
    other operand or the empty language.

    The identity case returns the other operand itself rather than a copy. Callers must therefore treat
    the result as they would any cached automaton and not modify it in place (see `clone_automaton`).
    """
    for constant_operand, other_operand in ((first_nfa, second_nfa), (second_nfa, first_nfa)):
        if constant_operand.used_variables:
            continue
        if constant_operand.find_model() is not None:
            return other_operand
        automaton_cls = ctx.get_automaton_class_for_current_backend()
        return automaton_cls.trivial_nonaccepting(ctx.get_alphabet())

    ctx.stats_operation_starts(ParsingOperation.NFA_INTERSECT, first_nfa, second_nfa)
    intersection_nfa = first_nfa.intersection(second_nfa)
    ctx.stats_operation_ends(operand1=first_nfa, operand2=second_nfa, output=intersection_nfa)
    return intersection_nfa


@dataclass
class Assertion_Automaton_Builder:
    """
    Builds the automaton for an assertion, caching the automata of the *prefixes* of its conjunction.

    Consecutive assertions differ in a few literals, so their conjunctions share sub-conjunctions.
    Conjuncts are ordered canonically by structural id, so the set of prefixes depends only on the
    conjunct set and not on the order the SAT solver produced them.

    An assertion set never recurs exactly - each one is blocked as it is refuted, so no later set
    contains an earlier one - which is why there is no cache keyed on the whole set: it could never
    hit. Prefixes do recur.
    """

    max_prefix_cache_entries: int = 4096
    structural_id_table: Structural_Id_Table = field(default_factory=Structural_Id_Table)
    intersection_prefix_cache: 'OrderedDict[Tuple[int, ...], NFA]' = field(default_factory=OrderedDict)

    prefix_cache_hits: int = 0
    prefix_cache_misses: int = 0
    prefix_cache_evictions: int = 0
    longest_prefix_hit_length: int = 0

    def build_automaton_for_assertion(self, assertion: ASTp_Node, ctx: EvaluationContext) -> NFA:
        decomposition = self._decompose_assertion_into_conjunction(assertion)

        if decomposition is None or not self._is_prefix_caching_applicable(assertion, decomposition):
            return parse.run_evaluation_procedure(assertion, ctx)

        conjuncts, bound_vars = decomposition
        nfa = self._build_conjunction_automaton(conjuncts, ctx)
        if bound_vars:
            nfa = self._project_bound_vars_away(nfa, bound_vars, ctx)
        return nfa

    def _decompose_assertion_into_conjunction(
            self, assertion: ASTp_Node) -> Optional[Tuple[Tuple[ASTp_Node, ...], Tuple[Var, ...]]]:
        """ `(conjuncts, bound_vars)` for the shapes the prefix cache handles, None for anything else. """
        if isinstance(assertion, AST_Quantifier):
            child = assertion.child
            if isinstance(child, AST_Connective) and child.type == Connective_Type.AND:
                return child.children, assertion.bound_vars
            return None

        if isinstance(assertion, AST_Connective) and assertion.type == Connective_Type.AND:
            return assertion.children, tuple()

        return None

    def _is_prefix_caching_applicable(self,
                                      assertion: ASTp_Node,
                                      decomposition: Tuple[Tuple[ASTp_Node, ...], Tuple[Var, ...]]) -> bool:
        """
        Whether to build this assertion incrementally instead of handing it to the ordinary evaluator.

        Three situations rule it out. Without a clonable automaton the cache cannot be maintained at all
        (see `clone_automaton`). The other two are constructions of the ordinary evaluator that build a
        whole conjunction in one step, which the incremental intersection would replace with one
        intersection per conjunct:

        | Construction | Source | Condition |
        |---|---|---|
        | Lazy conjunction construction | `amaya.parse.try_lazy_construct_conjunction`, `amaya.parse.select_children_to_lazily_evaluate` | `do_lazy_evaluation` and at least two atoms among the conjuncts |
        | Bounded congruence construction | `amaya.parse.try_construct_bounded_congruence` | integers, MTBDD, `use_bounded_congruence_construction`, and a bound variable the construction can eliminate |

        The lazy-construction condition is the weaker of the two available tests: it does not replicate
        `select_children_to_lazily_evaluate`'s density threshold, so it declines the prefix cache on some
        conjunctions the evaluator would not have handled lazily anyway. Declining costs cache hits, not
        correctness.
        """
        if self.max_prefix_cache_entries <= 0:
            return False
        if solver_config.backend_type != BackendType.MTBDD:
            return False

        conjuncts, _ = decomposition
        atom_conjunct_count = sum(1 for conjunct in conjuncts if isinstance(conjunct, (Relation, Congruence)))
        if solver_config.optimizations.do_lazy_evaluation and atom_conjunct_count >= 2:
            return False

        bounded_congruence_construction_would_fire = (
            solver_config.solution_domain == SolutionDomain.INTEGERS
            and solver_config.optimizations.use_bounded_congruence_construction
            and isinstance(assertion, AST_Quantifier)
            and parse.find_var_eliminable_by_bounded_congruence_construction(assertion) is not None
        )
        return not bounded_congruence_construction_would_fire

    def _build_conjunction_automaton(self, conjuncts: Tuple[ASTp_Node, ...], ctx: EvaluationContext) -> NFA:
        """
        Intersect the conjuncts one at a time, storing the automaton of every prefix.

        Mirrors two things `amaya.parse.evaluate_binary_conjunction_expr` does around its own reduction
        loop: the configured minimization is applied after every intersection (never to a single
        conjunct's own automaton, which the evaluator does not minimize either), and the loop stops as
        soon as the running automaton has no final states, since no further conjunct can restore them.
        """
        ordered_conjuncts, ordered_conjunct_ids = self._order_conjuncts_canonically(conjuncts)

        nfa, first_conjunct_to_build = self._find_longest_cached_prefix(ordered_conjunct_ids)

        for conjunct_index in range(first_conjunct_to_build, len(ordered_conjuncts)):
            if nfa is not None and not nfa.final_states:
                return nfa

            conjunct_nfa = parse.run_evaluation_procedure(ordered_conjuncts[conjunct_index], ctx)

            if nfa is None:
                nfa = conjunct_nfa
            else:
                nfa = intersect_automata(nfa, conjunct_nfa, ctx)
                prefix_node = AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND,
                                             children=tuple(ordered_conjuncts[:conjunct_index + 1]))
                nfa = parse.minimize_automaton_if_configured(prefix_node, nfa, ctx)

            self._store_prefix(ordered_conjunct_ids[:conjunct_index + 1], nfa)

        assert nfa is not None, 'A conjunction with no conjuncts should not have been decomposed'
        return nfa

    def _order_conjuncts_canonically(self,
                                     conjuncts: Tuple[ASTp_Node, ...]) -> Tuple[List[ASTp_Node], Tuple[int, ...]]:
        """
        Sort the conjuncts by structural id, so that two assertions sharing a set of conjuncts also
        share the prefixes built out of them.

        This competes with `amaya.parse.reorder_conjunction_to_derive_conflict_more_quickly`, which
        orders the conjuncts of an `AND` by estimated automaton size in order to reach an empty
        automaton sooner. Both orders are correct; which performs fewer intersection steps is not
        measured.
        """
        conjunct_ids = [compute_structural_id(conjunct, self.structural_id_table)[0] for conjunct in conjuncts]
        order = sorted(range(len(conjuncts)), key=lambda index: conjunct_ids[index])
        return ([conjuncts[index] for index in order], tuple(conjunct_ids[index] for index in order))

    def _find_longest_cached_prefix(self,
                                    ordered_conjunct_ids: Tuple[int, ...]) -> Tuple[Optional[NFA], int]:
        for prefix_length in range(len(ordered_conjunct_ids), 0, -1):
            cached_nfa = self.intersection_prefix_cache.get(ordered_conjunct_ids[:prefix_length])
            if cached_nfa is None:
                continue

            cloned_nfa = clone_automaton(cached_nfa)
            if cloned_nfa is None:
                break

            self.intersection_prefix_cache.move_to_end(ordered_conjunct_ids[:prefix_length])
            self.prefix_cache_hits += 1
            self.longest_prefix_hit_length = max(self.longest_prefix_hit_length, prefix_length)
            return cloned_nfa, prefix_length

        self.prefix_cache_misses += 1
        return None, 0

    def _store_prefix(self, prefix_key: Tuple[int, ...], nfa: NFA):
        cloned_nfa = clone_automaton(nfa)
        if cloned_nfa is None:
            return

        self.intersection_prefix_cache[prefix_key] = cloned_nfa
        self.intersection_prefix_cache.move_to_end(prefix_key)
        while len(self.intersection_prefix_cache) > self.max_prefix_cache_entries:
            self.intersection_prefix_cache.popitem(last=False)
            self.prefix_cache_evictions += 1

    def _project_bound_vars_away(self, nfa: NFA, bound_vars: Tuple[Var, ...], ctx: EvaluationContext) -> NFA:
        """
        Project the assertion's prefix away, mirroring `amaya.parse.evaluate_exists_expr`: the padding
        closure is performed only after the last variable has been projected away.

        Variables the automaton does not use are skipped - the automaton the prefix cache returns may
        have lost a track to a constant-folding construction, and both backends' `do_projection` assume
        the variable is used.
        """
        vars_to_project = [var for var in bound_vars if var in nfa.used_variables]
        if not vars_to_project:
            return nfa

        last_var_to_project = vars_to_project[-1]
        for var in vars_to_project:
            ctx.stats_operation_starts(ParsingOperation.NFA_PROJECTION, nfa, None)
            projection_result = nfa.do_projection(var, skip_pad_closure=(var != last_var_to_project))
            assert projection_result is not None
            ctx.stats_operation_ends(operand1=nfa, operand2=None, output=projection_result)
            nfa = projection_result

        return nfa


# ---------------------------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------------------------

@dataclass
class Dpllt_Run_Statistics:
    """ Per-run counters; logged when `DpllTAutomataConfig.report` is set. """

    phi_conjunct_count: int = 0
    chi_conjunct_count: int = 0
    abstracted_literal_count: int = 0
    iteration_count: int = 0
    theory_calls: int = 0
    bounds_refutations: int = 0
    bounds_refutation_core_literals: int = 0
    asserted_literals_before_minimization: int = 0
    asserted_literals_after_minimization: int = 0
    optimizer_invocations: int = 0
    phi_automaton_states: int = 0
    max_assertion_automaton_states: int = 0
    max_intersection_states: int = 0
    prefix_cache_hits: int = 0
    prefix_cache_misses: int = 0
    prefix_cache_evictions: int = 0
    longest_prefix_hit_length: int = 0

    def absorb_builder_counters(self, builder: Assertion_Automaton_Builder):
        self.prefix_cache_hits = builder.prefix_cache_hits
        self.prefix_cache_misses = builder.prefix_cache_misses
        self.prefix_cache_evictions = builder.prefix_cache_evictions
        self.longest_prefix_hit_length = builder.longest_prefix_hit_length


def _make_sat_evaluation_result(ctx: EvaluationContext, nfa: Optional[NFA], binary_model) -> Evaluation_Result:
    """
    Assemble the model reported for a satisfiable formula.

    `solutions_nfa` is deliberately left None: the automaton this loop ends up with describes the
    solutions of `phi AND (the asserted conjunction)`, which is a subset of the solutions of the whole
    formula, and the field's consumers (`run-amaya.py`, the visualization paths) read it as the
    solution space of the input.
    """
    formula_params = tuple(var for var, var_info in ctx.var_table.items() if var_info.is_formula_param)

    if binary_model is None or nfa is None:
        model: Dict[Var, int] = {var: 0 for var in formula_params}
    else:
        model = convert_binary_model_into_decadic(binary_model, nfa.used_variables, formula_params)

    return Evaluation_Result(run_stats=ctx.stats, solutions_nfa=None, model=model, var_table=ctx.var_table)


def _make_unsat_evaluation_result(ctx: EvaluationContext) -> Evaluation_Result:
    return Evaluation_Result(run_stats=ctx.stats, solutions_nfa=None, model=None, var_table=ctx.var_table)


def _report_statistics(statistics: Dpllt_Run_Statistics):
    logger.info('DPLL(T) run statistics: %s', statistics)


def solve_with_dpllt_over_automata(root: ASTp_Node,
                                   ctx: EvaluationContext,
                                   config: Optional[DpllTAutomataConfig] = None) -> Evaluation_Result:
    """
    Decide `root` by enumerating minimal implicants of the Boolean abstraction of its
    positive-existential part and handing each one, conjoined with the general part, to the automata
    engine. See the module docstring for the correctness argument.

    Falls through to `amaya.parse.evaluate_prepared_formula_with_automata` when the split finds nothing
    to work with - no positive-existential conjunct, or one without a disjunction, in which case the
    abstraction has a single implicant and the loop would do the ordinary evaluator's work twice.
    """
    if config is None:
        config = solver_config.dpllt_automata

    normalized_root = normalize_formula_for_splitting(root)
    split = split_formula_into_phi_and_chi(normalized_root)

    if config.show_positive_existential_part:
        display_positive_existential_part_and_exit(split)

    if config.count_abstraction_models:
        display_abstraction_model_counts_and_exit(split, ctx.var_table,
                                                  config.abstraction_model_enumeration_limit)

    # The fall-through evaluates `root`, not `normalized_root`: the normalization is a precondition of
    # the split, not an optimization, and an input this strategy does not apply to should be evaluated
    # exactly as the default driver would evaluate it.
    if not split.chi_conjuncts:
        logger.info('DPLL(T): no positive-existential conjunct in the formula, evaluating it directly.')
        return parse.evaluate_prepared_formula_with_automata(root, ctx)

    if not any(does_subformula_contain_disjunction(conjunct) for conjunct in split.chi_conjuncts):
        logger.info('DPLL(T): the positive-existential part contains no disjunction, so its abstraction has a '
                    'single implicant; evaluating the formula directly.')
        return parse.evaluate_prepared_formula_with_automata(root, ctx)

    statistics = Dpllt_Run_Statistics(phi_conjunct_count=len(split.phi_conjuncts),
                                      chi_conjunct_count=len(split.chi_conjuncts))

    chi_conjuncts = tuple(freshen_bound_variables_in_subformula(conjunct, ctx.var_table)
                          for conjunct in split.chi_conjuncts)
    chi_bound_vars: FrozenSet[Var] = frozenset()
    for conjunct in chi_conjuncts:
        chi_bound_vars |= collect_bound_vars_of_subformula(conjunct)

    # The alphabet must be rebuilt before *any* automaton is constructed: the freshened variables are
    # new tracks, and the MTBDD backend asserts that the operands of a union agree on their nominal
    # alphabet (see `amaya.cse_cache._renamed_copy`).
    ctx.alphabet = LSBF_Alphabet.from_vars(ctx.var_table.keys())

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula(chi_conjuncts)
        statistics.abstracted_literal_count = abstraction.atom_count

        logger.info('DPLL(T): %d general conjuncts, %d positive-existential conjuncts, %d abstracted literals.',
                    len(split.phi_conjuncts), len(chi_conjuncts), abstraction.atom_count)

        # The positive-existential part is never evaluated as it stands - the assertions logged per
        # iteration are what reaches the automata engine - but it is what those assertions are drawn
        # from, so it is logged once, after the binders have been renamed apart.
        for conjunct_index, chi_conjunct in enumerate(chi_conjuncts):
            logger.debug('DPLL(T): positive-existential conjunct %d of %d:\n%s',
                         conjunct_index + 1, len(chi_conjuncts), format_formula(chi_conjunct))

        nfa_for_phi = _build_automaton_for_phi(split.phi_conjuncts, ctx)
        statistics.phi_automaton_states = len(nfa_for_phi.states)

        builder = Assertion_Automaton_Builder(max_prefix_cache_entries=config.prefix_cache_max_entries)

        try:
            if abstraction.atom_count == 0:
                return _solve_with_constant_abstraction(abstraction, nfa_for_phi, ctx, statistics)

            return _enumerate_implicants(abstraction, chi_bound_vars, nfa_for_phi, builder, ctx, config,
                                         statistics)
        finally:
            statistics.absorb_builder_counters(builder)
            if config.report:
                _report_statistics(statistics)


def _build_automaton_for_phi(phi_conjuncts: Tuple[ASTp_Node, ...], ctx: EvaluationContext) -> NFA:
    """ The automaton for the general part, built once and used as an intersection operand thereafter. """
    if not phi_conjuncts:
        logger.info('DPLL(T): the general part is empty, its automaton accepts every word.')
        automaton_cls = ctx.get_automaton_class_for_current_backend()
        return automaton_cls.trivial_accepting(ctx.get_alphabet())

    phi = make_conjunction_of_conjuncts(phi_conjuncts)

    logger.info('DPLL(T): evaluating the general part:\n%s', format_formula(phi))
    return parse.run_evaluation_procedure(phi, ctx)


def _solve_with_constant_abstraction(abstraction: Monotone_Literal_Abstraction,
                                     nfa_for_phi: NFA,
                                     ctx: EvaluationContext,
                                     statistics: Dpllt_Run_Statistics) -> Evaluation_Result:
    """
    Decide the formula when the abstraction has no literals at all - `chi` is a Boolean constant, so
    the verdict is the one of `phi` alone (or UNSAT, if `chi` is `False`).
    """
    if not evaluate_monotone_skeleton(abstraction.skeleton, set()):
        logger.info('DPLL(T): the positive-existential part is constantly false.')
        return _make_unsat_evaluation_result(ctx)

    statistics.iteration_count = 1
    binary_model = nfa_for_phi.find_model()
    if binary_model is None:
        return _make_unsat_evaluation_result(ctx)
    return _make_sat_evaluation_result(ctx, nfa_for_phi, binary_model)


def _enumerate_implicants(abstraction: Monotone_Literal_Abstraction,
                          chi_bound_vars: FrozenSet[Var],
                          nfa_for_phi: NFA,
                          builder: Assertion_Automaton_Builder,
                          ctx: EvaluationContext,
                          config: DpllTAutomataConfig,
                          statistics: Dpllt_Run_Statistics) -> Evaluation_Result:
    with pysat.solvers.Solver(bootstrap_with=abstraction.sat_formula) as sat_solver:
        while sat_solver.solve():
            statistics.iteration_count += 1

            asserted_atom_ids = abstraction.collect_asserted_atom_ids_from_sat_model(sat_solver.get_model())
            statistics.asserted_literals_before_minimization += len(asserted_atom_ids)

            # The bounds refutation runs on the *unminimized* set, and only there. Minimization can
            # only remove literals, and removing a bound cannot create a clash, so a set the check
            # accepts has no clashing pair in any of its subsets either - running it again after
            # minimization could not find anything. Checking first also skips the minimization and the
            # theory call outright on a hit.
            bounds_refutation = (find_bounds_refutation(asserted_atom_ids, abstraction)
                                 if config.use_bounds_refutation else None)

            if bounds_refutation is not None:
                statistics.bounds_refutations += 1
                statistics.bounds_refutation_core_literals += len(bounds_refutation.atom_ids)
                logger.debug('DPLL(T): iteration %d, refuted by bounds without a theory call: %s.',
                             statistics.iteration_count, bounds_refutation.reason)
                atom_ids_to_block = set(bounds_refutation.atom_ids)
            else:
                if config.minimize_implicants:
                    asserted_atom_ids = minimize_asserted_atom_ids(abstraction, asserted_atom_ids)
                elif not evaluate_monotone_skeleton(abstraction.skeleton, asserted_atom_ids):
                    asserted_atom_ids = set(abstraction.manager.literal_by_atom_id)
                statistics.asserted_literals_after_minimization += len(asserted_atom_ids)

                logger.debug('DPLL(T): iteration %d, asserting %d literals.',
                             statistics.iteration_count, len(asserted_atom_ids))

                statistics.theory_calls += 1
                model_of_iteration = _decide_asserted_literals(abstraction, asserted_atom_ids,
                                                               chi_bound_vars, nfa_for_phi, builder, ctx,
                                                               config, statistics)
                if model_of_iteration is not None:
                    return model_of_iteration

                atom_ids_to_block = asserted_atom_ids

            blocking_clause = abstraction.make_blocking_clause(atom_ids_to_block)
            if not blocking_clause:
                # No literal was asserted, so the abstraction is satisfied by asserting nothing and the
                # refuted assertion is the one every model of the abstraction produces. Adding the empty
                # clause would say the same thing; some solver backends refuse it, so say it directly.
                # A bounds refutation always names at least one literal, so it never reaches this.
                break
            sat_solver.add_clause(blocking_clause)

    logger.info('DPLL(T): no literal set left to try after %d iterations, formula is UNSAT.',
                statistics.iteration_count)
    return _make_unsat_evaluation_result(ctx)


def _decide_asserted_literals(abstraction: Monotone_Literal_Abstraction,
                              asserted_atom_ids: Set[int],
                              chi_bound_vars: FrozenSet[Var],
                              nfa_for_phi: NFA,
                              builder: Assertion_Automaton_Builder,
                              ctx: EvaluationContext,
                              config: DpllTAutomataConfig,
                              statistics: Dpllt_Run_Statistics) -> Optional[Evaluation_Result]:
    """
    Evaluate one asserted literal set against the general part; return the SAT result, or None when the
    intersection is empty and the caller should block the set and continue.
    """
    assertion = build_assertion_formula_for_atom_ids(abstraction, asserted_atom_ids, chi_bound_vars,
                                                     project_bound_vars=config.project_bound_vars)

    if _may_invoke_assertion_optimizer(config, statistics):
        statistics.optimizer_invocations += 1
        optimized_assertion = optimize_assertion_formula(assertion, ctx, config.assertion_optimizer)
        if optimized_assertion is not assertion:
            logger.debug('DPLL(T): iteration %d, assertion before optimization:\n%s',
                         statistics.iteration_count, format_formula(assertion))
        assertion = optimized_assertion

    logger.info('DPLL(T): iteration %d, evaluating the assertion:\n%s',
                statistics.iteration_count, format_formula(assertion))

    # `ctx.enc_table` memoizes De Bruijn encodings keyed by `id(node)`; every iteration builds a fresh
    # assertion tree that dies at the end of the iteration, so a stale entry could be matched by a new
    # node allocated at a recycled address. The content-keyed automaton cache is what we keep.
    if getattr(ctx, 'enc_table', None) is not None:
        ctx.enc_table = {}

    nfa_for_assertion = builder.build_automaton_for_assertion(assertion, ctx)
    statistics.max_assertion_automaton_states = max(statistics.max_assertion_automaton_states,
                                                    len(nfa_for_assertion.states))

    nfa = intersect_automata(nfa_for_phi, nfa_for_assertion, ctx)
    statistics.max_intersection_states = max(statistics.max_intersection_states, len(nfa.states))

    binary_model = nfa.find_model()
    if binary_model is None:  # An empty model is a *satisfiable* one - not falsy-testable
        return None

    return _make_sat_evaluation_result(ctx, nfa, binary_model)


def _may_invoke_assertion_optimizer(config: DpllTAutomataConfig, statistics: Dpllt_Run_Statistics) -> bool:
    if config.assertion_optimizer == ASSERTION_OPTIMIZER_MODE_NONE:
        return False
    if config.max_optimizer_invocations is None:
        return True
    return statistics.optimizer_invocations < config.max_optimizer_invocations


# ---------------------------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------------------------

def evaluate_prepared_formula_with_dpllt_automata(astp: ASTp_Node,
                                                  ctx: EvaluationContext,
                                                  config: Optional[DpllTAutomataConfig] = None) -> Evaluation_Result:
    """
    Evaluation strategy plugging `solve_with_dpllt_over_automata` into
    `amaya.parse.perform_whole_evaluation_on_source_text`.

    The whole loop runs inside `cse_enabled()`, which patches the module-global
    `parse.run_evaluation_procedure` so that *recursive* evaluations inside `parse.py` are cached too;
    calling the cache-aware entry point directly would only ever cache the roots this module hands it,
    which differ every iteration.
    """
    if solver_config.backend_type != BackendType.MTBDD:
        logger.warning('DPLL(T) solving is running on the %s backend, where neither the conjunction-prefix '
                       'cache nor the subformula cache is available (both need an automaton clone, which '
                       'only the MTBDD backend provides). Every iteration will rebuild its assertion from '
                       'scratch; pass --backend MTBDD for the caches to be in play.',
                       solver_config.backend_type.name)

    with cse_enabled():
        return solve_with_dpllt_over_automata(astp, ctx, config=config)


def perform_whole_evaluation_on_source_text_with_dpllt_automata(source_text: str,
                                                                emit_introspect=None) -> Optional[Evaluation_Result]:
    """ Convenience wrapper: `perform_whole_evaluation_on_source_text` driven by the DPLL(T) loop. """
    return parse.perform_whole_evaluation_on_source_text(
        source_text,
        emit_introspect=emit_introspect,
        evaluate_prepared_formula=evaluate_prepared_formula_with_dpllt_automata,
    )
