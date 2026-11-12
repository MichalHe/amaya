"""
Fourier-Motzkin elimination of existentially quantified integer variables whose every occurrence
has coefficient +1 or -1 (unit-coefficient Fourier-Motzkin, UCFM).

Let `v` be an existentially quantified integer variable and let the body of its quantifier be a
conjunction in which every conjunct mentioning `v` is a linear atom with coefficient +1 or -1 at `v`:

    exists v. (and  L_1 <= v ... L_p <= v   v <= U_1 ... v <= U_q   rest)       (v not in rest)

Every `L_i` and `U_j` is a linear term with integer coefficients, so it takes integer values, and an
integer `v` with `max_i L_i <= v <= min_j U_j` exists if and only if `L_i <= U_j` holds for every pair
`(i, j)`. The rewrite

    exists v. (...)   --->   (and  L_i <= U_j for every (i, j)   rest)

is therefore an equivalence over the integers. If `p = 0` or `q = 0`, no pair exists and every conjunct
mentioning `v` is removed. An equation `v + T = k` contributes both `v <= k - T` and `k - T <= v`.

Occurrence shapes that abort the rewrite for `v` (the formula is left unchanged for `v`):
    - a coefficient of `v` other than +1, -1;
    - `v` in a congruence, in a negated equation, or in a nested connective, negation or quantifier;
    - more than `|L| + |U|` atoms produced, i.e. `|L| * |U| > |L| + |U|` (see `_produces_no_more_atoms`).

When the solution domain is the natural numbers, `v >= 0` is added to the lower bounds of `v`.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from amaya.preprocessing.conditional_equality_resolution import (
    _extract_referenced_vars,
    _make_and,
    _referenced_vars_of_children,
)
from amaya.preprocessing.eval import VarInfo
from amaya.preprocessing.inner_quantifier_squeeze_elimination import (
    _fold_relation,
    _linear_combo,
    _references_squeezed_var as _references_var,
)
from amaya.relations_structures import (
    ASTp_Node,
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
)


@dataclass
class Unit_Coefficient_Bound:
    """
    One bound on the eliminated variable `v`, stored as the terms and right-hand side of the atom
    `coef_of_v * v + sum(terms) <= rhs` with `v` removed. `coef_of_v` is -1 for a lower bound and +1
    for an upper bound.
    """
    terms: Dict[Var, int]
    rhs: int


@dataclass
class Bounds_On_Eliminated_Var:
    lower_bounds: List[Unit_Coefficient_Bound] = field(default_factory=list)
    upper_bounds: List[Unit_Coefficient_Bound] = field(default_factory=list)


def _terms_without_var(relation: Relation, eliminated_var: Var) -> Dict[Var, int]:
    return {var: coef for var, coef in zip(relation.vars, relation.coefs) if var != eliminated_var}


def _coefficient_of_var(relation: Relation, eliminated_var: Var) -> int:
    if eliminated_var not in relation.vars:
        return 0
    return relation.coefs[relation.vars.index(eliminated_var)]


def _classify_conjunct_into_bounds(conjunct: ASTp_Node, eliminated_var: Var, bounds: Bounds_On_Eliminated_Var) -> bool:
    """
    Add the bounds on `eliminated_var` expressed by `conjunct` to `bounds`. Returns False if the shape of
    `conjunct` is not admissible (see the module docstring), in which case `bounds` must be discarded.
    """
    if not isinstance(conjunct, Relation):
        return False

    coef_of_var = _coefficient_of_var(conjunct, eliminated_var)
    if abs(coef_of_var) != 1:
        return False

    terms = _terms_without_var(conjunct, eliminated_var)
    rhs = conjunct.rhs

    if conjunct.predicate_symbol == '<=':
        bound = Unit_Coefficient_Bound(terms=terms, rhs=rhs)
        if coef_of_var == 1:
            bounds.upper_bounds.append(bound)   # v + T <= k
        else:
            bounds.lower_bounds.append(bound)   # -v + T <= k
        return True

    if conjunct.predicate_symbol == '=':
        # c*v + T = k  <=>  (v + c*T <= c*k)  and  (-v - c*T <= -c*k),  for c in {+1, -1}
        terms_with_v_coef_one = {var: coef_of_var * coef for var, coef in terms.items()}
        bounds.upper_bounds.append(Unit_Coefficient_Bound(terms=terms_with_v_coef_one, rhs=coef_of_var * rhs))
        bounds.lower_bounds.append(Unit_Coefficient_Bound(terms={var: -coef for var, coef in terms_with_v_coef_one.items()},
                                                          rhs=-coef_of_var * rhs))
        return True

    return False


def _produces_no_more_atoms(bounds: Bounds_On_Eliminated_Var) -> bool:
    """
    Fourier-Motzkin replaces `|L| + |U|` atoms by `|L| * |U|` atoms. The rewrite is restricted to the
    cases in which the number of atoms does not increase.
    """
    lower_count = len(bounds.lower_bounds)
    upper_count = len(bounds.upper_bounds)
    return lower_count * upper_count <= lower_count + upper_count


def _combine_lower_and_upper_bound(lower_bound: Unit_Coefficient_Bound, upper_bound: Unit_Coefficient_Bound) -> ASTp_Node:
    """
    (-v + T_lower <= k_lower) + (v + T_upper <= k_upper)  =  (T_lower + T_upper <= k_lower + k_upper)
    """
    vars_, coefs = _linear_combo(lower_bound.terms, 1, upper_bound.terms, 1)
    combined = Relation(vars=vars_, coefs=coefs, rhs=lower_bound.rhs + upper_bound.rhs, predicate_symbol='<=')
    return _fold_relation(combined)


def _try_eliminate_var_by_fourier_motzkin(eliminated_var: Var, body: ASTp_Node, quantified_vars_are_nonnegative: bool) -> Optional[ASTp_Node]:
    """
    Returns the body with `eliminated_var` eliminated, or None if some occurrence of `eliminated_var` is
    not admissible or the rewrite would increase the number of atoms.
    """
    if isinstance(body, AST_Connective) and body.type == Connective_Type.AND:
        conjuncts: Tuple[ASTp_Node, ...] = body.children
    else:
        conjuncts = (body,)

    bounds = Bounds_On_Eliminated_Var()
    if quantified_vars_are_nonnegative:
        bounds.lower_bounds.append(Unit_Coefficient_Bound(terms={}, rhs=0))  # -v <= 0

    retained_conjuncts: List[ASTp_Node] = []
    for conjunct in conjuncts:
        if not _references_var(conjunct, eliminated_var):
            retained_conjuncts.append(conjunct)
            continue
        if not _classify_conjunct_into_bounds(conjunct, eliminated_var, bounds):
            return None

    if not _produces_no_more_atoms(bounds):
        return None

    for lower_bound in bounds.lower_bounds:
        for upper_bound in bounds.upper_bounds:
            retained_conjuncts.append(_combine_lower_and_upper_bound(lower_bound, upper_bound))

    return _make_and(retained_conjuncts)


def _eliminate_vars_of_quantifier(bound_vars: Tuple[Var, ...], body: ASTp_Node, var_table: Dict[Var, VarInfo],
                                  quantified_vars_are_nonnegative: bool) -> Tuple[ASTp_Node, Tuple[Var, ...]]:
    """
    Eliminates bound variables until none of the remaining ones is admissible: eliminating one variable
    can change the coefficients of another (e.g. `-v + w <= 0` and `v - w + u <= 0` combine into `u <= 0`).
    """
    remaining_bound_vars = list(bound_vars)
    current_body = body

    made_progress = True
    while made_progress and not isinstance(current_body, BoolLiteral):
        made_progress = False
        for var in list(remaining_bound_vars):
            if var_table[var].type != VariableType.INT:
                continue

            rewritten_body = _try_eliminate_var_by_fourier_motzkin(var, current_body, quantified_vars_are_nonnegative)
            if rewritten_body is None:
                continue

            current_body = rewritten_body
            remaining_bound_vars.remove(var)
            made_progress = True
            if isinstance(current_body, BoolLiteral):
                break

    return current_body, tuple(remaining_bound_vars)


def eliminate_unit_coefficient_vars_by_fourier_motzkin(root: ASTp_Node, var_table: Dict[Var, VarInfo],
                                                       quantified_vars_are_nonnegative: bool = False) -> ASTp_Node:
    """
    Bottom-up pass applying unit-coefficient Fourier-Motzkin elimination to every existential quantifier.
    See the module docstring. `quantified_vars_are_nonnegative` is True when the solution domain is the
    natural numbers.
    """
    match root:
        case Relation() | Congruence() | BoolLiteral() | Var():
            return root

        case AST_Negation():
            new_child = eliminate_unit_coefficient_vars_by_fourier_motzkin(root.child, var_table, quantified_vars_are_nonnegative)
            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(not new_child.value)
            return AST_Negation(referenced_vars=_extract_referenced_vars(new_child), child=new_child)

        case AST_Connective():
            new_children = tuple(
                eliminate_unit_coefficient_vars_by_fourier_motzkin(child, var_table, quantified_vars_are_nonnegative)
                for child in root.children
            )
            # `replace_children` copies `root.referenced_vars`, which still lists the variables eliminated below.
            new_node = AST_Connective(referenced_vars=_referenced_vars_of_children(list(new_children)), type=root.type,
                                      children=new_children, variable_bounds=root.variable_bounds)

            new_node = new_node.simplify_on_anihilators()
            if not isinstance(new_node, AST_Connective):
                return new_node

            return new_node.remove_idempotent_children()

        case AST_Quantifier():
            new_child = eliminate_unit_coefficient_vars_by_fourier_motzkin(root.child, var_table, quantified_vars_are_nonnegative)
            new_child, remaining_bound_vars = _eliminate_vars_of_quantifier(root.bound_vars, new_child, var_table,
                                                                           quantified_vars_are_nonnegative)

            if not remaining_bound_vars or isinstance(new_child, BoolLiteral):
                return new_child

            return AST_Quantifier(
                referenced_vars=_extract_referenced_vars(new_child),
                bound_vars=remaining_bound_vars,
                child=new_child,
            )

        case _:
            raise ValueError(f'Unhandled node while eliminating unit-coefficient variables by Fourier-Motzkin: {root}')
