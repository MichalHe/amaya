"""
Inner Quantifier Squeeze Elimination (IQSE).

Eliminates an existentially quantified integer variable `squeezed_var` that is "squeezed"
between two linear bounds whose gap is exactly `squeeze_modulus - 1`, e.g.:

    exists (y)
       and
          10*y <= 9*x
          10*y >= 9*x - 9

forces `y = floor(9*x / 10)`, so `y` can be substituted out of every other conjunct that
mentions it and the quantifier dropped. See `docs/QSE.md` for the design and
`docs/QSE_IMPLEMENTATION_PLAN.md` for the representation-level restatement this module
implements (in particular §4, which this module follows section by section).

This module targets every `AST_Quantifier` node it visits (not only the innermost one - see
`docs/QSE_IMPLEMENTATION_PLAN.md` D1), and aborts the rewrite for a given bound variable as soon
as any occurrence of that variable does not conform to one of the admissible shapes in §4.3.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import IntEnum
from typing import Dict, List, Optional, Tuple

from amaya.preprocessing.conditional_equality_resolution import (
    _extract_referenced_vars,
    _make_and,
    _make_or,
)
from amaya.preprocessing.eval import VarInfo
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


class Residual_Bound_Kind(IntEnum):
    UPPER = 0x01        # y + T <= k
    LOWER = 0x02        # -y + T <= k
    EQUALITY = 0x03     # y + T = k (already normalized to coefficient +1, see `_classify_residual_conjunct`)
    DISEQUALITY = 0x04  # not (y + T = k), same normalization


@dataclass
class Squeeze_Match:
    """The result of matching a squeeze pair on `squeezed_var` (`docs/QSE_IMPLEMENTATION_PLAN.md` §4.2)."""
    squeeze_modulus: int
    upper_bound_terms: Dict[Var, int]
    upper_bound_constant: int
    upper_index: int = -1
    lower_index: int = -1


@dataclass
class Residual_Bound:
    """One admissible conjunct mentioning `squeezed_var`, classified per §4.3 and already
    normalized (for EQUALITY/DISEQUALITY) so that `squeezed_var`'s coefficient is +1."""
    kind: Residual_Bound_Kind
    terms: Dict[Var, int]
    rhs: int
    child_index: int


def _coefficient_of_squeezed_var(relation: Relation, squeezed_var: Var) -> int:
    if squeezed_var not in relation.vars:
        return 0
    return relation.coefs[relation.vars.index(squeezed_var)]


def _residual_terms(relation: Relation, squeezed_var: Var) -> Dict[Var, int]:
    return {var: coef for var, coef in zip(relation.vars, relation.coefs) if var != squeezed_var}


def _references_squeezed_var(node: ASTp_Node, squeezed_var: Var) -> bool:
    """
    Membership test for §4.3: a `Relation`/`Congruence` references `squeezed_var` only when its
    coefficient there is non-zero (a variable listed with coefficient 0 does not constrain it),
    while a compound child (`AST_Connective`, `AST_Negation`, `AST_Quantifier`) is tested via its
    maintained `referenced_vars` annotation - see `docs/QSE_IMPLEMENTATION_PLAN.md` §4.3.
    """
    if isinstance(node, (Relation, Congruence)):
        return squeezed_var in node.vars and node.coefs[node.vars.index(squeezed_var)] != 0
    if isinstance(node, Var):
        return node == squeezed_var
    if isinstance(node, BoolLiteral):
        return False
    return squeezed_var in node.referenced_vars


def _fold_relation(relation: Relation) -> ASTp_Node:
    """Ground atoms fold to a `BoolLiteral` so `_make_and`/`_make_or` can discharge them (§4.4)."""
    if relation.are_all_coefficients_zero():
        return BoolLiteral(relation.is_always_satisfied())
    return relation


def _linear_combo(terms_a: Dict[Var, int], coef_a: int, terms_b: Dict[Var, int], coef_b: int) -> Tuple[List[Var], List[int]]:
    """`coef_a * terms_a + coef_b * terms_b`, as sorted, zero-coefficient-free `(vars, coefs)` lists."""
    combined: Dict[Var, int] = {}
    for var, coef in terms_a.items():
        combined[var] = combined.get(var, 0) + coef_a * coef
    for var, coef in terms_b.items():
        combined[var] = combined.get(var, 0) + coef_b * coef

    sorted_terms = sorted((var, coef) for var, coef in combined.items() if coef != 0)
    return [var for var, _coef in sorted_terms], [coef for _var, coef in sorted_terms]


def _try_match_squeeze_pair(upper_candidate: Relation, lower_candidate: Relation, squeezed_var: Var) -> Optional[Squeeze_Match]:
    """§4.2 conditions 1-4. `upper_candidate`/`lower_candidate` are tried in this fixed role
    assignment; the caller tries both orderings of a candidate pair (§4.2 discussion of D1)."""
    coef_upper = _coefficient_of_squeezed_var(upper_candidate, squeezed_var)
    if coef_upper < 1:
        return None

    coef_lower = _coefficient_of_squeezed_var(lower_candidate, squeezed_var)
    if coef_lower != -coef_upper:
        return None

    squeeze_modulus = coef_upper
    upper_terms = _residual_terms(upper_candidate, squeezed_var)
    lower_terms = _residual_terms(lower_candidate, squeezed_var)

    all_other_vars = set(upper_terms) | set(lower_terms)
    if any(upper_terms.get(var, 0) + lower_terms.get(var, 0) != 0 for var in all_other_vars):
        return None

    if upper_candidate.rhs + lower_candidate.rhs != squeeze_modulus - 1:
        return None

    return Squeeze_Match(squeeze_modulus=squeeze_modulus, upper_bound_terms=upper_terms, upper_bound_constant=upper_candidate.rhs)


def _find_squeeze_pair(children: Tuple[ASTp_Node, ...], squeezed_var: Var) -> Optional[Squeeze_Match]:
    """
    Enumerate ordered pairs of distinct conjunct indices that are both `<=` relations, testing
    each unordered pair in both role assignments (§4.2). The first match found is used - later
    passes over the same quantifier body (driven by `_eliminate_squeezes_for_quantifier`'s
    fixpoint loop) can pick up any squeeze left behind by this choice.
    """
    for i, upper_candidate in enumerate(children):
        if not (isinstance(upper_candidate, Relation) and upper_candidate.predicate_symbol == '<='):
            continue
        for j, lower_candidate in enumerate(children):
            if i == j or not (isinstance(lower_candidate, Relation) and lower_candidate.predicate_symbol == '<='):
                continue

            match = _try_match_squeeze_pair(upper_candidate, lower_candidate, squeezed_var)
            if match is not None:
                match.upper_index = i
                match.lower_index = j
                return match

    return None


def _classify_residual_conjunct(conjunct: ASTp_Node, squeezed_var: Var) -> Optional[Residual_Bound]:
    """
    §4.3: classify one conjunct (other than the squeeze pair) that references `squeezed_var`.
    Returns None for any shape not in the admissible table, which aborts the whole rewrite for
    `squeezed_var` (§4.3, S4).
    """
    if isinstance(conjunct, Relation):
        coef = _coefficient_of_squeezed_var(conjunct, squeezed_var)
        if abs(coef) != 1:
            return None

        if conjunct.predicate_symbol == '<=':
            kind = Residual_Bound_Kind.UPPER if coef == 1 else Residual_Bound_Kind.LOWER
            return Residual_Bound(kind=kind, terms=_residual_terms(conjunct, squeezed_var), rhs=conjunct.rhs, child_index=-1)

        if conjunct.predicate_symbol == '=':
            # Normalize to coefficient +1 (C3's shape); C4 is C3 after this same normalization.
            normalized = conjunct if coef == 1 else conjunct.multiply_by_num(-1)
            return Residual_Bound(kind=Residual_Bound_Kind.EQUALITY, terms=_residual_terms(normalized, squeezed_var),
                                  rhs=normalized.rhs, child_index=-1)

        return None

    if isinstance(conjunct, AST_Negation) and isinstance(conjunct.child, Relation) and conjunct.child.predicate_symbol == '=':
        equality = conjunct.child
        coef = _coefficient_of_squeezed_var(equality, squeezed_var)
        if abs(coef) != 1:
            return None

        normalized = equality if coef == 1 else equality.multiply_by_num(-1)
        return Residual_Bound(kind=Residual_Bound_Kind.DISEQUALITY, terms=_residual_terms(normalized, squeezed_var),
                              rhs=normalized.rhs, child_index=-1)

    return None


def _substitute_squeezed_var_in_bound(residual: Residual_Bound, squeeze: Squeeze_Match) -> ASTp_Node:
    """§4.4, cases C1-C5."""
    squeeze_modulus = squeeze.squeeze_modulus
    upper_terms = squeeze.upper_bound_terms
    upper_constant = squeeze.upper_bound_constant

    if residual.kind == Residual_Bound_Kind.UPPER:
        # C1: y + T <= k  -->  A*T - T_upper <= A - 1 - k_upper + A*k
        vars_, coefs = _linear_combo(residual.terms, squeeze_modulus, upper_terms, -1)
        rhs = squeeze_modulus - 1 - upper_constant + squeeze_modulus * residual.rhs
        return _fold_relation(Relation(vars=vars_, coefs=coefs, rhs=rhs, predicate_symbol='<='))

    if residual.kind == Residual_Bound_Kind.LOWER:
        # C2: -y + T <= k  -->  T_upper + A*T <= k_upper + A*k
        vars_, coefs = _linear_combo(upper_terms, 1, residual.terms, squeeze_modulus)
        rhs = upper_constant + squeeze_modulus * residual.rhs
        return _fold_relation(Relation(vars=vars_, coefs=coefs, rhs=rhs, predicate_symbol='<='))

    # EQUALITY and DISEQUALITY both build the same two atoms (C3/C4), one per direction of `y == k - T`.
    upper_vars, upper_coefs = _linear_combo(residual.terms, squeeze_modulus, upper_terms, -1)
    upper_rhs = squeeze_modulus - 1 - upper_constant + squeeze_modulus * residual.rhs
    atom_upper = Relation(vars=upper_vars, coefs=upper_coefs, rhs=upper_rhs, predicate_symbol='<=')

    lower_vars, lower_coefs = _linear_combo(upper_terms, 1, residual.terms, -squeeze_modulus)
    lower_rhs = upper_constant - squeeze_modulus * residual.rhs
    atom_lower = Relation(vars=lower_vars, coefs=lower_coefs, rhs=lower_rhs, predicate_symbol='<=')

    if residual.kind == Residual_Bound_Kind.EQUALITY:
        return _make_and([_fold_relation(atom_upper), _fold_relation(atom_lower)])

    # DISEQUALITY (C5): not (atom_upper and atom_lower) == (not atom_upper) or (not atom_lower).
    # `Relation.negate` is exact over the integers, so this is exact too.
    return _make_or([_fold_relation(atom_upper.negate()), _fold_relation(atom_lower.negate())])


def _try_eliminate_squeezed_var(squeezed_var: Var, body: ASTp_Node) -> Optional[ASTp_Node]:
    """§4.2-§4.5 for one bound variable. Returns the rewritten body, or None if no squeeze pair
    on `squeezed_var` is found, or if some other occurrence of `squeezed_var` in `body` does not
    conform to an admissible shape (§4.3)."""
    if not (isinstance(body, AST_Connective) and body.type == Connective_Type.AND):
        return None

    children = body.children
    match = _find_squeeze_pair(children, squeezed_var)
    if match is None:
        return None

    squeeze_indices = {match.upper_index, match.lower_index}

    retained_children: List[ASTp_Node] = []
    residual_bounds: List[Residual_Bound] = []

    for idx, child in enumerate(children):
        if idx in squeeze_indices:
            continue
        if not _references_squeezed_var(child, squeezed_var):
            retained_children.append(child)
            continue

        residual = _classify_residual_conjunct(child, squeezed_var)
        if residual is None:
            return None
        residual_bounds.append(residual)

    for residual in residual_bounds:
        retained_children.append(_substitute_squeezed_var_in_bound(residual, match))

    return _make_and(retained_children)


def _eliminate_squeezes_for_quantifier(bound_vars: Tuple[Var, ...], body: ASTp_Node,
                                       var_table: Dict[Var, VarInfo]) -> Tuple[ASTp_Node, Tuple[Var, ...]]:
    """Loops over `bound_vars` to a fixpoint: eliminating one squeezed variable can expose a
    squeeze on another variable in the same body (e.g. a residual bound of the first variable
    was itself a squeeze bound for a second one)."""
    remaining_vars = list(bound_vars)
    current_body = body

    made_progress = True
    while made_progress:
        made_progress = False
        for var in list(remaining_vars):
            if var_table[var].type != VariableType.INT:
                continue  # S2

            rewritten = _try_eliminate_squeezed_var(var, current_body)
            if rewritten is None:
                continue

            current_body = rewritten
            remaining_vars.remove(var)
            made_progress = True

    return current_body, tuple(remaining_vars)


def eliminate_inner_quantifier_squeezes(root: ASTp_Node, var_table: Dict[Var, VarInfo]) -> ASTp_Node:
    """
    Bottom-up pass eliminating existentially quantified integer variables squeezed between two
    linear bounds with a unit gap. See the module docstring and `docs/QSE_IMPLEMENTATION_PLAN.md`.
    """
    match root:
        case Relation() | Congruence() | BoolLiteral() | Var():
            return root

        case AST_Negation():
            new_child = eliminate_inner_quantifier_squeezes(root.child, var_table)
            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(not new_child.value)
            return AST_Negation(referenced_vars=_extract_referenced_vars(new_child), child=new_child)

        case AST_Connective():
            new_children = tuple(eliminate_inner_quantifier_squeezes(child, var_table) for child in root.children)
            new_node = root.replace_children(new_children)

            new_node = new_node.simplify_on_anihilators()
            if not isinstance(new_node, AST_Connective):
                return new_node

            new_node = new_node.remove_idempotent_children()
            return new_node

        case AST_Quantifier():
            new_child = eliminate_inner_quantifier_squeezes(root.child, var_table)
            new_child, remaining_bound_vars = _eliminate_squeezes_for_quantifier(root.bound_vars, new_child, var_table)

            if not remaining_bound_vars or isinstance(new_child, BoolLiteral):
                return new_child

            return AST_Quantifier(
                referenced_vars=_extract_referenced_vars(new_child),
                bound_vars=remaining_bound_vars,
                child=new_child,
            )

        case _:
            raise ValueError(f'Unhandled node while eliminating inner quantifier squeezes: {root}')
