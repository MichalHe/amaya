"""
Conditional Equality Resolution (CER).

Eliminates existentially quantified variables that appear only inside "conditional
equalities" hidden in disjunctions, e.g.:

    exists (x)
       and
          or (alpha_1) (x = t_1)
          or (alpha_2) (x = t_2)
          ...
          or (alpha_n) (x = t_n)

is rewritten (for n >= 2) into the quantifier-free formula:

    (or alpha_1 alpha_2 ... alpha_n) (or (t_1 = t_2) (t_1 = t_3) ... (t_{n-1} = t_n))

See OPTIMISATIONS.md for the full derivation. The n == 1 case is intentionally not
handled here: with a single clause `x` is unconstrained by anything else, so
`exists x. (alpha_1 or x = t_1)` is unconditionally true - a different (already
existing) optimization is responsible for dropping such trivially-true quantifiers.

Additionally, `x` is allowed to also appear in general inequalities - unconditional (i.e.
not hidden behind an escape literal) relations `c*x + (rest) <= k`, where `rest` may
involve other free variables - conjoined alongside the conditional-equality clauses, e.g.:

    exists (x)
       and
          (x <= V114 - 1)
          or (alpha_1) (x = t_1)
          or (alpha_2) (x = t_2)

This is a strictly harder case: unlike the escape literals, `(x <= V114 - 1)` has no
escape of its own - it must hold no matter which branch resolves the equalities, so a
value used to eliminate `x` (either "any value" when every alpha_i holds, or one of the
t_i otherwise) must be checked against it. The correct rewrite (derived and verified
against a full truth table below - see the module-level comment above `_try_eliminate_var`
for why the naive "just substitute one t_i and OR in its escape" rule from EXAMPLE.md is
UNSOUND) is:

    (and D_ok alpha_1 ... alpha_n)
    or (and (not alpha_1) D(t_1) (or alpha_2 (t_1 = t_2)) (or alpha_3 (t_1 = t_3)) ...)
    or (and (not alpha_2) D(t_2) (or alpha_1 (t_1 = t_2)) (or alpha_3 (t_2 = t_3)) ...)
    or ...

where `D` is the conjunction of the inequalities on `x`, `D(t_i)` denotes `D` with `x`
substituted by `t_i` (a purely syntactic linear substitution - always exact, regardless of
how many other variables `D` involves), and `D_ok` says `D` is satisfiable for *some* `x`.

`D(t_i)` never needs a quantifier - substituting a concrete term for `x` is always exact.
`D_ok`, on the other hand, is `exists x. D(x)`, i.e. a genuine (single-variable) quantifier
elimination problem in general. When every inequality in `D` involves no variable other
than `x` ("hard bounds"), this reduces to plain interval-consistency, computed cheaply and
exactly. As soon as an inequality also involves other free variables, computing `D_ok`
exactly in general is full Fourier-Motzkin elimination (with the integer-rounding
subtleties that come with it, e.g. the "dark shadow" construction needed for exactness).
Rather than risk an unsound shortcut there, `D_ok` is instead left as a genuine (but small,
and now scoped to `D` alone rather than the whole original quantifier body) residual
`exists x. D` in that case - still sound, just not as fully flattened as the hard-bounds-only
case.
"""

from __future__ import annotations

import itertools
from typing import List, Optional, Sequence, Tuple

from amaya.relations_structures import (
    ASTp_Node,
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Value_Interval,
    Var,
)


def _extract_referenced_vars(node: ASTp_Node) -> Tuple[Var, ...]:
    if isinstance(node, (Relation, Congruence)):
        return tuple(node.vars)
    elif isinstance(node, (Var,)):
        return (node,)
    elif isinstance(node, (BoolLiteral,)):
        return tuple()
    return tuple(node.referenced_vars)


def fill_referenced_vars(node: ASTp_Node):
    """
    Recompute `referenced_vars` bottom-up so it is accurate for `node` and every subtree of it.

    Originally written so hand-built test trees (the dsl `_and`/`_or`/`_neg`/`_exists` helpers
    default `referenced_vars` to `()`) could be fed to `resolve_conditional_equalities`, which
    relies on the field being accurate. It has since been promoted to a scheduled invariant
    repair in `amaya.preprocessing.pipeline.Optimization_Pipeline` (see
    `Pass_Descriptor.requires_referenced_vars`): every rewrite pass except this one and
    `remove_duplicit_connective_children` is functional (`f(ast) -> ast`, rebuilding rather than
    mutating), and shares unmodified subtrees between its input and output, but this function
    **mutates nodes in place**. That is safe here - the values it writes are correct for any tree
    containing the node - but it means a repair made to one tree (e.g. the pipeline's `current`)
    is also visible from any other tree still holding the same node (e.g. `best`, or a discarded
    candidate). Do not reuse this mechanism for an annotation whose correct value depends on a
    node's ancestors.
    """
    match node:
        case AST_Connective():
            referenced_vars: set[Var] = set()
            for child in node.children:
                fill_referenced_vars(child)
                referenced_vars.update(_extract_referenced_vars(child))
            node.referenced_vars=tuple(sorted(referenced_vars))
            return

        case AST_Negation():
            fill_referenced_vars(node.child)
            childs_referenced_vars = _extract_referenced_vars(node.child)
            node.referenced_vars=tuple(sorted(childs_referenced_vars))
            return

        case AST_Quantifier():
            fill_referenced_vars(node.child)
            childs_referenced_vars = _extract_referenced_vars(node.child)
            node.referenced_vars=tuple(sorted(childs_referenced_vars))
            return

        case _:
            return node


def _subtract_equations(eq: Relation, other_eq: Relation) -> Relation:
    """ Compute `eq - other_eq` as a new `= 0`-normalized Relation (variables shared with equal coefficients cancel out). """
    terms: dict[Var, int] = {var: coef for var, coef in zip(eq.vars, eq.coefs)}

    for var, coef in zip(other_eq.vars, other_eq.coefs):
        new_coef = terms.get(var, 0) - coef
        if new_coef != 0:
            terms[var] = new_coef
        else:
            terms.pop(var, None)

    sorted_terms = sorted(terms.items())
    result_vars = [var for var, _coef in sorted_terms]
    result_coefs = [coef for _var, coef in sorted_terms]
    result_rhs = eq.rhs - other_eq.rhs

    return Relation(vars=result_vars, coefs=result_coefs, rhs=result_rhs, predicate_symbol='=')


def _referenced_vars_of_children(children: List[ASTp_Node]) -> Tuple[Var, ...]:
    seen: set[Var] = set()
    for child in children:
        seen.update(_extract_referenced_vars(child))
    return tuple(sorted(seen))


def _make_or(children: List[ASTp_Node]) -> ASTp_Node:
    filtered = [child for child in children if child != BoolLiteral(False)]
    if any(child == BoolLiteral(True) for child in filtered):
        return BoolLiteral(True)
    if not filtered:
        return BoolLiteral(False)
    if len(filtered) == 1:
        return filtered[0]
    return AST_Connective(referenced_vars=_referenced_vars_of_children(filtered), type=Connective_Type.OR, children=tuple(filtered))


def _make_and(children: Sequence[ASTp_Node]) -> ASTp_Node:
    filtered = [child for child in children if child != BoolLiteral(True)]
    if any(child == BoolLiteral(False) for child in filtered):
        return BoolLiteral(False)
    if not filtered:
        return BoolLiteral(True)
    if len(filtered) == 1:
        return filtered[0]
    return AST_Connective(referenced_vars=_referenced_vars_of_children(filtered), type=Connective_Type.AND, children=tuple(filtered))


def _negate(node: ASTp_Node) -> ASTp_Node:
    """ Push a negation through `node`, keeping it in roughly the same normal form as `push_negations_towards_atoms` does elsewhere. """
    match node:
        case BoolLiteral():
            return BoolLiteral(not node.value)
        case AST_Negation():
            return node.child
        case Var():
            return AST_Negation(referenced_vars=(node,), child=node)
        case Relation():
            if node.predicate_symbol == '<=':
                return node.negate()
            return AST_Negation(referenced_vars=tuple(node.vars), child=node)
        case Congruence():
            return AST_Negation(referenced_vars=tuple(node.vars), child=node)
        case AST_Connective():
            if node.type == Connective_Type.EQUIV:
                # Negating an equivalence isn't a simple De Morgan swap - keep it wrapped.
                return AST_Negation(referenced_vars=node.referenced_vars, child=node)
            flipped_type = Connective_Type.OR if node.type == Connective_Type.AND else Connective_Type.AND
            negated_children = tuple(_negate(child) for child in node.children)
            return AST_Connective(referenced_vars=node.referenced_vars, type=flipped_type, children=negated_children)
        case _:
            raise ValueError(f'Unhandled node while negating: {node}')


def _inequality_coef_of(inequality: Relation, var: Var) -> int:
    """ `var`'s coefficient in `inequality` (`c*var + rest <= k`). Positive means `inequality` bounds `var` from above, negative from below. """
    return inequality.coefs[inequality.vars.index(var)]


def _substitute_var_in_relation(relation: Relation, var: Var, equality: Relation) -> Relation:
    """
    Substitute `var` in `relation` with the term implied by `equality` (`var + sum(coef*v) = rhs`,
    i.e. `var`'s coefficient in `equality` must be +1, as produced by `_match_clause_against_var`).
    """
    if var not in relation.vars:
        return relation

    var_idx = relation.vars.index(var)
    coef = relation.coefs[var_idx]

    terms: dict[Var, int] = {v: c for v, c in zip(relation.vars, relation.coefs) if v != var}
    for v, c in zip(equality.vars, equality.coefs):
        if v == var:
            continue
        terms[v] = terms.get(v, 0) - coef * c

    sorted_terms = sorted((v, c) for v, c in terms.items() if c != 0)
    new_vars = [v for v, _c in sorted_terms]
    new_coefs = [c for _v, c in sorted_terms]
    new_rhs = relation.rhs - coef * equality.rhs

    return Relation(vars=new_vars, coefs=new_coefs, rhs=new_rhs, predicate_symbol=relation.predicate_symbol)


class _Clause_Match:
    __slots__ = ('and_child_index', 'escape', 'equality')

    def __init__(self, and_child_index: int, escape: ASTp_Node, equality: Relation):
        self.and_child_index = and_child_index
        self.escape = escape
        self.equality = equality  # Normalized `var + ... = t`, i.e. var has coefficient +1


def _match_clause_against_var(clause: ASTp_Node, var: Var) -> Optional[Tuple[ASTp_Node, Relation]]:
    """
    If `clause` has the shape `(or alpha (var = t))` (in any order, with `alpha` possibly a
    disjunction of several literals none of which mention `var`), return `(alpha, var = t)` with
    the equality normalized to have `var`'s coefficient equal to +1. Otherwise return None.

    `var` is allowed to occur more than once as long as every occurrence is the *same* equality
    (up to sign) - harmless duplicates like `(or alpha (var = t) (var = t))` are common in
    formulae produced by repeated substitution (e.g. phi-nodes reached via multiple paths) and
    are equivalent to the single-occurrence form. A clause with genuinely different equalities on
    `var` (e.g. `(or (var = t1) (var = t2))`) is a different pattern this function doesn't handle,
    and still returns None.
    """
    if not (isinstance(clause, AST_Connective) and clause.type == Connective_Type.OR):
        return None

    children_containing_var = [child for child in clause.children if var in _extract_referenced_vars(child)]
    if not children_containing_var:
        return None

    normalized_equality: Optional[Relation] = None
    for equality_candidate in children_containing_var:
        if not (isinstance(equality_candidate, Relation) and equality_candidate.predicate_symbol == '='):
            return None

        var_idx = equality_candidate.vars.index(var)
        coef = equality_candidate.coefs[var_idx]
        if abs(coef) != 1:
            return None

        candidate_normalized = equality_candidate if coef == 1 else equality_candidate.multiply_by_num(-1)

        if normalized_equality is None:
            normalized_equality = candidate_normalized
        elif candidate_normalized != normalized_equality:
            return None

    assert normalized_equality is not None

    var_child_ids = {id(child) for child in children_containing_var}
    escape_children = [child for child in clause.children if id(child) not in var_child_ids]
    escape = _make_or(escape_children)

    return escape, normalized_equality


def _try_eliminate_var(var: Var, node: ASTp_Node) -> Optional[ASTp_Node]:
    """
    Try to eliminate `var` from `node` (the quantifier's body) using conditional equality
    resolution. Returns the rewritten body, or None if `var` does not conform to the required
    pattern: `node` must be an AND whose children mentioning `var` are either

      - `(or alpha (var = t))` clauses (at least two of them are required), or
      - unconditional inequalities on `var` (`c*var + (rest, possibly other vars) <= k`, any
        number of them).

    Any other conjunct mentioning `var` aborts the rewrite for `var` entirely (returns None)
    rather than risk an unsound partial rewrite.
    """
    if not (isinstance(node, AST_Connective) and node.type == Connective_Type.AND):
        return None

    matches: List[_Clause_Match] = []
    inequality_indices: List[int] = []
    inequalities: List[Relation] = []

    for idx, child in enumerate(node.children):
        if not var in _extract_referenced_vars(child):
            continue

        if isinstance(child, Relation) and child.predicate_symbol == '<=':
            # TEMPORARILY DISABLED: the inequality-substitution rewrite (`_resolve_with_inequalities`)
            # is switched off - bail out entirely instead of eliminating `var` in its presence.
            return None
            inequality_indices.append(idx)
            inequalities.append(child)
            continue

        matched = _match_clause_against_var(child, var)
        if matched is None:
            return None

        escape, equality = matched
        matches.append(_Clause_Match(and_child_index=idx, escape=escape, equality=equality))

    if len(matches) < 2:
        return None

    if not inequalities:
        # No extra inequalities on `var` - fall back to the simpler (and cheaper) formula:
        # (or alpha_1 ... alpha_n (t_1=t_2) (t_1=t_3) ...). This is a special case of the
        # general formula below (it's what it reduces to when every `D(t_i)` is vacuously
        # True), kept separately because it produces much flatter, more readable output.
        escapes = [match.escape for match in matches]
        pairwise_equalities = [
            _subtract_equations(matches[i].equality, matches[j].equality)
            for i in range(len(matches))
            for j in range(i + 1, len(matches))
        ]
        resolved_disjunction = _make_or(escapes + pairwise_equalities)
    else:
        resolved_disjunction = _resolve_with_inequalities(var, matches, inequalities)

    consumed_indices = {match.and_child_index for match in matches} | set(inequality_indices)
    remaining_and_children = [child for idx, child in enumerate(node.children) if idx not in consumed_indices]
    remaining_and_children.append(resolved_disjunction)

    if len(remaining_and_children) == 1:
        return remaining_and_children[0]

    return AST_Connective(
        referenced_vars=_referenced_vars_of_children(remaining_and_children),
        type=Connective_Type.AND,
        children=tuple(remaining_and_children),
    )


def _resolve_with_inequalities(var: Var, matches: List[_Clause_Match], inequalities: List[Relation]) -> ASTp_Node:
    """
    Same idea as the inequality-free case above, but `var` is additionally constrained by
    unconditional inequalities (`inequalities`, e.g. `x <= V114 - 1`, possibly also involving
    other free variables) that must hold regardless of which equality clause ends up "pinning"
    `var`'s value (or of none doing so, if every escape literal holds). See the module docstring
    for the derivation.
    """
    # Whether D := (and *inequalities) admits *some* value of `var` at all - needed for the branch
    # where every equality clause escapes and `var` is otherwise only constrained by D.
    #
    # `var`'s domain is unbounded in both directions, so if D only bounds it from one side (e.g.
    # only ever `var <= ...`, never `var >= ...`), it's trivially satisfiable for any value of the
    # other variables involved - just push `var` towards the unconstrained direction. Only once D
    # bounds `var` from *both* sides does satisfiability become a real question.
    #
    # When it does, and every such bound is a "hard bound" (mentions only `var`, no other free
    # variables), it reduces to plain interval-consistency, computed exactly and cheaply via
    # Value_Interval. As soon as a bound from both directions also involves other variables,
    # "exists var. D(var)" is no longer a constant - it's a formula over those other variables, and
    # computing it exactly in general is full Fourier-Motzkin elimination (with the integer
    # rounding subtleties that come with it). Rather than risk an unsound shortcut, we keep this
    # branch as a genuine (but much smaller, and now conjuncted with D alone rather than the whole
    # original body) residual `exists var. D`.
    has_upper_bound = any(_inequality_coef_of(ineq, var) > 0 for ineq in inequalities)
    has_lower_bound = any(_inequality_coef_of(ineq, var) < 0 for ineq in inequalities)

    if not (has_upper_bound and has_lower_bound):
        d_is_satisfiable: ASTp_Node = BoolLiteral(True)
    elif all(ineq.is_hard_bound() for ineq in inequalities):
        bound_interval = Value_Interval()
        for bound in inequalities:
            bound_interval.apply_assertion(bound)
        d_is_satisfiable = BoolLiteral(not bound_interval.implies_contradiction())
    else:
        vars_in_inequalities: set[Var] = set(itertools.chain.from_iterable(ineq.vars for ineq in inequalities))
        d_is_satisfiable = AST_Quantifier(
            referenced_vars=tuple(vars_in_inequalities),
            bound_vars=(var,),
            child=_make_and(inequalities),
        )

    all_escapes_branch = _make_and([match.escape for match in matches] + [d_is_satisfiable])

    pivot_terms: List[ASTp_Node] = []
    for i, pivot in enumerate(matches):
        substituted_inequalities = [_substitute_var_in_relation(ineq, var, pivot.equality) for ineq in inequalities]
        agreement_terms = [
            _make_or([matches[j].escape, _subtract_equations(pivot.equality, matches[j].equality)])
            for j in range(len(matches))
            if j != i
        ]
        pivot_terms.append(_make_and([_negate(pivot.escape), *substituted_inequalities, *agreement_terms]))

    return _make_or([all_escapes_branch, *pivot_terms])


def _resolve_conditional_equalities_for_quantifier(bound_vars: Tuple[Var, ...], body: ASTp_Node) -> Tuple[ASTp_Node, Tuple[Var, ...]]:
    remaining_vars = list(bound_vars)
    current_body = body

    made_progress = True
    while made_progress:
        made_progress = False
        for var in list(remaining_vars):
            rewritten = _try_eliminate_var(var, current_body)
            if rewritten is None:
                continue
            current_body = rewritten
            remaining_vars.remove(var)
            made_progress = True

    return current_body, tuple(remaining_vars)


def resolve_conditional_equalities(root: ASTp_Node) -> ASTp_Node:
    """
    Bottom-up pass eliminating existentially quantified variables that appear only in
    conditional equalities (equalities hidden inside disjunctions). See module docstring.
    """
    match root:
        case Relation() | Congruence() | BoolLiteral() | Var():
            return root

        case AST_Negation():
            new_child = resolve_conditional_equalities(root.child)
            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(not new_child.value)
            return AST_Negation(referenced_vars=_extract_referenced_vars(new_child), child=new_child)

        case AST_Connective():
            new_children = tuple(resolve_conditional_equalities(child) for child in root.children)
            new_node = root.replace_children(new_children)

            new_node = new_node.simplify_on_anihilators()
            if not isinstance(new_node, AST_Connective):
                return new_node

            new_node = new_node.remove_idempotent_children()
            return new_node

        case AST_Quantifier():
            new_child = resolve_conditional_equalities(root.child)
            new_child, remaining_bound_vars = _resolve_conditional_equalities_for_quantifier(root.bound_vars, new_child)

            if not remaining_bound_vars or isinstance(new_child, BoolLiteral):
                return new_child

            return AST_Quantifier(
                referenced_vars=_extract_referenced_vars(new_child),
                bound_vars=remaining_bound_vars,
                child=new_child,
            )

        case _:
            raise ValueError(f'Unhandled node while resolving conditional equalities: {root}')
