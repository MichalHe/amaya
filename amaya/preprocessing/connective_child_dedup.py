"""
Removal of duplicit children of n-ary connectives.

The formulae we receive often contain the same subformula multiple times under a single
connective, e.g., (and (<= x 0) (or A B) (<= x 0)). Such duplicities make the resulting
automata needlessly larger, and they also hide simplification opportunities from the
other preprocessing passes.

The pass works by assigning a unique ID to every distinct atom (relation, congruence,
Bool variable, Bool literal) present in the formula, and then propagating the IDs upwards
- the ID of an inner node is derived from the IDs of its children. Two subformulae are
therefore assigned the same ID iff they are structurally identical (modulo the ordering
of the children of a connective, and modulo the ordering of the terms of an atom).

Once the IDs are known, the children of a connective can be treated as a *set* of IDs,
and the duplicit children can be simply dropped.

The computed IDs are stored in the `_id` field of the produced nodes so that the later
passes can reuse them. Note that `Var` carries no `_id` - a Bool variable is identified
by the variable itself.
"""
from __future__ import annotations

from typing import Dict, List, Tuple

from amaya import logger
from amaya.preprocessing.structural_id import (
    Node_Key,
    Structural_Id_Table,
    _make_atom_key,
    _make_linear_terms_key,
)
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
)


# Kept as an alias so `remove_duplicit_connective_children(ast, id_table=None)`'s public
# signature, and its callers/tests, keep working unchanged.
Node_Id_Table = Structural_Id_Table


def _deduplicate_children(children: Tuple[Tuple[ASTp_Node, int], ...]) -> Tuple[Tuple[ASTp_Node, ...], Tuple[int, ...]]:
    """Drop children with an ID that has already been seen, preserving the original order."""
    seen_ids: Dict[int, None] = {}  # An ordered set
    unique_children: List[ASTp_Node] = []

    for child, child_id in children:
        if child_id in seen_ids:
            continue
        seen_ids[child_id] = None
        unique_children.append(child)

    return tuple(unique_children), tuple(seen_ids)


def _assign_ids(ast: ASTp_Node, id_table: Node_Id_Table) -> Tuple[ASTp_Node, int]:
    """
    Remove duplicit children of the connectives in the given AST and label the nodes with their IDs.

    Returns the rewritten AST together with the ID assigned to its root.
    """
    match ast:
        case Var():
            # Var is not labeled with an _id - it is identified by the variable itself
            return ast, id_table.get_id(_make_atom_key(ast))

        case BoolLiteral() | Relation() | Congruence():
            ast._id = id_table.get_id(_make_atom_key(ast))
            return ast, ast._id

        case AST_Negation():
            child, child_id = _assign_ids(ast.child, id_table)
            node_id = id_table.get_id(('not', child_id))
            node = AST_Negation(referenced_vars=ast.referenced_vars, child=child, _id=node_id)
            return node, node_id

        case AST_Quantifier():
            child, child_id = _assign_ids(ast.child, id_table)
            node_id = id_table.get_id(('exists', tuple(sorted(var.id for var in ast.bound_vars)), child_id))
            node = AST_Quantifier(referenced_vars=ast.referenced_vars, bound_vars=ast.bound_vars,
                                  child=child, _id=node_id)
            return node, node_id

        case AST_Connective():
            labeled_children = tuple(_assign_ids(child, id_table) for child in ast.children)
            children, child_ids = _deduplicate_children(labeled_children)

            if len(children) == 1:
                # (and A A) ~ A,   (or A A) ~ A,   (= A A) ~ True
                if ast.type == Connective_Type.EQUIV:
                    literal = BoolLiteral(True)
                    literal._id = id_table.get_id(_make_atom_key(literal))
                    return literal, literal._id
                return children[0], child_ids[0]

            # The children of a connective are treated as a set - the connectives are
            # both commutative and associative
            node_id = id_table.get_id(('connective', ast.type, frozenset(child_ids)))
            node = AST_Connective(referenced_vars=ast.referenced_vars, type=ast.type, children=children,
                                  variable_bounds=ast.variable_bounds, _id=node_id)
            return node, node_id

        case _:
            raise NotImplementedError(f'Unhandled node while deduplicating connective children: {ast=}')


def remove_duplicit_connective_children(ast: ASTp_Node, id_table: Node_Id_Table | None = None) -> ASTp_Node:
    """
    Remove duplicit children of every connective in the given formula.

    The nodes of the returned formula are labeled with their IDs (the `_id` field), meaning
    that two subformulae have the same ID iff they are structurally identical.

    Params:
        - ast - the formula to rewrite. The formula is not modified, except for its atoms
                that are labeled with their IDs in place.
        - id_table - an optional table to assign the IDs from, so that the IDs can be shared
                     between multiple invocations of this pass.
    """
    id_table = id_table if id_table is not None else Node_Id_Table()

    result, _ = _assign_ids(ast, id_table)

    logger.debug('Removed duplicit connective children. Distinct subformulae seen: %d', id_table.next_id)

    return result
