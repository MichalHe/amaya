"""
Structural fingerprinting of ASTp formulae, used by the fixpoint optimization pipeline
(`amaya/preprocessing/pipeline.py`) to detect whether a pass actually changed a formula.

This traversal is deliberately kept separate from `connective_child_dedup._assign_ids`, even
though the two share most of their keying vocabulary. `_assign_ids` fuses id assignment with the
dedup rewrite: it drops duplicate children of a connective and collapses a single-child
connective into that child (or into `BoolLiteral(True)` for EQUIV), so the ids it produces
describe the *rewritten* tree, not the tree it was handed. It also keys a connective by a
`frozenset` of its children's ids, which is only correct once duplicates have already been
removed.

A fingerprint used for change detection must describe the *input* tree faithfully, or the
optimizations that perform exactly the above normalizations (`dedup-connective-children`,
single-child collapsing) become invisible to the scheduler: their output would fingerprint as
identical to their input, be recorded as unproductive, and be discarded on every run. Hence:
`compute_structural_id` never writes to the tree, keys a connective by the *sorted tuple*
(multiset) of its children's ids, and never collapses a single-child connective.

Do not "deduplicate" these two traversals into one - they compute different things on purpose.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Tuple

from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Node,
    BoolLiteral,
    Congruence,
    Relation,
    Var,
)


Node_Key = Tuple


@dataclass
class Structural_Id_Table:
    """Assigns a stable integer id to every distinct (sub)formula seen so far."""
    key_to_id: Dict[Node_Key, int] = field(default_factory=dict)
    next_id: int = 0

    def get_id(self, key: Node_Key) -> int:
        node_id = self.key_to_id.get(key)
        if node_id is None:
            node_id = self.next_id
            self.next_id += 1
            self.key_to_id[key] = node_id
        return node_id


def _make_linear_terms_key(coefs: List[int], vars: List[Var]) -> Tuple[Tuple[int, int], ...]:
    """Make an ordering-insensitive key out of the linear terms of an atom."""
    return tuple(sorted((var.id, coef) for coef, var in zip(coefs, vars)))


def _make_atom_key(atom: ASTp_Node) -> Node_Key:
    match atom:
        case Var():
            return ('var', atom.id)
        case BoolLiteral():
            return ('lit', atom.value)
        case Relation():
            terms = _make_linear_terms_key(atom.coefs, atom.vars)
            return ('rel', atom.predicate_symbol, atom.rhs, terms)
        case Congruence():
            terms = _make_linear_terms_key(atom.coefs, atom.vars)
            return ('congruence', atom.modulus, atom.rhs, terms)
        case _:
            raise NotImplementedError(f'Cannot make an atom key for: {atom=}')


def _compute_structural_id(ast: ASTp_Node, table: Structural_Id_Table) -> Tuple[int, int]:
    """Return `(id_of_node, node_count_of_subtree)`, never mutating `ast`."""
    match ast:
        case Var() | BoolLiteral() | Relation() | Congruence():
            return table.get_id(_make_atom_key(ast)), 1

        case AST_Negation():
            child_id, child_count = _compute_structural_id(ast.child, table)
            node_id = table.get_id(('not', child_id))
            return node_id, child_count + 1

        case AST_Quantifier():
            child_id, child_count = _compute_structural_id(ast.child, table)
            bound_vars_key = tuple(sorted(var.id for var in ast.bound_vars))
            node_id = table.get_id(('exists', bound_vars_key, child_id))
            return node_id, child_count + 1

        case AST_Connective():
            child_results = tuple(_compute_structural_id(child, table) for child in ast.children)
            child_ids = tuple(sorted(child_id for child_id, _ in child_results))
            node_count = 1 + sum(count for _, count in child_results)

            # A multiset (sorted tuple), not a frozenset, of child ids: unlike
            # `_assign_ids`, duplicates have not been removed here, and a frozenset key
            # would make `(and A B A)` and `(and A B)` fingerprint identically.
            node_id = table.get_id(('connective', ast.type, child_ids))
            return node_id, node_count

        case _:
            raise NotImplementedError(f'Unhandled node while computing structural id: {ast=}')


def compute_structural_id(root: ASTp_Node, table: Structural_Id_Table) -> Tuple[int, int]:
    """
    Bottom-up, purely observational fingerprint of `root`. Returns `(root_id, node_count)`.

    Never mutates the tree. Keys are insensitive to (a) the order of a connective's children
    and (b) the order of an atom's terms; they are NOT insensitive to bound-variable renaming.

    `table` must live for the whole pipeline run it is used in - a fresh table per call makes
    ids just a traversal-order counter, which collides for unrelated formulae of similar shape.
    With one persistent table, id equality is equivalent to structural equality for every pair
    of (sub)formulae seen anywhere in the run.
    """
    return _compute_structural_id(root, table)
