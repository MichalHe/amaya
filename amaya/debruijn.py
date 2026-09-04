"""
De Bruijn / slot-normalised encoding of `ASTp_Node` formulae.

This module computes, for every node of a formula tree, a hashable canonical key that is
invariant under alpha-renaming of the variables bound *inside* the subformula rooted at that
node, together with a canonical ascending-sorted tuple of the variables *free* in that
subformula (its "signature"). Two subformulae that are alpha-equivalent (differ only in the
identity of their bound variables) and whose free variables line up 1-1 in ascending-id order
get equal keys.

This is what `amaya/cse_cache.py` uses as the lookup key for its automaton cache: an automaton
built for one occurrence of a subformula can be reused for another occurrence with an equal key,
by renaming its tracks from the cached occurrence's free variables onto the current occurrence's
free variables (in ascending-id correspondence, which is what makes the renaming legal on the
MTBDD backend - see `cse_cache.py` for the monotonicity argument).

Numbering free variables by their rank in `sorted(free_vars(subformula))` (rather than by, say,
first-occurrence order) is deliberate: it is what makes `zip(cached_sig, current_sig)` a strictly
increasing map whenever two keys match, which is required by the MTBDD backend's `rename_vars`.
It also means this encoding is *not* invariant under permutations of the free variables - e.g.
`x <= y` and `y <= x` get different keys. That is intentional, not a missed opportunity.

Note: this is unrelated to `connective_child_dedup`'s `_id` field (`relations_structures.py`),
which is a structural-identity marker used for a different purpose (isomorphism-based
deduplication over the *same* variable ids) and is not a substitute for this encoding, which is
specifically about abstracting variable identity away.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional, Tuple

from amaya.parse import order_congruence_vars
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
)

Slot = int
"""Index into a node's free-variable signature tuple."""


@dataclass(frozen=True)
class Encoded_Node:
    key: Tuple
    """Canonical, hashable, fully variable-identity-free encoding of the subformula."""

    sig: Tuple[Var, ...]
    """Ascending-sorted free variables of this subformula; slot `i` corresponds to `sig[i]`."""


def _var_type_tag(var: Var, var_table: Optional[Dict[Var, VarInfo]]):
    """
    Cheap insurance so that an Int slot can never be matched against a Bool slot: included in
    every leaf key when a `var_table` is supplied, so it also participates in every key built on
    top of that leaf (transitively, through nested tuples).
    """
    if var_table is None:
        return None
    return var_table[var].type


def encode_formula(root: ASTp_Node,
                   var_table: Optional[Dict[Var, VarInfo]] = None,
                   table: Optional[Dict[int, Encoded_Node]] = None) -> Dict[int, Encoded_Node]:
    """
    Compute the De Bruijn / slot-normalised encoding of every node in the tree rooted at `root`,
    bottom-up, in a single pass.

    :param root: Root of the (sub)formula to encode. The caller must keep it (and its children)
                 alive for as long as the returned table is used - it is keyed by `id(node)`.
    :param var_table: Maps variables to their `VarInfo` (for the `VariableType` safety tag). If
                       omitted, leaf keys are not tagged with variable types.
    :param table: An existing id->Encoded_Node table to extend in place (e.g. one built by a
                  previous call to `encode_formula` on a different subtree that shares the same
                  evaluation context). If omitted, a fresh table is created.
    :returns: `table`, extended with an entry for every node in `root`'s subtree.
    """
    if table is None:
        table = {}

    def visit(node: ASTp_Node) -> Encoded_Node:
        node_id = id(node)
        cached = table.get(node_id)
        if cached is not None:
            return cached

        match node:
            case BoolLiteral(value=value):
                result = Encoded_Node(key=('lit', value, 0), sig=())

            case Var():
                result = Encoded_Node(key=('bvar', _var_type_tag(node, var_table)), sig=(node,))

            case Relation():
                pairs = sorted(zip(node.vars, node.coefs), key=lambda pair: pair[0])
                sig = tuple(var for var, _ in pairs)
                coefs = tuple(coef for _, coef in pairs)
                var_types = tuple(_var_type_tag(var, var_table) for var in sig)
                result = Encoded_Node(
                    key=('rel', node.predicate_symbol, var_types, coefs, node.rhs, len(sig)),
                    sig=sig,
                )

            case Congruence():
                # `order_congruence_vars` is what the actual automaton construction uses to
                # order the congruence's tracks - the key must match that, not the AST's own
                # (possibly different) variable order.
                ordered = order_congruence_vars(node)
                sig = tuple(ordered.vars)
                var_types = tuple(_var_type_tag(var, var_table) for var in sig)
                result = Encoded_Node(
                    key=('cong', var_types, tuple(ordered.coefs), ordered.rhs, ordered.modulus, len(sig)),
                    sig=sig,
                )

            case AST_Negation():
                child = visit(node.child)
                result = Encoded_Node(key=('not', child.key, len(child.sig)), sig=child.sig)

            case AST_Connective():
                child_encodings = [visit(child) for child in node.children]

                merged_sig = set()
                for child_encoding in child_encodings:
                    merged_sig.update(child_encoding.sig)
                sig = tuple(sorted(merged_sig))
                parent_slot_of = {var: slot for slot, var in enumerate(sig)}

                pairs = [
                    (child_encoding.key, tuple(parent_slot_of[var] for var in child_encoding.sig))
                    for child_encoding in child_encodings
                ]

                # AND/OR are commutative in `remove_duplicit_connective_children`'s eyes (set
                # semantics) - sorting the children makes reuse insensitive to their order too.
                # EQUIV is evaluated positionally (`evaluate_bool_equivalence_expr`) - keep order.
                if node.type != Connective_Type.EQUIV:
                    pairs = sorted(pairs)

                result = Encoded_Node(key=('conn', int(node.type), tuple(pairs), len(sig)), sig=sig)

            case AST_Quantifier():
                bound_vars = tuple(sorted(node.bound_vars))
                bound_index = {var: idx for idx, var in enumerate(bound_vars)}
                bound_set = set(bound_vars)

                child = visit(node.child)

                sig = tuple(var for var in child.sig if var not in bound_set)
                parent_slot_of = {var: slot for slot, var in enumerate(sig)}

                embedding = tuple(
                    ('b', bound_index[var]) if var in bound_set else ('f', parent_slot_of[var])
                    for var in child.sig
                )

                result = Encoded_Node(
                    key=('exists', len(bound_vars), child.key, embedding, len(sig)),
                    sig=sig,
                )

            case _:
                raise NotImplementedError(f'encode_formula: unhandled AST node: {node!r}')

        table[node_id] = result
        return result

    visit(root)
    return table
