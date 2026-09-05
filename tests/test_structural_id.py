"""
Tests for `amaya.preprocessing.structural_id.compute_structural_id`, the observational
fingerprint used by the fixpoint optimization pipeline for change detection.

Two regressions are the point of this file:
- (d) `(and A B A)` must fingerprint differently from `(and A B)` - a frozenset-of-child-ids
  key would collapse these, making `dedup-connective-children` permanently invisible to the
  scheduler.
- (e) two structurally different trees with the same number of distinct subformulae must
  fingerprint differently when measured against the same table - a fresh table per call turns
  ids into a traversal-order counter that collides between unrelated formulae.
"""
from amaya.preprocessing.structural_id import Structural_Id_Table, compute_structural_id
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    Connective_Type,
    Relation,
    Var,
)


X, Y, Z = Var(id=1), Var(id=2), Var(id=3)


def _rel(var: Var, predicate_symbol: str = '<=', rhs: int = 0) -> Relation:
    return Relation(vars=[var], coefs=[1], rhs=rhs, predicate_symbol=predicate_symbol)


def _and(*children) -> AST_Connective:
    return AST_Connective(referenced_vars=(), type=Connective_Type.AND, children=tuple(children))


def _or(*children) -> AST_Connective:
    return AST_Connective(referenced_vars=(), type=Connective_Type.OR, children=tuple(children))


def _not(child) -> AST_Negation:
    return AST_Negation(referenced_vars=(), child=child)


def _exists(bound_vars, child) -> AST_Quantifier:
    return AST_Quantifier(referenced_vars=(), bound_vars=tuple(bound_vars), child=child)


def test_structurally_identical_trees_have_equal_ids():
    table = Structural_Id_Table()
    tree_a = _and(_rel(X), _rel(Y))
    tree_b = _and(_rel(X), _rel(Y))

    id_a, _ = compute_structural_id(tree_a, table)
    id_b, _ = compute_structural_id(tree_b, table)

    assert id_a == id_b


def test_reordered_connective_children_and_atom_terms_have_equal_ids():
    table = Structural_Id_Table()

    left = _and(_rel(X), _or(_rel(Y), _rel(Z)))
    right = _and(_or(_rel(Z), _rel(Y)), _rel(X))

    id_left, _ = compute_structural_id(left, table)
    id_right, _ = compute_structural_id(right, table)

    assert id_left == id_right


def test_semantically_different_trees_have_different_ids():
    table = Structural_Id_Table()

    base = _and(_rel(X), _rel(Y))
    different_rhs = _and(_rel(X, rhs=1), _rel(Y))
    different_predicate = _and(_rel(X, predicate_symbol='<'), _rel(Y))
    different_var = _and(_rel(X), _rel(Z))

    base_id, _ = compute_structural_id(base, table)
    ids = [
        compute_structural_id(different_rhs, table)[0],
        compute_structural_id(different_predicate, table)[0],
        compute_structural_id(different_var, table)[0],
    ]

    assert base_id not in ids
    assert len(set(ids)) == len(ids)


def test_duplicate_connective_child_is_not_collapsed_away():
    table = Structural_Id_Table()

    with_duplicate = _and(_rel(X), _rel(Y), _rel(X))
    without_duplicate = _and(_rel(X), _rel(Y))

    id_with, _ = compute_structural_id(with_duplicate, table)
    id_without, _ = compute_structural_id(without_duplicate, table)

    assert id_with != id_without


def test_different_trees_with_same_distinct_subformula_count_get_different_ids():
    # Both trees below introduce exactly 3 distinct subformulae (2 atoms + 1 connective) when
    # fingerprinted against a fresh table, so a fresh-table-per-call id would collide on the
    # (2, root) counter value even though the trees are not structurally equal.
    table = Structural_Id_Table()

    tree_a = _and(_rel(X), _rel(Y))
    tree_b = _or(_rel(X), _rel(Z))

    id_a, _ = compute_structural_id(tree_a, table)
    id_b, _ = compute_structural_id(tree_b, table)

    assert id_a != id_b


def test_ids_are_stable_across_calls_sharing_one_table():
    table = Structural_Id_Table()

    subformula = _rel(X)
    tree = _and(subformula, _rel(Y))

    first_id, _ = compute_structural_id(subformula, table)
    compute_structural_id(tree, table)
    second_id, _ = compute_structural_id(subformula, table)

    assert first_id == second_id


def test_node_count_matches_independent_recursive_count():
    def count_nodes(node) -> int:
        match node:
            case AST_Connective():
                return 1 + sum(count_nodes(child) for child in node.children)
            case AST_Negation() | AST_Quantifier():
                return 1 + count_nodes(node.child)
            case _:
                return 1

    table = Structural_Id_Table()
    tree = _exists([X], _not(_and(_rel(X), _or(_rel(Y), _rel(Z)))))

    _, node_count = compute_structural_id(tree, table)

    assert node_count == count_nodes(tree)
