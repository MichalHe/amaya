from amaya.preprocessing.unbound_vars import (
    AST_Leaf_Node_With_Bounds_Info,
    AST_Internal_Node_With_Bounds_Info,
    remove_existential_quantification_of_unbound_vars,
    Variable_Bounds_Info
)
from amaya.relations_structures import (
    ModuloTerm,
    Relation
)


def test_simplification_on_trivial_formula():
    relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, -1],
                                         operation='<=', absolute_part=10)

    ast = AST_Leaf_Node_With_Bounds_Info(contents=relation)  # We don't care about bounds of the node for this test

    # The relation gives 'y' a lower bound, since 'y' has a negative coefficient
    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=True, has_upper_bound=False)}
    )

    assert result is True


def test_simplification_on_formula_with_negation():
    relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 1],
                                         operation='<=', absolute_part=10)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='not',
        children=[AST_Leaf_Node_With_Bounds_Info(contents=relation)]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result is False


def test_simplification_propagation_through_conjunction():
    left_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 1],
                                              operation='<=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['y'], variable_coeficients=[2],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='and',
        children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result is True

    # Test only one of the 'and' branches being simplified to True

    left_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 1],
                                              operation='<=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['z'], variable_coeficients=[1],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='and',
        children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result == AST_Leaf_Node_With_Bounds_Info(contents=right_relation)

    # Test one of the 'and' branches being simplified to True

    left_relation = Relation.new_lin_relation(variable_names=['x'], variable_coeficients=[1, 1],
                                              operation='>=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['z'], variable_coeficients=[1],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='and',
        children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result == ast

    # Test one of the 'and' branches being simplified to False due to negation, and the other one not being simplified

    left_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 1],
                                              operation='<=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['z'], variable_coeficients=[1],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='and',
        children=[AST_Internal_Node_With_Bounds_Info(node_type='not',
                                                     children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation)]),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result is False


def test_simplification_propagation_through_disjunction():
    # Test both branches being simplified to True
    left_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 1],
                                              operation='<=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['y'], variable_coeficients=[1],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='or',
        children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result is True

    # Test one of the branches being simplified to True

    left_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 1],
                                              operation='<=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['z'], variable_coeficients=[1],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='or',
        children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result is True

    # Test none of the branches being simplified to True

    left_relation = Relation.new_lin_relation(variable_names=['x'], variable_coeficients=[1, 1],
                                              operation='<=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['z'], variable_coeficients=[1],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='or',
        children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result == ast

    # Test one of the branches being simplified to None due to negation and the other not being simplified

    left_relation = Relation.new_lin_relation(variable_names=['y'], variable_coeficients=[1, 1],
                                              operation='<=', absolute_part=10)

    right_relation = Relation.new_lin_relation(variable_names=['z'], variable_coeficients=[1],
                                               operation='<=', absolute_part=5)

    ast = AST_Internal_Node_With_Bounds_Info(
        node_type='or',
        children=[AST_Internal_Node_With_Bounds_Info(node_type='not',
                                                     children=[AST_Leaf_Node_With_Bounds_Info(contents=left_relation)]),
                  AST_Leaf_Node_With_Bounds_Info(contents=right_relation)
        ]
    )

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    assert result == AST_Leaf_Node_With_Bounds_Info(contents=right_relation)


def test_modulo_simplification_on_unbound_variable():
    # x + (y mod 37) <= 10
    modulo_term = ModuloTerm(variables=('y',), variable_coeficients=(1,), constant=0, modulo=37)
    relation = Relation(variable_names=['x'], variable_coeficients=[1],
                        modulo_terms=[modulo_term], modulo_term_coeficients=[1],
                        div_terms=[], div_term_coeficients=[],
                        absolute_part=10, operation='<=')

    ast = AST_Leaf_Node_With_Bounds_Info(contents=relation)

    result = remove_existential_quantification_of_unbound_vars(
        ast, {'y': Variable_Bounds_Info(has_lower_bound=False, has_upper_bound=True)}
    )

    expected_result = AST_Leaf_Node_With_Bounds_Info(contents=Relation.new_lin_relation(variable_names=['x'],
                                                                                        variable_coeficients=[1],
                                                                                        absolute_part=10,
                                                                                        operation='<='))

    assert result == expected_result
