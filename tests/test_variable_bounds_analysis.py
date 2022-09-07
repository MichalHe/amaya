from amaya.relations_structures import (
    ModuloTerm,
    Relation,
)
from amaya.preprocessing.unbound_vars import (
    AST_Leaf_Node_With_Bounds_Info,
    AST_Internal_Node_With_Bounds_Info,
    AST_Quantifier_Node_With_Bounds_Info,
    AST_Node_With_Bounds_Info,
    perform_variable_bounds_analysis_on_ast,
)

import pytest

def test_variable_bounds_analysis_with_simple_ast():
    relation = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                         predicate_symbol='<=', absolute_part=0)
    ast = relation
    actual_result = perform_variable_bounds_analysis_on_ast(ast)

    assert isinstance(actual_result, AST_Leaf_Node_With_Bounds_Info)
    assert actual_result.contents == relation
    assert not actual_result.bounds['x'].has_lower_bound
    assert actual_result.bounds['x'].has_upper_bound


def test_variable_bounds_analysis_with_and():
    left_relation = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                              predicate_symbol='<=', absolute_part=0)
    right_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                              predicate_symbol='>=', absolute_part=-10)

    ast = ['and', left_relation, right_relation]
    actual_result = perform_variable_bounds_analysis_on_ast(ast)

    assert isinstance(actual_result, AST_Internal_Node_With_Bounds_Info)
    assert actual_result.node_type == 'and'
    assert len(actual_result.children) == 2

    assert actual_result.bounds['x'].has_upper_bound
    assert actual_result.bounds['x'].has_lower_bound
    assert actual_result.bounds['y'].has_lower_bound
    assert not actual_result.bounds['y'].has_upper_bound

    left_child = actual_result.children[0]
    assert isinstance(left_child, AST_Leaf_Node_With_Bounds_Info)
    assert left_child.contents == left_relation
    assert len(left_child.bounds) == 1
    assert left_child.bounds['x'].has_upper_bound
    assert not left_child.bounds['x'].has_lower_bound

    right_child = actual_result.children[1]
    assert isinstance(right_child, AST_Leaf_Node_With_Bounds_Info)
    assert right_child.contents == right_relation
    assert len(right_child.bounds) == 2
    assert right_child.bounds['x'].has_lower_bound
    assert not right_child.bounds['x'].has_upper_bound
    assert right_child.bounds['y'].has_lower_bound
    assert not right_child.bounds['y'].has_upper_bound


def test_variable_bounds_analysis_with_or():
    left_relation = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                              predicate_symbol='<=', absolute_part=0)
    right_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                              predicate_symbol='>=', absolute_part=-10)

    ast = ['or', left_relation, right_relation]
    actual_result = perform_variable_bounds_analysis_on_ast(ast)

    assert isinstance(actual_result, AST_Internal_Node_With_Bounds_Info)
    assert actual_result.node_type == 'or'
    assert len(actual_result.children) == 2

    assert actual_result.bounds['x'].has_upper_bound
    assert actual_result.bounds['x'].has_lower_bound
    assert actual_result.bounds['y'].has_lower_bound
    assert not actual_result.bounds['y'].has_upper_bound


def test_variable_bounds_analysis_deeper_ast():
    level1_relation_left = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                                     predicate_symbol='<=', absolute_part=0)
    level1_relation_right = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                                      predicate_symbol='>=', absolute_part=-10)

    level0_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                                predicate_symbol='>=', absolute_part=-20)

    ast = ['exists', [['x', 'Int']], ['or', ['and', level1_relation_left, level1_relation_right], level0_relation]]

    actual_result = perform_variable_bounds_analysis_on_ast(ast)

    assert isinstance(actual_result, AST_Quantifier_Node_With_Bounds_Info)
    assert actual_result.node_type == 'exists'
    assert len(actual_result.children) == 1

    assert actual_result.bounds['x'].has_lower_bound
    assert actual_result.bounds['x'].has_upper_bound
    assert actual_result.bounds['y'].has_lower_bound
    assert not actual_result.bounds['y'].has_upper_bound


def test_variable_bounds_analysis_constrained_mod_terms():
    
    mod_term = ModuloTerm(variables=('x',), variable_coefficients=(1,), constant=0, modulo=13)

    left_relation = Relation(variable_names=[], variable_coefficients=[],
                             div_terms=[], div_term_coefficients=[],
                             modulo_terms=[mod_term], modulo_term_coefficients=[-1],
                             predicate_symbol='>', absolute_part=-8)
    right_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                               predicate_symbol='>=', absolute_part=-10)

    ast = ['and', left_relation, right_relation]

    result = perform_variable_bounds_analysis_on_ast(ast)

    assert len(result.mod_term_bounds) == 1
    assert mod_term in result.mod_term_bounds
    assert result.mod_term_bounds[mod_term].lower_bound == 0
    assert result.mod_term_bounds[mod_term].upper_bound == 7


def test_variable_bounds_analysis_ultimate_automizer_fragment():
    modulo_term = ModuloTerm(variables=('u',), variable_coefficients=(1,), constant=0, modulo=299993)
    # Variable information: Free variables={'w'}, Bound vars={'u', 'v'}
    ast = ['exists', [['u', 'Int'], ['v', 'Int']],
           ['and',
             # (<= 23 w)
             Relation.new_lin_relation(variable_names=['w'], variable_coefficients=[-1],
                                       absolute_part=23, predicate_symbol='<='),
             # (<= (mod u 299993) (+ v 300007))
             Relation(variable_names=['v'], variable_coefficients=[-1],
                      modulo_terms=[modulo_term], modulo_term_coefficients=[1],
                      div_terms=[], div_term_coefficients=[],
                      absolute_part=300007, predicate_symbol='<='),
             # (<= 0 u)
             Relation.new_lin_relation(variable_names=['u'], variable_coefficients=[-1],
                                       absolute_part=0, predicate_symbol='<='),
	     # (<= (+ (* 5 w) 517989) u))))
             Relation.new_lin_relation(variable_names=['w', 'u'], variable_coefficients=[5, -1],
                                       absolute_part=-517989, predicate_symbol='<='),
           ]
    ]

    ast_with_bounds_info = perform_variable_bounds_analysis_on_ast(ast)

    assert isinstance(ast_with_bounds_info, AST_Quantifier_Node_With_Bounds_Info)

    assert ast_with_bounds_info.bounds['w'].has_lower_bound
    assert ast_with_bounds_info.bounds['w'].has_upper_bound

    assert ast_with_bounds_info.bounds['u'].has_lower_bound
    assert not ast_with_bounds_info.bounds['u'].has_upper_bound

    assert ast_with_bounds_info.bounds['v'].has_lower_bound
    assert not ast_with_bounds_info.bounds['v'].has_upper_bound
