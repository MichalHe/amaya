from typing import (
    Dict,
    List,
)

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
    Value_Interval,
    make_value_interval_intersection,
    make_value_interval_negation,
    make_value_interval_union,
    _simplify_bounded_atoms,
    simplify_bounded_atoms,
)

import pytest


def test_variable_bounds_analysis_on_simple_relation():
    relation = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                         predicate_symbol='<=', absolute_part=0)
    ast = relation
    actual_result = perform_variable_bounds_analysis_on_ast(ast)

    assert actual_result.var_values['x'] == [Value_Interval(lower_limit=None, upper_limit=0)]


def test_variable_bounds_analysis_with_and():
    left_relation = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                              predicate_symbol='<=', absolute_part=0)
    right_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                              predicate_symbol='>=', absolute_part=-10)

    ast = ['and', left_relation, right_relation]
    actual_result = perform_variable_bounds_analysis_on_ast(ast)

    assert actual_result.var_values['x'] == [Value_Interval(lower_limit=None, upper_limit=0)]
    assert actual_result.var_values['y'] == [Value_Interval(None, None)]


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

    assert actual_result.var_values['x'] == [Value_Interval(None, None)]
    assert actual_result.var_values['y'] == [Value_Interval(None, None)]


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

    # x is unconstrained in one of the branches
    assert actual_result.var_values['x'] == [Value_Interval(lower_limit=None, upper_limit=None)]
    assert actual_result.var_values['y'] == [Value_Interval(lower_limit=None, upper_limit=None)]


def test_variable_bounds_analysis_both_bounds():

    lower_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[-1],
                                            predicate_symbol='<=', absolute_part=0)
    upper_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                            predicate_symbol='<=', absolute_part=10)

    ast = ['and', lower_bound, upper_bound]

    result = perform_variable_bounds_analysis_on_ast(ast)

    assert result.var_values['x'] == [Value_Interval(lower_limit=0, upper_limit=10)]


def test_variable_bounds_analysis_with_multiple_bounded_variables():
    ast = ['exists', [['u', 'Int'], ['v', 'Int']],
           ['and',
             # (<= 23 w)
             Relation.new_lin_relation(variable_names=['w'], variable_coefficients=[-1],
                                       absolute_part=23, predicate_symbol='<='),
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

    assert ast_with_bounds_info.var_values['w'] == [Value_Interval(lower_limit=-23, upper_limit=None)]
    assert ast_with_bounds_info.var_values['u'] == [Value_Interval(lower_limit=0, upper_limit=None)]


def test_var_interval_intersection():
    left_intervals = [Value_Interval(None, 10), Value_Interval(20, 30)]
    right_intervals = [Value_Interval(None, 0), Value_Interval(5, 6), Value_Interval(25, None)]

    intersection = make_value_interval_intersection(left_intervals, right_intervals)
    assert len(intersection) == 3
    assert intersection == [Value_Interval(None, 0), Value_Interval(5, 6), Value_Interval(25, 30)]

    left_intervals = [Value_Interval(None, None)]
    right_intervals = [Value_Interval(None, 20)]
    intersection = make_value_interval_intersection(left_intervals, right_intervals)
    assert intersection == right_intervals


def test_var_interval_union():
    left_intervals = [Value_Interval(None, -10), Value_Interval(2, 3), Value_Interval(100, None)]
    right_intervals = [Value_Interval(None, -5), Value_Interval(4, 5), Value_Interval(80, None)]

    union = make_value_interval_union(left_intervals, right_intervals)
    assert union == [Value_Interval(None, -5), Value_Interval(2, 3), Value_Interval(4, 5), Value_Interval(80, None)]


def test_var_interval_negation():
    intervals = [Value_Interval(None, -10), Value_Interval(2, 3), Value_Interval(100, None)]
    negation = make_value_interval_negation(intervals)

    assert negation == [Value_Interval(-9, 1), Value_Interval(4, 99)]

    # Check that double negation is identity
    assert intervals == make_value_interval_negation(negation)


def test_variable_bounds_analysis_on_ultimate_automizer_fragment():
    # ['and',
    #   Relation(-1.m <= 0),
    #   Relation(+1.m <= 299992),
    #   Relation(+1.x -1.v <= 0),
    #   Relation(+1.m -1.y <= 600000),
    #   ['not', Relation(+1.m = 0)],
    #   Relation(+1.v <= -1)
    #   Relation(+1.(-1.m 1.v mod 299993) = 0),
    #  ]

    modulo_term = ModuloTerm(variables=('m', 'v'), variable_coefficients=(-1, 1), constant=0, modulo=299_993)
    ast = [
        'and',
        Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[-1],
                                  predicate_symbol='<=', absolute_part=0),
        Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[1],
                                  predicate_symbol='<=', absolute_part=299_992),
        Relation.new_lin_relation(variable_names=['x', 'v'], variable_coefficients=[1, -1],
                                  predicate_symbol='<=', absolute_part=600_000),
        Relation.new_lin_relation(variable_names=['m', 'y'], variable_coefficients=[1, -1],
                                  predicate_symbol='<=', absolute_part=0),
        ['not', Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[1],
                                          predicate_symbol='=', absolute_part=0)],
        Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[-1],
                                  predicate_symbol='<=', absolute_part=0),
        Relation.new_congruence_relation(modulo_terms=[modulo_term], modulo_term_coefficients=[1], absolute_part=0),
    ]

    ast_with_bounds_info = perform_variable_bounds_analysis_on_ast(ast)

    assert len(ast_with_bounds_info.var_values) == 1
    assert ast_with_bounds_info.var_values['m'] == [Value_Interval(lower_limit=1, upper_limit=299_992)]


def test_simple_variable_bounds_simplification():
    var_bounds: Dict[str, List[Value_Interval]] = {
        'x': [Value_Interval(lower_limit=10, upper_limit=20)],
        'y': [Value_Interval(lower_limit=1, upper_limit=2)]
    }

    preserved_relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 2], predicate_symbol='=', absolute_part=-30)

    relations = [
         Relation.new_lin_relation(variable_names=['y'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=30),
         Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=30),
         Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[-2], predicate_symbol='<=', absolute_part=-30),
         preserved_relation,
    ]

    analyzed_relations: List[AST_Node_With_Bounds_Info] = [AST_Leaf_Node_With_Bounds_Info(contents=relation, var_values={}) for relation in relations]

    analyzed_ast = AST_Internal_Node_With_Bounds_Info(node_type='and',
                                                      children=analyzed_relations,
                                                      var_values=var_bounds,)

    result = _simplify_bounded_atoms(analyzed_ast, {'y'})

    expected_lower_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[-1], predicate_symbol='<=', absolute_part=10)
    expected_upper_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=20)

    assert isinstance(result, list)
    assert len(result) == 4
    assert 'and' == result[0]
    assert expected_lower_bound in result
    assert expected_upper_bound in result
    assert preserved_relation in result


def test_bounds_simplification_on_ultimate_automizer_fragment():
    modulo_term = ModuloTerm(variables=('m', 'v'), variable_coefficients=(-1, 1), constant=0, modulo=299_993)
    preserved_relations = [
        Relation.new_lin_relation(variable_names=['x', 'v'], variable_coefficients=[1, -1],
                                  predicate_symbol='<=', absolute_part=600_000),
        Relation.new_lin_relation(variable_names=['m', 'y'], variable_coefficients=[1, -1],
                                  predicate_symbol='<=', absolute_part=0),
        Relation.new_congruence_relation(modulo_terms=[modulo_term], modulo_term_coefficients=[1], absolute_part=0),
    ]

    ast = [
        'and',
        Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[-1],
                                  predicate_symbol='<=', absolute_part=0),
        Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[1],
                                  predicate_symbol='<=', absolute_part=299_992),
        ['not', Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[1],
                                          predicate_symbol='=', absolute_part=0)],
        *preserved_relations,
    ]

    result = simplify_bounded_atoms(ast)
    assert isinstance(result, list)
    assert result[0] == 'and'
    assert len(result) == 6

    for preserved_relation in preserved_relations:
        assert preserved_relation in result

    upper_bound = Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=299_992)
    lower_bound = Relation.new_lin_relation(variable_names=['m'], variable_coefficients=[-1], predicate_symbol='<=', absolute_part=1)
    assert upper_bound in result
    assert lower_bound in result
