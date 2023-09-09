from typing import (
    Dict,
    List,
    Union,
)

from amaya.config import solver_config
from amaya.preprocessing import convert_ast_into_evaluable_form
from amaya.preprocessing.eval import VarInfo
from amaya.relations_structures import (
    Congruence,
    FunctionSymbol,
    ModuloTerm,
    Relation,
    Var,
    VariableType,
)

import pytest


def lookup_var(var_table: Dict[Var, VarInfo], var_name: str) -> Var:
    for var, var_info in var_table.items():
        if var_info.name == var_name:
            return var
    raise ValueError(f'No such variable {var_name=} is present in the var table: {var_table=}')


def test_rewrite_simple_equation_ast():
    equation_ast = ['=', ['+', 'x', 'y'], 0]
    global_symbols = [
        FunctionSymbol(name='x', arity=0, args=[], return_type=VariableType.INT),
        FunctionSymbol(name='y', arity=0, args=[], return_type=VariableType.INT),
    ]
    ast, var_table = convert_ast_into_evaluable_form(equation_ast, global_symbols=global_symbols)

    x = lookup_var(var_table, 'x')
    y = lookup_var(var_table, 'y')

    expected_result = Relation.new_lin_relation(variable_names=sorted((x, y)), variable_coefficients=[1, 1],
                                                predicate_symbol='=', absolute_part=0)
    assert ast == expected_result


def test_rewrite_congruence():
    input_ast = ['=', ['*', 3, ['mod', 'x', 5]], 0]
    global_symbols = [FunctionSymbol(name='x', arity=0, args=[], return_type=VariableType.INT)]
    ast, var_table = convert_ast_into_evaluable_form(input_ast, global_symbols=global_symbols)

    x: Var = lookup_var(var_table, 'x')
    m: Var = Var(2)

    solver_config.preprocessing.use_congruences_when_rewriting_modulo = True

    original_eq = Relation.new_lin_relation(variable_names=[m], variable_coefficients=[3], absolute_part=0, predicate_symbol='=')
    congruence = Congruence(vars=[x, m], coefs=[1, -1], modulus=5, rhs=0)
    lower_bound = Relation.new_lin_relation(variable_names=[m], variable_coefficients=[-1], predicate_symbol='<=', absolute_part=0)
    upper_bound = Relation.new_lin_relation(variable_names=[m], variable_coefficients=[1], predicate_symbol='<=', absolute_part=4)

    assert isinstance(ast, list)
    assert ast[0] == 'exists'
    assert ast[1] == [m]

    and_node = ast[2]
    assert isinstance(and_node, list)
    assert and_node[0] == 'and'
    assert len(and_node) == 5
    assert original_eq in and_node[1:]
    assert congruence in and_node[1:]
    assert lower_bound in and_node[1:]
    assert upper_bound in and_node[1:]


def test_relation_ast_condensation_on_rich_ast():
    ast = [
        'exists', [['x', 'Int']],
        ['not',
            ['and',
                ['<=', 'x', 0],
                ['=', ['mod', 'x', 5], 0]]]
    ]

    solver_config.preprocessing.use_congruences_when_rewriting_modulo = True

    ast, var_table = convert_ast_into_evaluable_form(ast, global_symbols=[])

    x = lookup_var(var_table, 'x')
    m = Var(id=2)

    assert isinstance(ast, list)
    assert ast[0] == 'exists'
    assert ast[1] == [x, m]

    assert isinstance(ast[2], list)  # AND node added when introducing m due to quantifier
    and_node = ast[2]
    assert and_node[0] == 'and'

    congruence = Congruence(vars=[x, m], coefs=[1, -1], rhs=0, modulus=5)
    lower_bound = Relation.new_lin_relation(variable_names=[m], variable_coefficients=[-1], predicate_symbol='<=', absolute_part=0)
    upper_bound = Relation.new_lin_relation(variable_names=[m], variable_coefficients=[1], predicate_symbol='<=', absolute_part=4)
    for atom in (congruence, lower_bound, upper_bound):
        assert atom in and_node[1:]
    assert len(and_node) == 5

    original_not_node = [child for child in and_node if isinstance(child, list) and child[0] == 'not'][0]

    original_and_node = original_not_node[1]
    assert isinstance(original_and_node, list)
    assert original_and_node[0] == 'and'

    ineq = Relation.new_lin_relation(variable_names=[x], variable_coefficients=[1], absolute_part=0, predicate_symbol='<=')
    original_eq = Relation.new_lin_relation(variable_names=[m], variable_coefficients=[1], absolute_part=0, predicate_symbol='=')

    assert ineq in original_and_node
    assert original_eq in original_and_node
    assert len(original_and_node) == 3


def test_variable_are_disambiguated():
    input_ast = [
        'exists', [['x', 'Int']],
        [
            'and',
            ['<=', 'x', 0],
            [
                'exists', [['x', 'Int']],
                ['<=', 'x', 0],
            ]
        ]
    ]

    ast, var_table = convert_ast_into_evaluable_form(input_ast, global_symbols=[])
    assert len(var_table) == 2

    top_exists = ast
    assert isinstance(top_exists, list)
    assert top_exists[0] == 'exists'

    and_node = top_exists[2]
    assert isinstance(and_node, list)

    top_relation: Relation = [child for child in and_node if isinstance(child, Relation)][0]
    assert len(top_relation.variable_names) == 1
    top_var = top_relation.variable_names[0]
    assert top_exists[1] == [top_var]

    bottom_exists = [child for child in and_node if isinstance(child, list) and child[0] == 'exists'][0]
    bottom_relation = bottom_exists[2]
    assert isinstance(bottom_relation, Relation)
    assert len(bottom_relation.variable_names) == 1
    bottom_var = bottom_relation.variable_names[0]

    assert bottom_exists[1] == [bottom_var]
