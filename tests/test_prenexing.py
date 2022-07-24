from amaya.preprocessing.prenexing import (
    PrenexingContext,
    convert_formula_to_pnf
)
from amaya.relations_structures import Relation

import pytest


@pytest.mark.parametrize(
    ('ast', 'expected_result'),
    (
        (
            ['and', ['exists', [['X', 'Int']], 'phi'], 'psi'],
            ['exists', [['X', 'Int']], ['and', 'phi', 'psi']]
        ),
        (
            ['and', ['and', ['exists', [['X', 'Int']], 'phi'], 'eta'], 'psi'],
            ['exists', [['X', 'Int']], ['and', ['and', 'phi', 'eta'], 'psi']]
        ),
    )
)
def test_prenexing_simple(ast, expected_result):
    result = convert_formula_to_pnf(ast)
    assert result == expected_result


@pytest.mark.parametrize(
    ('ast', 'expected_result'),
    (
        (
            ['and', ['exists', [['X', 'Int']], 'phi'], ['not', ['exists', [['Y', 'Int']], 'eta']]],
            ['exists',  [['X', 'Int']], ['forall', [['Y', 'Int']], ['and', 'phi', ['not', 'eta']]]]
        ),
        (
            ['and', ['not', ['exists', [['Y', 'Int']], 'eta']], ['exists', [['X', 'Int']], 'phi']],
            ['forall', [['Y', 'Int']], ['exists', [['X', 'Int']], ['and', ['not', 'eta'], 'phi']]]
        ),
    )
)
def test_prenexing_multiple_quantifiers_simple(ast, expected_result):
    result = convert_formula_to_pnf(ast)
    assert result == expected_result


@pytest.mark.parametrize(
    ('ast', 'expected_result'),
    (
        (
            ['not', ['exists', [['X', 'Int']], 'phi']],
            ['forall', [['X', 'Int']], ['not', 'phi']]
        ),
        (
            ['not', ['forall', [['X', 'Int']], 'phi']],
            ['exists', [['X', 'Int']], ['not', 'phi']]
        ),
        (
            ['not', ['not', ['exists', [['X', 'Int']], 'phi']]],
            ['exists', [['X', 'Int']], ['not', ['not', 'phi']]]
        ),
        (
            ['not', ['not', ['forall', [['X', 'Int']], 'phi']]],
            ['forall', [['X', 'Int']], ['not', ['not', 'phi']]]
        ),
    )
)
def test_prenexing_moving_quantifiers_through_negation(ast, expected_result):
    result = convert_formula_to_pnf(ast)
    assert result == expected_result


def test_prenexing_variable_renaming():
    relation1 = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 2],
                                          operation='<', absolute_part=10)
    relation2 = Relation.new_lin_relation(variable_names=['x', 'z'], variable_coeficients=[2, 1],
                                          operation='<', absolute_part=9)
    ast = [
        'and',
        ['exists', [['x', 'Int']], relation1],
        ['exists', [['x', 'Int']], relation2]
    ]

    result = convert_formula_to_pnf(ast)

    relation1_renamed = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 2],
                                                  operation='<', absolute_part=10)

    relation2_renamed = Relation.new_lin_relation(variable_names=['x-1', 'z'], variable_coeficients=[2, 1],
                                                  operation='<', absolute_part=9)

    expected_result = ['exists', [['x', 'Int']],
                       ['exists', [['x-1', 'Int']], ['and', relation1_renamed, relation2_renamed]]]

    assert result == expected_result
    
    ast = [
        'exists', [['x', 'Int']],
        [
            'and',
            [
                'exists', [['x', 'Int']], 
                Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 1],
                                          absolute_part=0, operation='<')
            ],
            Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 2],
                                      absolute_part=2, operation='=')
        ]
    ]
    
    result = convert_formula_to_pnf(ast)

    expected_result = [
        'exists', [['x', 'Int']], 
        [
            'exists', [['x-1', 'Int']],
            [
                'and', 
                Relation.new_lin_relation(variable_names=['x-1', 'y'], variable_coeficients=[1, 1],
                                          absolute_part=0, operation='<'),
                Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[1, 2],
                                          absolute_part=2, operation='=')
            ]
        ]
    ]

    assert result == expected_result
