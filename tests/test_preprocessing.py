from amaya.relations_structures import Relation
from amaya.preprocessing.ite_preprocessing import (
    rewrite_ite_expressions
)

import pytest


ite_simple_input_ast = ['ite', 'C', 'P', 'N']
ite_simple_output_ast = ['or', ['and', 'C', 'P'], ['and', ['not', 'C'], 'N']]


ite_rich_cond = [
    'and',
    ['not', Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=10)],
    Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=10),
]

ite_rich_cond_input_ast = ['ite', ite_rich_cond, 'P', 'N']
ite_rich_cond_output_ast = [
    'or',
    ['and', ite_rich_cond, 'P'],
    ['and', ['not', ite_rich_cond], 'N'],
]

ite_nested_input_ast = [
    'ite',
    'C1',
    ['ite', 'C2', 'P2', 'N2'],
    ['ite', 'C3', 'P3', 'N3'],
]

ite_nested_output_ast = [
    'or',
    [
        'and',
        'C1',
        [
            'or',
            ['and', 'C2', 'P2'],
            ['and', ['not', 'C2'], 'N2'],
        ]
    ],
    [
        'and',
        ['not', 'C1'],
        [
            'or',
            ['and', 'C3', 'P3'],
            ['and', ['not', 'C3'], 'N3'],
        ]
    ],
]


ite_in_relation_simple_input_ast = ['<=', ['+', 'x', ['ite', 'C', 'P', 'N']], 10]
ite_in_relation_simple_output_ast = [
    'or',
    ['and', ['not', 'C'], ['<=', ['+', 'x', 'N'], 10]],
    ['and', 'C', ['<=', ['+', 'x', 'P'], 10]],
]

ite_in_relation_input_ast = [
    'and',
    ['<=', ['+', 'x', ['ite', 'C', 'P', 'N']], 10],
    ['>', ['mod', 'y', ['ite', 'C', 299, 300]], 11],
    ['<', ['div', 'z', ['ite', 'C', 29, 30]], 12],
]

ite_in_relation_output_ast = [
    'and',
    [
        'or',
        ['and', ['not', 'C'], ['<=', ['+', 'x', 'N'], 10]],
        ['and', 'C', ['<=', ['+', 'x', 'P'], 10]],
    ],
    [
        'or',
        ['and', ['not', 'C'], ['>', ['mod', 'y', 300], 11]],
        ['and', 'C', ['>', ['mod', 'y', 299], 11]],
    ],
    [
        'or',
        ['and', ['not', 'C'], ['<', ['div', 'z', 30], 12]],
        ['and', 'C', ['<', ['div', 'z', 29], 12]],
    ],
]

ite_multiple_inside_relation_input_ast = ['<=', ['+', ['ite', 'C1', 'x1', 'x2'], ['ite', 'C2', 'y1', 'y2']], 612]
ite_multiple_inside_relation_output_ast = [
    'or',
    [
        'and',
        ['not', 'C1'],
        ['not', 'C2'],
        ['<=', ['+', 'x2', 'y2'], 612],
    ],
    [
        'and',
        'C1',
        ['not', 'C2'],
        ['<=', ['+', 'x1', 'y2'], 612],
    ],
    [
        'and',
        ['not', 'C1'],
        'C2',
        ['<=', ['+', 'x2', 'y1'], 612],
    ],
    [
        'and',
        'C1',
        'C2',
        ['<=', ['+', 'x1', 'y1'], 612],
    ],
]


@pytest.mark.parametrize(('input_ast', 'expected_ast'),
    (
        (ite_simple_input_ast, ite_simple_output_ast),
        (ite_rich_cond_input_ast, ite_rich_cond_output_ast),
        (ite_nested_input_ast, ite_nested_output_ast),
        (ite_in_relation_simple_input_ast, ite_in_relation_simple_output_ast),
        (ite_in_relation_input_ast, ite_in_relation_output_ast),
        (ite_multiple_inside_relation_input_ast, ite_multiple_inside_relation_output_ast),
    )
)
def test_rewrite_ite_expressions(input_ast, expected_ast):
    actual_ast = rewrite_ite_expressions(input_ast)        
    assert actual_ast == expected_ast