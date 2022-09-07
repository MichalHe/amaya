from amaya.ast_definitions import (
    FunctionSymbol,
    VariableType
)
from amaya.preprocessing import disambiguate_variables


def test_variable_disambiguation_nested_exists():
    ast = [
        'exists', [['X', 'Int']],
        [
            'exists', [['X', 'Int'], ['Y', 'Int']],
            ['<=', ['-', 'X', 'Y'], 299]
        ]
    ]

    expected_result = [
        'exists', [['X', 'Int']],
        [
            'exists', [['X#1', 'Int'], ['Y', 'Int']],
            ['<=', ['-', 'X#1', 'Y'], 299]
        ]
    ]
    actual_result = disambiguate_variables(ast, [])

    assert actual_result == expected_result


def test_variable_disambiguation_parallel_exists_with_same_vars():
    ast = [
        'or',
        [
            'exists', [['X', 'Int']],
                ['<=', ['-', 'X'], 299]],
        [
            'exists', [['X', 'Int']],
                ['<=', ['+', 'X'], 42]],
    ]

    expected_result = [
        'or',
        [
            'exists', [['X', 'Int']],
                ['<=', ['-', 'X'], 299]],
        [
            'exists', [['X#1', 'Int']],
                ['<=', ['+', 'X#1'], 42]],
    ]
    actual_result = disambiguate_variables(ast, [])

    assert actual_result == expected_result


def test_variable_disambiguation_with_global_symbols():
    ast = [
        'exists', [['X', 'Int']],
            ['<=', ['-', 'X', 'Y'], 299]]

    expected_result = [
        'exists', [['X#1', 'Int']],
            ['<=', ['-', 'X#1', 'Y'], 299]]

    constant_fn_symbols = [
        FunctionSymbol(name='X', arity=0, args=[], return_type=VariableType.INT),
        FunctionSymbol(name='Y', arity=0, args=[], return_type=VariableType.INT),
    ]
    actual_result = disambiguate_variables(ast, constant_fn_symbols)

    assert actual_result == expected_result
