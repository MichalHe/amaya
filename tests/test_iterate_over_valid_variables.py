import pytest
from typing import Set, List, Tuple
from transitions import iterate_over_active_variables


@pytest.fixture()
def normal_alphabet_reduced_pair() -> Tuple[List[str], Set[str]]:
    whole_variables = ['x', 'y', 'z']
    partial_viables = set(['x', 'z'])

    return (whole_variables, partial_viables)


def verify_iteration_symbols(all_variables,
                             reduced_variables,
                             expected_symbols):

    iterator = iterate_over_active_variables(all_variables, reduced_variables)
    symbol_count = 0
    for it_symbol in iterator:
        assert it_symbol in expected_symbols
        symbol_count += 1

    assert symbol_count == len(expected_symbols)


def test_basic_iteration(normal_alphabet_reduced_pair: Tuple[List[str], Set[str]]):
    variables, reduced_variables = normal_alphabet_reduced_pair

    expected_symbols = [
        (0, '*', 0),
        (0, '*', 1),
        (1, '*', 0),
        (1, '*', 1),
    ]

    verify_iteration_symbols(variables, reduced_variables, expected_symbols)


def test_missing_end():
    variables = ['x', 'y', 'z']
    reduced_variables = set(['x'])

    expected_symbols = [
        (0, '*', '*'),
        (1, '*', '*')
    ]

    verify_iteration_symbols(variables, reduced_variables, expected_symbols)


def test_missing_beginning():
    variables = ['x', 'y', 'z']
    reduced_variables = set(['z', 'y'])

    expected_symbols = [
        ('*', 0, 0),
        ('*', 0, 1),
        ('*', 1, 0),
        ('*', 1, 1)
    ]

    verify_iteration_symbols(variables, reduced_variables, expected_symbols)


def test_mixed():
    variables = ['a', 'b', 'c', 'd', 'e', 'f']
    reduced_variables = set(['b', 'c', 'e'])
    expected_symbols = [
        ('*', 0, 0, '*', 0, '*'),
        ('*', 0, 0, '*', 1, '*'),
        ('*', 0, 1, '*', 0, '*'),
        ('*', 0, 1, '*', 1, '*'),

        ('*', 1, 0, '*', 0, '*'),
        ('*', 1, 0, '*', 1, '*'),
        ('*', 1, 1, '*', 0, '*'),
        ('*', 1, 1, '*', 1, '*'),
    ]

    verify_iteration_symbols(variables, reduced_variables, expected_symbols)
