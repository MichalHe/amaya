from amaya.alphabet import LSBF_Alphabet
from amaya.utils import number_to_bit_tuple

import pytest


def test_generate_symbols_onto_relevant_symbols():
    alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2), ('z', 3)])
    
    # Symbol generation when all variables are valid
    expected_symbols = sorted(number_to_bit_tuple(i, tuple_size=3) for i in range(2**3))
    actual_symbols = sorted(alphabet.gen_symbols_for_relevant_variables([1, 2, 3]))
    assert expected_symbols == actual_symbols

    # The first variable is missing
    expected_symbols = sorted((('*',) + number_to_bit_tuple(i, tuple_size=2)) for i in range(2**2))
    actual_symbols = sorted(alphabet.gen_symbols_for_relevant_variables([2, 3]))
    assert expected_symbols == actual_symbols

    # The last variable is missing
    expected_symbols = sorted((number_to_bit_tuple(i, tuple_size=2) + ('*',)) for i in range(2**2))
    actual_symbols = sorted(alphabet.gen_symbols_for_relevant_variables([1, 2]))
    assert expected_symbols == actual_symbols

    # The middle one is missing
    expected_symbols = sorted((bt[0], '*', bt[1]) for bt in (number_to_bit_tuple(i, tuple_size=2) for i in range(2**2)))
    actual_symbols = sorted(alphabet.gen_symbols_for_relevant_variables([1, 3]))
    assert expected_symbols == actual_symbols

    # Two are missing
    expected_symbols = sorted(('*', '*', i) for i in range(2))
    actual_symbols = sorted(alphabet.gen_symbols_for_relevant_variables([3]))
    assert expected_symbols == actual_symbols
