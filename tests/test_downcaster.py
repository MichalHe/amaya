import pytest
from automatons import LSBF_Alphabet


@pytest.fixture
def bigger_alphabet():
    return LSBF_Alphabet.from_variable_names(('a', 'b', 'c', 'd', 'f'))


@pytest.fixture
def smaller_alphabet():
    return LSBF_Alphabet.from_variable_names(('a', 'd', 'f'))


@pytest.fixture
def smallest_alphabet():
    return LSBF_Alphabet.from_variable_names(('a', 'd'))


def test_downcaster(bigger_alphabet: LSBF_Alphabet, smaller_alphabet: LSBF_Alphabet, smallest_alphabet: LSBF_Alphabet):
    downcaster_0 = smaller_alphabet.get_downcaster_from_higher_dim(bigger_alphabet)
    downcaster_1 = smallest_alphabet.get_downcaster_from_higher_dim(bigger_alphabet)

    assert downcaster_0
    assert downcaster_1

    assert downcaster_0 != downcaster_1
    assert downcaster_0((0, 1, 2, 3, 4)) == (0, 3, 4)
    assert downcaster_1((0, 1, 2, 3, 4)) == (0, 3)

    downcaster_3 = smallest_alphabet.get_downcaster_from_higher_dim(smaller_alphabet)
    assert downcaster_3
    assert downcaster_3((0, 3, 4)) == (0, 3)
