import pytest
import pressburger_algorithms as pa
from collections import defaultdict
from relations_structures import Relation


@pytest.fixture()
def equality() -> Relation:
    return Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[1, 1],
        absolute_part=4,
        operation='='
    )


def test_dfa_extraction_simple(equality: Relation):
    dfa = pa.build_dfa_from_equality(equality)

    expected_structure = [
        (4, (0, 0), 2),
        (4, (1, 1), 1),
        (2, (0, 0), 1),
        (2, (1, 1), 0),
        (0, (0, 0), 0),
        (0, (1, 1), -1),
        (-1, (0, 1), -1),
        (-1, (1, 0), -1),
    ]

    used_symbols = defaultdict(list)
    for expected_transition in expected_structure:
        o, s, d = expected_transition
        print(o, s, d)
        dest = dfa.get_transition_target(o, s)
        assert len(dest) == 1
        assert d in dest

        used_symbols[o].append(s)

    for origin in used_symbols:
        for symbol in dfa.alphabet.symbols:
            if symbol not in used_symbols[origin]:
                dests = dfa.get_transition_target(origin, symbol)
                assert len(dests) == 1
                assert 'TRAP' in dests

    for symbol in dfa.alphabet.symbols:
        assert 'TRAP' in dfa.get_transition_target('TRAP', symbol)

    assert 0 in dfa.final_states
    assert len(dfa.final_states) == 1
    assert len(dfa.states) == 6  # 5 normal plus trap
    assert 4 in dfa.initial_states
    assert len(dfa.initial_states) == 1
