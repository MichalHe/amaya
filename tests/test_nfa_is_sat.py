import pytest

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonType,
    NFA, 
)
from amaya.mtbdd_automatons import (
    MTBDD_NFA, 
)

from amaya.presburger.definitions import (
    AutomatonConstructor
)

def nfa_containing_model(constr: AutomatonConstructor) -> NFA:
    nfa = constr(
        alphabet=LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)]),
        automaton_type=AutomatonType.NFA,
        states={0, 1, 2, 3, 4},
        final_states={4},
        initial_states={0}
    )

    nfa_transitions = [
        # Valid path to final state
        (0, (1, 1), 1),
        (1, (1, 1), 2),
        (2, (1, 1), 2),
        (2, (1, 1), 4),

        # Dead end
        (0, ('*', '*'), 3),
        (3, (1, 1), 3),
    ]

    for transition in nfa_transitions:
        nfa.update_transition_fn(*transition)

    return nfa


def nfa_without_model(constr: AutomatonConstructor) -> NFA:
    nfa = constr(
        alphabet=LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)]),
        automaton_type=AutomatonType.NFA,
        states={0, 1, 2, 3, 4},
        initial_states={0},
        final_states={4},
    )

    # There is a final state but it is unreachable
    nfa_transitions = [
        (0, (1, 1), 1),
        (1, (1, 1), 2),
        (2, (1, 1), 2),
        (2, (1, 1), 3),

        (0, ('*', '*'), 3),
        (3, (1, 1), 3),

        (4, (1, 1), 4),
    ]

    for transition in nfa_transitions:
        nfa.update_transition_fn(*transition)

    return nfa


@pytest.mark.parametrize(
    ('nfa', 'expected_model'), 
    (
        (nfa_containing_model(NFA), ((1, 1), (1, 1), (1, 1))),
        (nfa_containing_model(MTBDD_NFA), ((1, 1), (1, 1), (1, 1))),
        (nfa_without_model(NFA), None),
        (nfa_without_model(MTBDD_NFA), None),
    ))
def test_find_model(nfa: NFA, expected_model):
    model = nfa.find_model()
    assert model == expected_model
