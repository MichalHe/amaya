from typing import (
    Dict,
    List,
    Tuple,
)

from amaya.automatons import NFA


def assert_dfas_isomorphic(actual: NFA, expected: NFA):
    assert len(actual.initial_states) == 1
    assert len(actual.initial_states) == len(expected.initial_states)
    assert len(actual.final_states) == len(expected.final_states)
    assert len(actual.states) == len(expected.states), f'{len(actual.states)=} {len(expected.states)=}'
    assert set(actual.used_variables) == set(expected.used_variables), f'{actual.used_variables=} {expected.used_variables}'

    isomorphism: Dict[int, int] = {next(iter(actual.initial_states)): next(iter(expected.initial_states))}

    worklist: List[Tuple[int, int]] = list(isomorphism.items())

    relevant_alphabet = actual.alphabet.gen_symbols_for_relevant_variables(actual.used_variables)
    while worklist:
        actual_state, expected_state = worklist.pop(-1)
        for symbol in relevant_alphabet:
            actual_post = actual.get_transition_target(actual_state, symbol)
            expected_post = expected.get_transition_target(expected_state, symbol)

            assert len(actual_post) == len(expected_post)
            if not actual_post:
                continue
            assert len(actual_post) == 1, f'Post from state {actual_state}: {actual_post}'
            actual_dest, expected_dest = next(iter(actual_post)), next(iter(expected_post))
            if actual_dest in isomorphism:
                assert isomorphism[actual_dest] == expected_dest
            else:
                isomorphism[actual_dest] = expected_dest
                worklist.append((actual_dest, expected_dest))
