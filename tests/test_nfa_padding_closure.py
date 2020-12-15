import pytest
import automatons as fsms
import transitions as trans
import relations_structures as rs
import pressburger_algorithms as p_algos


@pytest.fixture()
def simple_nfa() -> fsms.NFA:
    states = [
        0, 1, 2, 'F'
    ]

    alphabet = fsms.LSBF_Alphabet.from_variable_names(['x'])

    nfa = fsms.NFA(alphabet=alphabet, automaton_type=fsms.AutomatonType.NFA)
    nfa.states = set(states)
    nfa.add_final_state('F')
    nfa.add_initial_state(0)

    sigma = (0,)
    transitions = [
        (0, sigma, 1),
        (1, sigma, 2),
        (2, sigma, 'F'),
    ]

    for t in transitions:
        nfa.update_transition_fn(*t)

    return nfa


@pytest.fixture()
def multipath_nfa() -> fsms.NFA:
    states = [0, 1, 2, 3, 'F']
    alphabet = fsms.LSBF_Alphabet.from_variable_names(['x', 'y'])
    multipath_nfa = fsms.NFA(alphabet=alphabet, automaton_type=fsms.AutomatonType.NFA)

    multipath_nfa.states = set(states)
    multipath_nfa.add_initial_state(0)
    multipath_nfa.add_final_state('F')

    sigma_1 = (0, 0)
    sigma_2 = (1, 1)

    transitions = [
        (0, sigma_1, 1),

        (1, sigma_1, 2),
        (2, sigma_1, 'F'),

        (1, sigma_2, 3),
        (3, sigma_2, 'F')
    ]

    for t in transitions:
        multipath_nfa.update_transition_fn(*t)

    return multipath_nfa


@pytest.fixture()
def advanced_nfa() -> fsms.NFA:
    states = [-1, 0, 1, 2, 3, 4, 5]
    alphabet = fsms.LSBF_Alphabet.from_variable_names(['x', 'y'])
    advanced_nfa = fsms.NFA(alphabet=alphabet, automaton_type=fsms.AutomatonType.NFA)

    advanced_nfa.states = set(states)
    advanced_nfa.add_initial_state(-1)
    advanced_nfa.add_final_state('F')

    sigma_0 = (0, 0)
    sigma_1 = (0, 1)
    sigma_2 = (1, 0)
    # Transitions
    T = [
        (-1, sigma_0, 0),
        (0, sigma_0, 1),
        (1, sigma_0, 2),
        (2, sigma_0, 3),
        (2, sigma_1, 4),
        (3, sigma_0, 'F'),

        (0, sigma_1, 4),
        (4, sigma_1, 'F'),

        (0, sigma_2, 5),
        (5, sigma_2, 'F'),
    ]

    for t in T:
        advanced_nfa.update_transition_fn(*t)

    return advanced_nfa


@pytest.fixture()
def real_nfa() -> fsms.NFA:
    equality = rs.Relation(['x', 'y'], [2, -1], 2, operation='=')
    return p_algos.build_nfa_from_equality(equality)


def test_simple_finality_propagation(simple_nfa: fsms.NFA):
    # Expect finallity propagation via sigma to every state
    simple_nfa.perform_pad_closure()

    sigma = (0,)
    expected_transitions = [
        (0, sigma, 'F'),
        (1, sigma, 'F'),
        (2, sigma, 'F'),
    ]

    for expected_transition in expected_transitions:
        origin, symbol, destination = expected_transition
        assert 'F' in simple_nfa.get_transition_target(origin, symbol)


def test_multipath_propagation(multipath_nfa: fsms.NFA):
    multipath_nfa.perform_pad_closure()

    sigma_1 = (0, 0)
    sigma_2 = (1, 1)
    expected_trans = [
        (1, sigma_1, 'F'),
        (1, sigma_2, 'F'),
        (0, sigma_1, 'F'),

        # Original transitions
        (0, sigma_1, 1),
        (1, sigma_1, 2),
        (2, sigma_1, 'F'),
        (1, sigma_2, 3),
        (3, sigma_2, 'F')
    ]

    transition_size = 0
    for transition in trans.iter_transition_fn(multipath_nfa.transition_fn):
        assert transition in expected_trans
        transition_size += 1

    assert transition_size == len(expected_trans)


def test_advanced_propagation(advanced_nfa: fsms.NFA):
    transitions_before_padding = list(trans.iter_transition_fn(advanced_nfa.transition_fn))
    advanced_nfa.perform_pad_closure()

    sigma_0 = (0, 0)
    sigma_1 = (0, 1)
    sigma_2 = (1, 0)
    # Expected_transitions
    expected_transitions = [
        (2, sigma_0, 'F'),
        (2, sigma_1, 'F'),
        (1, sigma_0, 'F'),
        (0, sigma_0, 'F'),
        (-1, sigma_0, 'F'),
        (0, sigma_1, 'F'),
        (0, sigma_2, 'F'),
    ]

    all_transitions = expected_transitions + transitions_before_padding

    tc = 0
    for t in trans.iter_transition_fn(advanced_nfa.transition_fn):
        assert t in all_transitions
        tc += 1
    assert tc == len(all_transitions)


def test_real_pressburger_automaton_after_projection(real_nfa: fsms.NFA):
    final_state = list(real_nfa.final_states)[0]
    sigma_0 = (0, '*')  # NOQA
    sigma_1 = (1, '*')  # NOQA

    expected_new_transition = (2, sigma_0, final_state)
    origin, symbol, dest = expected_new_transition

    assert dest not in real_nfa.get_transition_target(origin, symbol)

    real_nfa = real_nfa.do_projection('y')  # Pad closure is done inside projection

    assert dest in real_nfa.get_transition_target(origin, symbol)

    # In fact every ending state (so except TRAP) should lead to final via every symbol
    all_symbols = set([sigma_0, sigma_1])
    for state in real_nfa.states - real_nfa.final_states:
        if state == 'TRAP':
            continue
        assert real_nfa.get_symbols_leading_from_state_to_state(state, 'FINAL') == all_symbols

    dfa = real_nfa.determinize()
    dfa = dfa.complement()
    for state in real_nfa.states - real_nfa.final_states:
        assert not real_nfa.get_symbols_leading_from_state_to_state(state, 'FINAL')