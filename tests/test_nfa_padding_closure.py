import itertools
from typing import (
    Callable,
    Tuple,
)
import pytest

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonType,
    AutomatonSnapshot,
    NFA,
)
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.relations_structures import Relation
from amaya.presburger.constructions.integers import build_nfa_from_linear_equality
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType
)


AutomatonFactory = Callable[[LSBF_Alphabet, AutomatonType], NFA]


def mk_simple_nfa(factory: AutomatonFactory) -> NFA:
    final_state = 3
    states = [
        0, 1, 2, final_state
    ]

    alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1)])

    nfa: NFA = factory(alphabet=alphabet, automaton_type=AutomatonType.NFA, state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None))
    nfa.states = set(states)
    nfa.add_final_state(final_state)
    nfa.add_initial_state(0)

    sigma = (0,)
    transitions = [
        (0, sigma, 1),
        (1, sigma, 2),
        (2, sigma, final_state),
    ]

    for t in transitions:
        nfa.update_transition_fn(*t)

    return nfa


def mk_multipath_nfa(factory: AutomatonFactory) -> NFA:
    final_state = 4
    states = [0, 1, 2, 3, final_state]
    alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])
    multipath_nfa = factory(alphabet=alphabet, automaton_type=AutomatonType.NFA, state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None))

    multipath_nfa.states = set(states)
    multipath_nfa.add_initial_state(0)
    multipath_nfa.add_final_state(final_state)

    sigma_1 = (0, 0)
    sigma_2 = (1, 1)

    transitions = [
        (0, sigma_1, 1),

        (1, sigma_1, 2),
        (2, sigma_1, final_state),

        (1, sigma_2, 3),
        (3, sigma_2, final_state)
    ]

    for t in transitions:
        multipath_nfa.update_transition_fn(*t)

    return multipath_nfa


def mk_advanced_nfa(factory: AutomatonFactory) -> NFA:
    states = [-1, 0, 1, 2, 3, 4, 5, 6]
    alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])
    advanced_nfa = factory(alphabet=alphabet, automaton_type=AutomatonType.NFA, state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None))

    final_state = 6

    advanced_nfa.states = set(states)
    advanced_nfa.add_initial_state(-1)
    advanced_nfa.add_final_state(final_state)

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
        (3, sigma_0, final_state),

        (0, sigma_1, 4),
        (4, sigma_1, final_state),

        (0, sigma_2, 5),
        (5, sigma_2, final_state),
    ]

    for t in T:
        advanced_nfa.update_transition_fn(*t)

    return advanced_nfa


@pytest.fixture()
def real_nfa() -> NFA:
    equality = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[2, -1], 
                                         absolute_part=2, predicate_symbol='=')
    alphabet = LSBF_Alphabet.from_variable_ids([1, 2])
    return build_nfa_from_linear_equality(equality, [1, 2], alphabet, NFA)


@pytest.fixture()
def nfa_no_modif_needed(constr: AutomatonFactory) -> NFA:
    """Constructs the automaton using the given factory that does not need repairing."""
    alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])
    nfa = constr(alphabet=alphabet, automaton_type=AutomatonType.NFA, state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None))
    
    nfa.states = {0, 1, 2, 100}

    transitions = (
        (0, (0, 0), 1),
        (0, (1, 0), 2),

        (1, (1, 0), 1),
        (1, (1, 0), 100),
        
        (2, (1, 1), 100),
    )

    for s in transitions:
        nfa.update_transition_fn(*s)

    nfa.initial_states = {0}
    nfa.final_states = {100}
    return nfa


def do_pad_closure_and_get_final_states(nfa: NFA) -> Tuple[Tuple[int, ...], int]:
    """
    Call NFA.pad_closure and return the original final states and the final state added by the pad closure.
    """
    original_final_states = tuple(nfa.final_states)
    nfa.perform_pad_closure()
    new_final_state = next((s for s in nfa.final_states if s not in original_final_states), None)
    assert new_final_state is not None
    return (original_final_states, new_final_state)


def do_simple_padding_closure_tests(nfa: NFA):
    original_final_states, new_final_state = do_pad_closure_and_get_final_states(nfa)
    original_final_state = original_final_states[0]

    padding_symbol = (0,)

    original_transitions = (
        (0, padding_symbol, 1),
        (1, padding_symbol, 2),
        (2, padding_symbol, original_final_state)
    )

    added_transitions = (
        (0, padding_symbol, new_final_state),
        (1, padding_symbol, new_final_state),
    )

    for origin, symbol, dest in itertools.chain(original_transitions, added_transitions):
        assert dest in nfa.get_transition_target(origin, symbol)


def test_mtbdd_simple_finality_propagation():
    simple_nfa = mk_simple_nfa(MTBDD_NFA)
    do_simple_padding_closure_tests(simple_nfa)


def test_simple_finality_propagation():
    simple_nfa = mk_simple_nfa(NFA)
    do_simple_padding_closure_tests(simple_nfa)


def do_multipath_propagation_tests(multipath_nfa: NFA):
    original_final_states, new_final_state = do_pad_closure_and_get_final_states(multipath_nfa)
    original_final_state = original_final_states[0]

    sigma_1 = (0, 0)
    sigma_2 = (1, 1)
    expected_trans = [
        # Original transitions
        (0, sigma_1, 1),
        (1, sigma_1, 2),
        (2, sigma_1, original_final_state),
        (1, sigma_2, 3),
        (3, sigma_2, original_final_state),

        # Transitions added by pad close
        (1, sigma_1, new_final_state),
        (1, sigma_2, new_final_state),
        (0, sigma_1, new_final_state),
    ]

    transition_size = 0
    present_transitions = []
    for transition in multipath_nfa.transition_fn.iter():
        assert transition in expected_trans
        transition_size += 1
        present_transitions.append(transition)

    assert transition_size == len(expected_trans)


def test_multipath_propagation_tests():
    nfa = mk_multipath_nfa(NFA)
    do_multipath_propagation_tests(nfa)


def test_mtbdd_multipath_propagation_tests():
    nfa = mk_multipath_nfa(MTBDD_NFA)
    do_multipath_propagation_tests(nfa)


def do_advanced_propagation_tests(nfa: NFA):
    transitions_before_padding = list(nfa.transition_fn.iter())
    original_final_states, new_final_state = do_pad_closure_and_get_final_states(nfa)
    original_final_state = original_final_states[0]

    sigma_0 = (0, 0)
    sigma_1 = (0, 1)
    sigma_2 = (1, 0)
    # Expected_transitions
    final_state = 6
    expected_transitions = [
        (2, sigma_0, new_final_state),
        (2, sigma_1, new_final_state),
        (1, sigma_0, new_final_state),
        (0, sigma_0, new_final_state),
        (0, sigma_1, new_final_state),
        (0, sigma_2, new_final_state),
        (-1, sigma_0, new_final_state),
    ]

    all_transitions = expected_transitions + transitions_before_padding

    transition_cnt = 0
    for t in nfa.transition_fn.iter():
        assert t in all_transitions
        transition_cnt += 1
    assert transition_cnt == len(all_transitions)


def test_advanced_propagation():
    nfa = mk_advanced_nfa(NFA)
    do_advanced_propagation_tests(nfa)


def test_mtbdd_advanced_propagation():
    nfa = mk_advanced_nfa(MTBDD_NFA)
    do_advanced_propagation_tests(nfa)


@pytest.mark.skip()
def test_real_pressburger_automaton_after_projection(real_nfa: NFA):
    """
    Note:
        *Not performed at the moment* - the MTBDD NFAs do not fully support variable projection.
    """
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


@pytest.mark.parametrize('constr', (NFA, MTBDD_NFA))
def test_no_pad_closure_needed(constr, nfa_no_modif_needed: NFA):
    snapshot_before = AutomatonSnapshot.create_snapshot(nfa_no_modif_needed)
    nfa_no_modif_needed.perform_pad_closure()
    snapshot_after =  AutomatonSnapshot.create_snapshot(nfa_no_modif_needed)

    assert snapshot_before == snapshot_after
