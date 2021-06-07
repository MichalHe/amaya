import pytest
from automatons import NFA, AutomatonType, LSBF_Alphabet, MTBDD_NFA
from relations_structures import Relation
from pressburger_algorithms import build_nfa_from_inequality
from typing import (
    Any,
    Dict,
)


@pytest.fixture
def ineq() -> Relation:
    ineq = Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=3,
        operation="<="
    )
    return ineq


alphabet = LSBF_Alphabet.from_variable_names(['1', '2'])


def test_nfa_state_rename_w_simple_tfn(ineq: Relation):
    nfa = build_nfa_from_inequality(ineq, alphabet, NFA)
    assert nfa, 'Build nfa from ineq did not return a NFA'
    _test_state_renaming(nfa)


def test_nfa_state_rename_w_mtbdd_tfn(ineq: Relation):
    nfa = build_nfa_from_inequality(ineq, alphabet, MTBDD_NFA)
    assert nfa, 'Build nfa from ineq did not return a NFA'
    _test_state_renaming(nfa)


def _test_state_renaming(nfa):
    state_names_translat: Dict[Any, int] = dict()

    def state_renamed(automaton_id: int, old_state: Any, new_state: int):
        state_names_translat[old_state] = new_state

    assert nfa.automaton_type == AutomatonType.NFA

    before_rename_state_posts = {}
    for state in nfa.states:
        before_rename_state_posts[state] = nfa.get_state_post(state)

    nfa._debug_state_rename = state_renamed
    _, new_nfa = nfa.rename_states()

    after_rename_state_posts = {}
    for state in new_nfa.states:
        after_rename_state_posts[state] = new_nfa.get_state_post(state)

    assert new_nfa
    assert nfa.automaton_type == AutomatonType.NFA
    assert len(state_names_translat) == len(new_nfa.states)

    assert len(before_rename_state_posts) == len(after_rename_state_posts),\
        'The dicts containing post sets before and after renaming should be the same size'

    for old_state in before_rename_state_posts:
        new_state = state_names_translat[old_state]

        before_posts = before_rename_state_posts[old_state]
        after_posts = after_rename_state_posts[new_state]

        assert len(before_posts) == len(after_posts),\
            f'The state posts of {old_state}->{new_state} should have the same size after rename'

        # Try rename the old post to the new, and see if they match
        old_post_renames = set(map(lambda old_name: state_names_translat[old_name], before_posts))
        assert old_post_renames == set(after_posts)
