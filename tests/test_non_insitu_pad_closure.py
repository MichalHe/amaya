import pytest  # NOQA
from mtbdd_transitions import MTBDDTransitionFn


@pytest.fixture
def tfn() -> MTBDDTransitionFn:
    return MTBDDTransitionFn([1, 2], 0)


def test_basic_transition_propagation__raw_calls(tfn: MTBDDTransitionFn):
    tfn.insert_transition(0, (0, 0), 1)
    tfn.insert_transition(1, (0, 0), 2)

    tfn.call_begin_pad_closure([2])
    result = tfn.call_do_pad_closure(0, tfn.mtbdds[0],
                                     1, tfn.mtbdds[1])
    assert result, 'The result of pad closure of non false mtbdds should be OK.'
    post = MTBDDTransitionFn.call_get_state_post(result)
    assert post, 'The state should have some post set.'
    assert len(post) == 2
    assert 1 in post, 'The original dest state should be present in the state post.'
    assert 2 in post, 'A transition to the final state should be somehow propagated.'

    assert 2 in MTBDDTransitionFn.call_get_transition_target(result, (0, 0))

    tfn.call_end_pad_closure()


def test_basic_cached_r_state__raw_calls(tfn: MTBDDTransitionFn):
    tfn.insert_transition(0, (0, 0), 1)
    tfn.insert_transition(-1, (0, 0), 1)
    tfn.insert_transition(1, (0, 0), 2)

    tfn.call_begin_pad_closure([2])
    result = tfn.call_do_pad_closure(0, tfn.mtbdds[0],
                                     1, tfn.mtbdds[1])
    assert result != tfn.mtbdds[0], 'The pad closure should have effect.'
    assert 2 in MTBDDTransitionFn.call_get_transition_target(result, (0, 0)), 'The transition to final states should get propagated.'

    result = tfn.call_do_pad_closure(-1, tfn.mtbdds[-1],
                                     1, tfn.mtbdds[1])

    assert result != tfn.mtbdds[-1], 'The next pad closure should have effect.'
    assert 2 in MTBDDTransitionFn.call_get_transition_target(result, (0, 0)), 'The transition to final states should get propagated.'

    tfn.call_end_pad_closure()


def test_cached_r_state_after_other_pad_closure__raw_calls(tfn: MTBDDTransitionFn):
    tfn.insert_transition(0, (0, 0), 1)
    tfn.insert_transition(1, (0, 0), 2)
    tfn.insert_transition(5, (0, 0), 1)

    tfn.insert_transition(3, (0, 0), 4)
    tfn.insert_transition(4, (0, 0), 5)

    tfn.call_begin_pad_closure([2, 5])
    result = tfn.call_do_pad_closure(0, tfn.mtbdds[0],
                                     1, tfn.mtbdds[1])
    assert result != tfn.mtbdds[0], 'The pad closure should have effect.'
    assert 2 in MTBDDTransitionFn.call_get_transition_target(result, (0, 0)), 'The transition to final states should get propagated.'

    result = tfn.call_do_pad_closure(3, tfn.mtbdds[3],
                                     4, tfn.mtbdds[4])

    assert result != tfn.mtbdds[3], 'The next pad closure should have effect.'
    assert 5 in MTBDDTransitionFn.call_get_transition_target(result, (0, 0)), 'The transition to final states should get propagated.'

    result = tfn.call_do_pad_closure(5, tfn.mtbdds[5],
                                     1, tfn.mtbdds[1])

    assert result != tfn.mtbdds[3], 'The next pad closure should have effect.'
    target = MTBDDTransitionFn.call_get_transition_target(result, (0, 0))
    assert 2 in target, 'The transition to final states should get propagated.'
    assert 1 in target, 'The transition to final states should get propagated.'

    tfn.call_end_pad_closure()


def test_cached_r_state_after_cache_invalidation__raw_calls(tfn: MTBDDTransitionFn):
    zeta0 = (0, 0)
    zeta1 = (0, 1)
    final_states = [3]

    tfn.insert_transition(0, zeta0, 1)
    tfn.insert_transition(0, zeta1, 1)

    tfn.insert_transition(1, zeta0, 2)
    tfn.insert_transition(1, zeta1, 3)

    tfn.insert_transition(2, zeta0, 3)

    tfn.call_begin_pad_closure(final_states)

    result = tfn.call_do_pad_closure(0, tfn.mtbdds[0],
                                     1, tfn.mtbdds[1])

    assert result != tfn.mtbdds[0], 'The pad closure should have effect.'
    assert 3 in MTBDDTransitionFn.call_get_transition_target(result, zeta1), 'The transition to final states should get propagated.'
    MTBDDTransitionFn.inc_mtbdd_ref_unsafe(result)
    tfn.mtbdds[0] = result

    result = tfn.call_do_pad_closure(1, tfn.mtbdds[1],
                                     2, tfn.mtbdds[2])
    assert result != tfn.mtbdds[1], 'The next pad closure should have effect.'
    assert 3 in MTBDDTransitionFn.call_get_transition_target(result, zeta0), 'The transition to final states should get propagated.'
    MTBDDTransitionFn.inc_mtbdd_ref_unsafe(result)
    tfn.mtbdds[1] = result

    # Now comes the real test -- will the cache invalidation be detected?
    result = tfn.call_do_pad_closure(0, tfn.mtbdds[0],
                                     1, tfn.mtbdds[1])

    assert result != tfn.mtbdds[0], 'The pad closure should have effect.'
    assert 3 in MTBDDTransitionFn.call_get_transition_target(result, zeta0), 'The transition to final states should get propagated.'
    assert 3 in MTBDDTransitionFn.call_get_transition_target(result, zeta1), 'The transition to final states should get propagated.'

    tfn.call_end_pad_closure()


def test_cache_invalidation_when_between_pad_closures(tfn: MTBDDTransitionFn):
    '''Asserts whether the cache are correctly invalidated between two pad closures.'''
    zeta0 = (0, 0)

    tfn.insert_transition(0, zeta0, 1)
    tfn.insert_transition(1, zeta0, 2)

    tfn.call_begin_pad_closure([2])
    result = tfn.call_do_pad_closure(0, tfn.mtbdds[0],
                                     1, tfn.mtbdds[1])
    assert result != tfn.mtbdds[0], 'Pad closure should have effect.'
    destination = tfn.call_get_transition_target(result, zeta0)
    assert 1 in destination, 'Original destination state remain in the transition.'
    assert 2 in destination, 'Transition to final state should be propagated.'

    tfn.call_end_pad_closure()

    # Now the real test
    tfn2 = MTBDDTransitionFn([1, 2], 100)
    tfn2.insert_transition(0, zeta0, 1)
    tfn2.insert_transition(1, zeta0, 2)

    tfn.call_begin_pad_closure([3])  # Different automaton, different final states
    tfn2.write_mtbdd_dot_to_file(tfn2.mtbdds[0], '/tmp/amaya-input0.dot')
    tfn2.write_mtbdd_dot_to_file(tfn2.mtbdds[1], '/tmp/amaya-input1.dot')
    result = tfn2.call_do_pad_closure(0, tfn2.mtbdds[0],
                                      1, tfn2.mtbdds[1])

    tfn.write_mtbdd_dot_to_file(result, '/tmp/amaya.dot')

    assert result == tfn2.mtbdds[0], 'Nothing should get propagated - were the cache results used when they should not be?'
