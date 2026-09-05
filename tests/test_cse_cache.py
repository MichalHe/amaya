"""
Tests for `amaya.cse_cache` (the experimental De Bruijn-keyed automaton cache, see
`DEBRUJIN_CSE.md`):

- `MTBDD_NFA.renamed_copy` (added by this module at runtime) actually renames the automaton's
  language and leaves the original untouched, and the result can still be intersected/unioned
  with a freshly constructed automaton (the `alphabet_variables` bug the design doc calls out).
- `cse_enabled()` does not change the solver's answer on formulas containing repeated
  alpha-equivalent subformulae, and it actually produces cache hits (guards the comparison below
  against being vacuous).
- The default evaluation path (`parse.perform_whole_evaluation_on_source_text`, without
  `cse_enabled()`) is completely unaffected by this module merely being imported.
"""
import copy
import logging

import pytest

from amaya import dsl, parse
from amaya import logger as amaya_logger
from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import AutomatonType
from amaya.config import BackendType, SolutionDomain, solver_config
from amaya.cse_cache import Automaton_Cache, cse_enabled, perform_whole_evaluation_on_source_text_with_cse
from amaya.mtbdd_transitions import MTBDDTransitionFn
from amaya.relations_structures import Relation, Var


X, Y = Var(id=1), Var(id=2)


@pytest.fixture
def mtbdd_solver_config():
    """ Run over integers with the MTBDD backend, restoring the global config afterwards. """
    saved_backend = solver_config.backend_type
    saved_domain = solver_config.solution_domain
    saved_optimizations = copy.deepcopy(solver_config.optimizations)
    saved_log_level = amaya_logger.level

    solver_config.backend_type = BackendType.MTBDD
    solver_config.solution_domain = SolutionDomain.INTEGERS
    amaya_logger.setLevel(logging.WARNING)

    yield solver_config

    solver_config.backend_type = saved_backend
    solver_config.solution_domain = saved_domain
    solver_config.optimizations = saved_optimizations
    amaya_logger.setLevel(saved_log_level)


def _langs_equal(a, b) -> bool:
    """ Whether two (possibly nondeterministic) MTBDD automata accept the same language. """
    da, db = a.determinize(), b.determinize()
    only_in_a = da.intersection(db.complement())
    only_in_b = db.intersection(da.complement())
    return only_in_a.find_model() is None and only_in_b.find_model() is None


# --- MTBDD_NFA.renamed_copy --------------------------------------------------------------------

def test_renamed_copy_renames_the_language(mtbdd_solver_config):
    alphabet = LSBF_Alphabet.from_vars([X, Y])

    x_le_3 = Relation(vars=[X], coefs=[1], rhs=3, predicate_symbol='<=')
    y_le_3 = Relation(vars=[Y], coefs=[1], rhs=3, predicate_symbol='<=')

    nfa_x = MTBDDTransitionFn.construct_nfa_for_ineq(x_le_3, alphabet)
    nfa_y_direct = MTBDDTransitionFn.construct_nfa_for_ineq(y_le_3, alphabet)

    original_states = set(nfa_x.states)
    renamed = nfa_x.renamed_copy({X: Y})

    # The original is untouched.
    assert nfa_x.used_variables == [X]
    assert nfa_x.states == original_states

    assert renamed.used_variables == [Y]
    assert _langs_equal(renamed, nfa_y_direct)
    # Sanity: renaming actually changed something observable (renamed != nfa_x's language, since
    # they now talk about different tracks and `y <= 3` is not the same relation as `x <= 3`).
    assert not _langs_equal(renamed, nfa_x)


def test_renamed_copy_can_still_be_unioned_with_a_fresh_automaton(mtbdd_solver_config):
    """ Regression test for the `alphabet_variables` bug flagged in DEBRUJIN_CSE.md. """
    alphabet = LSBF_Alphabet.from_vars([X, Y])

    x_le_3 = Relation(vars=[X], coefs=[1], rhs=3, predicate_symbol='<=')
    y_le_5 = Relation(vars=[Y], coefs=[1], rhs=5, predicate_symbol='<=')

    nfa_x = MTBDDTransitionFn.construct_nfa_for_ineq(x_le_3, alphabet)
    renamed = nfa_x.renamed_copy({X: Y})  # now "y <= 3"

    nfa_y_le_5 = MTBDDTransitionFn.construct_nfa_for_ineq(y_le_5, alphabet)

    # Must not raise (would raise AssertionError inside MTBDDTransitionFn.union_of if
    # `alphabet_variables` had been corrupted by the renaming).
    union = renamed.union(nfa_y_le_5)
    assert union.find_model() is not None


def test_renamed_copy_identity_renaming_is_an_independent_clone(mtbdd_solver_config):
    alphabet = LSBF_Alphabet.from_vars([X])
    x_le_3 = Relation(vars=[X], coefs=[1], rhs=3, predicate_symbol='<=')
    nfa = MTBDDTransitionFn.construct_nfa_for_ineq(x_le_3, alphabet)

    clone = nfa.renamed_copy({})
    assert clone.used_variables == nfa.used_variables
    assert _langs_equal(clone, nfa)

    # Mutating the clone's states must not affect the original.
    clone.states.add(9999)
    assert 9999 not in nfa.states


# --- end-to-end parity -------------------------------------------------------------------------

def _formula(assertion: str, var_names) -> str:
    declares = ''.join(f'(declare-fun {name} () Int)\n' for name in var_names)
    return f'{declares}(assert {assertion})\n(check-sat)\n'


END_TO_END_CASES = [
    # A conjunction of two alpha-equivalent quantified subformulae - the textbook CSE hit.
    ('(and (exists ((w Int)) (<= x w)) (exists ((v Int)) (<= x v)))', ('x',)),
    # Same shape, but nested inside a disjunction and negation as well.
    ('(or (not (exists ((w Int)) (<= x w))) (exists ((v Int)) (and (<= x v) (<= v 5))))', ('x',)),
    # No repeated subformula at all - the cache should just be a no-op here.
    ('(and (<= x 3) (<= y 5) (<= z 7))', ('x', 'y', 'z')),
    # A repeated atom (below the caching size threshold) plus a repeated composite subformula.
    ('(and (<= x 3) (<= x 3) (exists ((w Int)) (and (<= x w) (<= w 10))) (exists ((v Int)) (and (<= x v) (<= v 10))))', ('x',)),
]


@pytest.mark.parametrize('assertion, var_names', END_TO_END_CASES)
def test_cse_enabled_preserves_the_answer(mtbdd_solver_config, assertion, var_names):
    source_text = _formula(assertion, var_names)

    result_without_cse = parse.perform_whole_evaluation_on_source_text(source_text)
    result_with_cse = perform_whole_evaluation_on_source_text_with_cse(source_text)

    assert result_without_cse is not None and result_with_cse is not None
    assert (result_without_cse.model is not None) == (result_with_cse.model is not None)


def test_cse_enabled_actually_produces_cache_hits(mtbdd_solver_config):
    source_text = _formula(
        '(and (exists ((w Int)) (and (<= x w) (<= w 10))) (exists ((v Int)) (and (<= x v) (<= v 10))))',
        ('x',)
    )

    from amaya.solver_core import EvaluationContext
    import amaya.cse_cache as cse_cache_module

    captured_cache = {}
    original_entry = cse_cache_module.run_evaluation_procedure_cse

    def _spy(ast, ctx, _debug_recursion_depth=0):
        result = original_entry(ast, ctx, _debug_recursion_depth)
        captured_cache['cache'] = getattr(ctx, 'automaton_cache', None)
        return result

    cse_cache_module.run_evaluation_procedure_cse = _spy
    try:
        with cse_enabled():
            # `cse_enabled` rebound `parse.run_evaluation_procedure` to the *original*
            # `run_evaluation_procedure_cse` object it captured at import time; rebind it again to
            # our spy so we can inspect the cache used for this run.
            parse.run_evaluation_procedure = _spy
            result = parse.perform_whole_evaluation_on_source_text(source_text)
    finally:
        cse_cache_module.run_evaluation_procedure_cse = original_entry

    assert result is not None
    cache: Automaton_Cache = captured_cache['cache']
    assert cache is not None
    assert cache.hits >= 1


def test_default_path_unaffected_by_cse_cache_being_importable(mtbdd_solver_config):
    """ Merely having `amaya.cse_cache` imported must not change anything about plain evaluation. """
    assert parse.run_evaluation_procedure.__name__ == 'run_evaluation_procedure'

    source_text = _formula('(and (<= x 3) (<= y 5))', ('x', 'y'))
    result = parse.perform_whole_evaluation_on_source_text(source_text)
    assert result is not None
    assert result.model is not None


def test_non_order_preserving_renaming_is_a_miss_not_a_crash(mtbdd_solver_config):
    """
    Regression: a cache hit whose renaming onto the current occurrence is not order-preserving used to
    propagate `libamaya.rename_vars`' ValueError and kill the whole run (reproducible with
    `--astp-cse` on benchmarks/formulae/psyco/001.smt2). Such a hit must degrade to a rebuild.
    """
    from amaya.mtbdd_automatons import MTBDD_NFA

    source_text = _formula(
        '(and (exists ((w Int)) (and (<= x w) (<= w 10))) (exists ((v Int)) (and (<= x v) (<= v 10))))',
        ('x',)
    )

    expected = parse.perform_whole_evaluation_on_source_text(source_text)

    original_renamed_copy = MTBDD_NFA.renamed_copy

    def _renamed_copy_rejecting_real_renamings(self, renaming):
        # `renamed_copy({})` is the clone used when *storing* into the cache - leave it working; only
        # renamings onto a different occurrence pretend to violate the order requirement.
        if renaming:
            raise ValueError('rename_vars: renaming does not preserve the order of the automaton\'s vars')
        return original_renamed_copy(self, renaming)

    captured_contexts = []

    def _capture(astp, eval_ctx):
        captured_contexts.append(eval_ctx)
        return parse.evaluate_prepared_formula_with_automata(astp, eval_ctx)

    MTBDD_NFA.renamed_copy = _renamed_copy_rejecting_real_renamings
    try:
        with cse_enabled():
            result = parse.perform_whole_evaluation_on_source_text(
                source_text, evaluate_prepared_formula=_capture)
    finally:
        MTBDD_NFA.renamed_copy = original_renamed_copy

    assert result is not None and expected is not None
    assert (result.model is not None) == (expected.model is not None)

    cache = getattr(captured_contexts[0], 'automaton_cache', None)
    assert cache is not None
    assert cache.unusable_renamings >= 1, 'The test did not actually exercise the fallback'
