"""
Rounding of integer quotients must be exact for integers of any size.

The functions below computed floor/ceil of an integer quotient through float division
(`math.floor(a / b)`, `math.floor(0.5 * a)`), which rounds the quotient to the nearest double first and
gives a wrong result once the operands exceed 2**53. The values here are around 2**60, the range of
the 2**64 moduli produced by machine-arithmetic encodings.
"""
import copy
import logging

import pytest

from amaya import logger as amaya_logger
from amaya import parse
from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.config import BackendType, SolutionDomain, solver_config
from amaya.preprocessing.eval import divide_relation_by_gcd
from amaya.presburger.constructions.integers import build_nfa_from_linear_equality, build_nfa_from_linear_inequality
from amaya.relations_structures import Bound_Type, Relation, Var, compute_implied_bound, get_hard_bound_semantics


X = Var(id=1)
LARGE = 2**60


@pytest.fixture
def default_solver_config():
    saved_backend = solver_config.backend_type
    saved_domain = solver_config.solution_domain
    saved_optimizations = copy.deepcopy(solver_config.optimizations)
    saved_log_level = amaya_logger.level
    solver_config.backend_type = BackendType.NATIVE
    solver_config.solution_domain = SolutionDomain.INTEGERS
    amaya_logger.setLevel(logging.WARNING)
    yield solver_config
    solver_config.backend_type = saved_backend
    solver_config.solution_domain = saved_domain
    solver_config.optimizations = saved_optimizations
    amaya_logger.setLevel(saved_log_level)


def test_inequation_automaton_rejects_the_value_just_above_a_large_bound():
    """ `build_nfa_from_linear_inequality` halves the state with floor((value - dot) / 2). """
    alphabet = LSBF_Alphabet.from_vars([X])
    bound_nfa = build_nfa_from_linear_inequality(NFA, alphabet, Relation(vars=[X], coefs=[1], rhs=LARGE - 1, predicate_symbol='<='))
    for value, expected_accepted in ((LARGE - 1, True), (LARGE, False)):
        point_nfa = build_nfa_from_linear_equality(NFA, alphabet, Relation(vars=[X], coefs=[1], rhs=value, predicate_symbol='='))
        assert (bound_nfa.intersection(point_nfa).find_model() is not None) == expected_accepted, value


def test_divide_relation_by_gcd_rounds_a_large_right_hand_side_down(default_solver_config):
    # 3x <= 3*2**60 - 1  <->  x <= 2**60 - 1; float division rounded the quotient up to 2**60.
    relation = divide_relation_by_gcd(Relation(vars=[X], coefs=[3], rhs=3 * LARGE - 1, predicate_symbol='<='))
    assert relation == Relation(vars=[X], coefs=[1], rhs=LARGE - 1, predicate_symbol='<=')


@pytest.mark.parametrize('coef, rhs, expected', [
    (3, 3 * LARGE - 1, (Bound_Type.UPPER, LARGE - 1)),       # float division rounded up to 2**60
    (-3, -(3 * LARGE + 1), (Bound_Type.LOWER, LARGE + 1)),   # float division rounded down to 2**60
    (2, -3, (Bound_Type.UPPER, -2)),
    (-2, 3, (Bound_Type.LOWER, -1)),
])
def test_hard_bound_helpers(coef, rhs, expected):
    relation = Relation(vars=[X], coefs=[coef], rhs=rhs, predicate_symbol='<=')
    bound_type, var, value = get_hard_bound_semantics(relation)
    assert (bound_type, value) == expected and var == X
    assert compute_implied_bound(X, coef, rhs) == expected[1]


def test_contradicting_large_bounds_are_reported_unsat(default_solver_config):
    source_text = f"""
    (declare-fun x () Int)
    (assert (and (<= (* 3 x) {3 * LARGE - 1}) (<= {LARGE} x)))
    (check-sat)
    """
    result = parse.perform_whole_evaluation_on_source_text(source_text)
    assert result is not None and result.model is None
