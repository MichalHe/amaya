"""
Tests for the lazy construction of an automaton for a conjunction of atoms
(`amaya.mtbdd_transitions.MTBDDTransitionFn.construct_dfa_for_atom_conjunction`, implemented by
`mtbdd-backend/src/lazy.cpp:build_nfa_with_formula_entailement`).

The construction simplifies the conjunction while exploring it: once the bits read so far fix a
variable to a single value, `mtbdd-backend/src/rewrites.cpp:substitute_var_for_value` substitutes the
value into every atom. Each test compares the language of the constructed automaton, restricted to a
small range of values, with the truth value of the conjunction evaluated directly.
"""
import logging

import pytest

from amaya import logger as amaya_logger
from amaya.alphabet import LSBF_Alphabet
from amaya.mtbdd_transitions import MTBDDTransitionFn
from amaya.relations_structures import Congruence, Relation, Var


Y = Var(id=1)
VALUE_RANGE = range(-10, 11)


@pytest.fixture(autouse=True)
def quiet_logger():
    saved_log_level = amaya_logger.level
    amaya_logger.setLevel(logging.WARNING)
    yield
    amaya_logger.setLevel(saved_log_level)


def _upper_bound(var: Var, upper: int) -> Relation:
    return Relation(vars=[var], coefs=[1], rhs=upper, predicate_symbol='<=')


def _lower_bound(var: Var, lower: int) -> Relation:
    return Relation(vars=[var], coefs=[-1], rhs=-lower, predicate_symbol='<=')


def _holds(atom, assignment) -> bool:
    total = sum(coef * assignment[var] for coef, var in zip(atom.coefs, atom.vars))
    if isinstance(atom, Congruence):
        return (total - atom.rhs) % atom.modulus == 0
    return total == atom.rhs if atom.predicate_symbol == '=' else total <= atom.rhs


def _accepted_values_of_y(atoms) -> list:
    """ The values of `Y` in `VALUE_RANGE` accepted by the lazily constructed automaton. """
    alphabet = LSBF_Alphabet.from_vars([Y])
    accepted = []
    for value in VALUE_RANGE:
        conjunction_nfa = MTBDDTransitionFn.construct_dfa_for_atom_conjunction(atoms, [], alphabet)
        point_nfa = MTBDDTransitionFn.construct_nfa_for_eq(Relation(vars=[Y], coefs=[1], rhs=value, predicate_symbol='='), alphabet)
        if conjunction_nfa.intersection(point_nfa).find_model() is not None:
            accepted.append(value)
    return accepted


def _satisfying_values_of_y(atoms) -> list:
    return [value for value in VALUE_RANGE if all(_holds(atom, {Y: value}) for atom in atoms)]


@pytest.mark.parametrize('lower, upper, modulus, rhs', [
    (1, 3, 5, 0),   # The conjunction `e2.smt2` reduces to under -O all.
    (1, 2, 3, 0),
    (4, 5, 3, 1),
    (1, 1, 2, 0),
    (-3, -1, 4, 2),
])
def test_two_sided_bounds_and_a_congruence(lower, upper, modulus, rhs):
    """
    A two-sided window fixes the variable once enough bits are read, which triggers the substitution.
    The congruence is left without variables and must be evaluated, not marked satisfied.
    """
    atoms = [_upper_bound(Y, upper), _lower_bound(Y, lower), Congruence(vars=[Y], coefs=[1], rhs=rhs, modulus=modulus)]
    assert _accepted_values_of_y(atoms) == _satisfying_values_of_y(atoms)
