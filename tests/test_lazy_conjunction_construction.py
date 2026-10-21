"""
Tests for the lazy construction of an automaton for a conjunction of atoms
(`amaya.mtbdd_transitions.MTBDDTransitionFn.construct_dfa_for_atom_conjunction`, implemented by
`mtbdd-backend/src/lazy.cpp:build_nfa_with_formula_entailement`).

The construction simplifies the conjunction while exploring it: once the bits read so far fix a
variable to a single value, `mtbdd-backend/src/rewrites.cpp:substitute_var_for_value` substitutes the
value into every atom. Each test compares the language of the constructed automaton, restricted to a
small range of values, with the truth value of the conjunction evaluated directly.
"""
import itertools
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


@pytest.mark.parametrize('lower, upper', [(1, 1), (3, 3), (-2, -2), (0, 0)])
def test_bounds_fixing_a_free_variable(lower, upper):
    """
    The bounds fix the free variable, so it is substituted and marked protected; its own bounds stay in
    the formula to fix its value in the automaton. Their right-hand sides were shifted by the
    substituted value, so `1 <= y <= 1` accepted `y = 0`.
    """
    atoms = [_upper_bound(Y, upper), _lower_bound(Y, lower)]
    assert _accepted_values_of_y(atoms) == _satisfying_values_of_y(atoms)



Z = Var(id=2)


def _lazy_is_sat(atoms, quantified_vars) -> bool:
    alphabet = LSBF_Alphabet.from_vars([Y, Z])
    return MTBDDTransitionFn.construct_dfa_for_atom_conjunction(atoms, list(quantified_vars), alphabet).find_model() is not None


def _is_sat(atoms) -> bool:
    return any(all(_holds(atom, {Y: y_value, Z: z_value}) for atom in atoms)
               for y_value, z_value in itertools.product(range(-10, 11), repeat=2))


@pytest.mark.parametrize('atom', [
    Relation(vars=[Y, Z], coefs=[1, 1], rhs=-3, predicate_symbol='='),   # 1 + 1 = -3 is false
    Relation(vars=[Y, Z], coefs=[1, 1], rhs=2, predicate_symbol='='),    # true
    Relation(vars=[Y, Z], coefs=[1, 2], rhs=0, predicate_symbol='<='),   # 1 + 2 <= 0 is false
    Relation(vars=[Y, Z], coefs=[1, 2], rhs=3, predicate_symbol='<='),   # true
], ids=['false-equation', 'true-equation', 'false-inequation', 'true-inequation'])
def test_atom_left_without_variables_after_substitution(atom):
    """
    `y` is free and `z` quantified, both fixed to 1 by their bounds. Substituting `y` leaves `atom` over
    `z` alone; substituting the quantified `z` then leaves it without variables, and it must be
    evaluated rather than marked satisfied.
    """
    atoms = [_upper_bound(Y, 1), _lower_bound(Y, 1), _upper_bound(Z, 1), _lower_bound(Z, 1), atom]
    assert _lazy_is_sat(atoms, quantified_vars=[Z]) == _is_sat(atoms)


@pytest.mark.parametrize('z_coef, rhs, z_lower, z_upper', [
    (2, 3, 0, 2),   # y = 1: 2z = 2 (mod 4), satisfied by z = 1
    (2, 1, 2, 3),   # y = 1: 2z = 0 (mod 4), satisfied by z = 2
    (2, 2, 0, 3),   # y = 1: 2z = 1 (mod 4), unsatisfiable
])
def test_quantified_variable_with_a_non_invertible_congruence_coefficient(z_coef, rhs, z_lower, z_upper):
    """
    After `y` is substituted, the quantified `z` occurs in a single-variable congruence with a
    coefficient that is not invertible modulo 4. The quantifier must not be instantiated from that
    congruence: the value chosen through a non-existent inverse need not satisfy it.
    """
    atoms = [_upper_bound(Y, 1), _lower_bound(Y, 1), _upper_bound(Z, z_upper), _lower_bound(Z, z_lower),
             Congruence(vars=[Y, Z], coefs=[1, z_coef], rhs=rhs, modulus=4)]
    assert _lazy_is_sat(atoms, quantified_vars=[Z]) == _is_sat(atoms)


@pytest.mark.parametrize('atom', [
    Relation(vars=[Y, Z], coefs=[1, 2], rhs=-1, predicate_symbol='<='),
    Relation(vars=[Y, Z], coefs=[2, 2], rhs=-1, predicate_symbol='<='),
    Relation(vars=[Y, Z], coefs=[2, 2], rhs=1, predicate_symbol='<='),
    Relation(vars=[Y, Z], coefs=[-1, 2], rhs=-2, predicate_symbol='<='),
], ids=['y+2z<=-1', '2y+2z<=-1', '2y+2z<=1', '-y+2z<=-2'])
def test_inequation_divided_by_the_gcd_of_its_coefficients(atom):
    """
    After a substitution, `normalize_coefficients` divides an inequation by the gcd of its
    coefficients, using `div_bound_by_coef` for the right-hand side. For a negative right-hand side
    that function rounded up instead of down, so `2z <= -1` became `z <= 0` instead of `z <= -1`.
    """
    for y_bounds, z_bounds in itertools.product([(0, 2), (1, 1), (2, 3)], repeat=2):
        atoms = [_upper_bound(Y, y_bounds[1]), _lower_bound(Y, y_bounds[0]),
                 _upper_bound(Z, z_bounds[1]), _lower_bound(Z, z_bounds[0]), atom]
        assert _lazy_is_sat(atoms, quantified_vars=[]) == _is_sat(atoms), (y_bounds, z_bounds)


def _accepted_pairs(atoms) -> set:
    alphabet = LSBF_Alphabet.from_vars([Y, Z])
    accepted = set()
    for y_value, z_value in itertools.product(range(-3, 7), repeat=2):
        conjunction_nfa = MTBDDTransitionFn.construct_dfa_for_atom_conjunction(atoms, [], alphabet)
        point_nfa = MTBDDTransitionFn.construct_nfa_for_eq(Relation(vars=[Y], coefs=[1], rhs=y_value, predicate_symbol='='), alphabet)
        point_nfa = point_nfa.intersection(
            MTBDDTransitionFn.construct_nfa_for_eq(Relation(vars=[Z], coefs=[1], rhs=z_value, predicate_symbol='='), alphabet))
        if conjunction_nfa.intersection(point_nfa).find_model() is not None:
            accepted.add((y_value, z_value))
    return accepted


def _accepted_values_of_y_with_z_quantified(atoms) -> set:
    alphabet = LSBF_Alphabet.from_vars([Y, Z])
    accepted = set()
    for y_value in range(-3, 7):
        conjunction_nfa = MTBDDTransitionFn.construct_dfa_for_atom_conjunction(atoms, [Z], alphabet)
        point_nfa = MTBDDTransitionFn.construct_nfa_for_eq(Relation(vars=[Y], coefs=[1], rhs=y_value, predicate_symbol='='), alphabet)
        if conjunction_nfa.intersection(point_nfa).find_model() is not None:
            accepted.add(y_value)
    return accepted


@pytest.mark.parametrize('y_bounds, z_bounds, coefs, rhs, modulus', [
    ((0, 2), (0, 2), [1, 1], 1, 4),    # both variables free; was accepted for y = z
    ((0, 2), (2, 3), [1, 1], 1, 4),    # both variables free; was empty
    ((0, 2), (0, 1), [-1, -1], 0, 3),
])
def test_two_variable_congruence_over_free_variables(y_bounds, z_bounds, coefs, rhs, modulus):
    """
    `linearize_moduli` replaced the congruence by a linear function although the leading variable is
    free: the linearization restricts that variable to a window next to its bound, which preserves
    satisfiability only for a quantified variable.
    """
    atoms = [_upper_bound(Y, y_bounds[1]), _lower_bound(Y, y_bounds[0]), _upper_bound(Z, z_bounds[1]), _lower_bound(Z, z_bounds[0]),
             Congruence(vars=[Y, Z], coefs=coefs, rhs=rhs, modulus=modulus)]
    expected = {(y_value, z_value) for y_value, z_value in itertools.product(range(-3, 7), repeat=2)
                if all(_holds(atom, {Y: y_value, Z: z_value}) for atom in atoms)}
    assert _accepted_pairs(atoms) == expected


@pytest.mark.parametrize('z_bounds, coefs, rhs', [
    ((2, 3), [-1, 1], 0),   # z = y (mod 3); the window z in [3, 5] lost y = 2 (from z = 2)
    ((2, 3), [2, 1], 0),    # leading coefficient on z is 1, subordinate coefficient on y is 2, not -1
    ((0, 1), [2, 1], 2),
])
def test_two_variable_congruence_with_a_two_sided_quantified_variable(z_bounds, coefs, rhs):
    """
    The linearization picks values of the quantified `z` from a window that need not start at its bound,
    which is admissible only when `z` is bounded from one side, and its linear function is derived for
    `z - m = K (mod M)` only.
    """
    atoms = [_upper_bound(Y, 2 if z_bounds == (2, 3) else 3), _lower_bound(Y, 0 if z_bounds == (2, 3) else 1),
             _upper_bound(Z, z_bounds[1]), _lower_bound(Z, z_bounds[0]),
             Congruence(vars=[Y, Z], coefs=coefs, rhs=rhs, modulus=3)]
    expected = {y_value for y_value in range(-3, 7)
                if any(all(_holds(atom, {Y: y_value, Z: z_value}) for atom in atoms) for z_value in range(-20, 21))}
    assert _accepted_values_of_y_with_z_quantified(atoms) == expected
