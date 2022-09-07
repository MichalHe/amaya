from amaya.ast_relations import Relation
from amaya.automaton_algorithms import (
    identify_atoms_that_can_imply_fixed_variable_value,
    Fixed_Var_Value_Implication
)


def test_variable_bounds_can_imply_value():
    upper_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=0)
    lower_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[-1], predicate_symbol='<=', absolute_part=0)
    identified_atoms = identify_atoms_that_can_imply_fixed_variable_value([lower_bound, upper_bound])

    assert identified_atoms == [Fixed_Var_Value_Implication(implied_by_atom_with_indicies=[0, 1], variable='x')]


def test_variable_bounds_can_imply_value_with_extra_atoms():
    upper_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=0)
    lower_bound = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[-1], predicate_symbol='<=', absolute_part=0)
    atoms = [
        lower_bound,
        upper_bound,
        Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[-1, 1], predicate_symbol='<=', absolute_part=0),
        Relation.new_lin_relation(variable_names=['y', 'z'], variable_coefficients=[2, 3], predicate_symbol='=', absolute_part=0)
    ]
    identified_atoms = identify_atoms_that_can_imply_fixed_variable_value(atoms)

    assert identified_atoms == [Fixed_Var_Value_Implication(implied_by_atom_with_indicies=[0, 1], variable='x')]


def test_equation_implies_variable_value():
    equation = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='=', absolute_part=0)

    identified_atoms = identify_atoms_that_can_imply_fixed_variable_value([equation])
    assert identified_atoms == [Fixed_Var_Value_Implication(implied_by_atom_with_indicies=[0], variable='x')]

