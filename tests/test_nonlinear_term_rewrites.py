from amaya.relations_structures import (
    ModuloTerm,
    Relation,
)
from amaya.preprocessing import rewrite_nonlinear_terms


def test_mod_term_inside_relation_rewrite():
    term = ModuloTerm(variables=('x',), variable_coefficients=(1,), constant=0, modulo=3)
    relation = Relation(variable_names=['y'], variable_coefficients=[1],
                        modulo_terms=[term], modulo_term_coefficients=[-1],
                        div_terms=[], div_term_coefficients=[],
                        predicate_symbol='<=', absolute_part=10)
    ast = ['exists', [['x', 'Int']], relation]

    actual_ast = rewrite_nonlinear_terms(ast)

    # This might fail if the returned ast is malformed, or not as expected
    assert actual_ast[0] == 'exists'
    assert len(actual_ast[1]) == 2

    new_var, new_var_type = actual_ast[1][1]
    assert new_var_type == 'Int'

    conjunction = actual_ast[2]
    assert conjunction[0] == 'and'

    lower_bound = Relation.new_lin_relation(variable_names=[new_var], variable_coefficients=[-1],
                                            predicate_symbol='<=', absolute_part=0)
    upper_bound = Relation.new_lin_relation(variable_names=[new_var], variable_coefficients=[1],
                                            predicate_symbol='<=', absolute_part=term.modulo - 1)

    congruence_term = ModuloTerm(variables=('x', new_var), variable_coefficients=(1, -1), constant=0, modulo=3)
    congruence_term = congruence_term.into_sorted()
    congruence = Relation.new_congruence_relation(modulo_terms=[congruence_term], modulo_term_coefficients=[1])

    original_relation = Relation.new_lin_relation(variable_names=['y', new_var], variable_coefficients=[1, -1],
                                                  predicate_symbol='<=', absolute_part=10)

    original_relation.sort_variables_alphabetically()

    actual_atoms = conjunction[1:]
    assert len(actual_atoms) == 4, actual_atoms

    assert lower_bound in actual_atoms
    assert upper_bound in actual_atoms
    assert congruence in actual_atoms
    assert original_relation in actual_atoms


def test_mod_term_inside_congruence_rewrite():
    term = ModuloTerm(variables=('x',), variable_coefficients=(1,), constant=0, modulo=3)
    congruence = Relation.new_congruence_relation(modulo_terms=[term], modulo_term_coefficients=[1])

    ast = ['exists', [['x', 'Int']], congruence]

    actual_ast = rewrite_nonlinear_terms(ast)
    assert actual_ast == ast


def test_mod_term_with_free_variable_rewrite():
    term = ModuloTerm(variables=('x',), variable_coefficients=(1,), constant=0, modulo=3)
    relation = Relation(variable_names=['y'], variable_coefficients=[1],
                        modulo_terms=[term], modulo_term_coefficients=[-1],
                        div_terms=[], div_term_coefficients=[],
                        predicate_symbol='<=', absolute_part=10)

    ast = relation
    actual_ast = rewrite_nonlinear_terms(ast)

    assert isinstance(actual_ast, list)

    assert actual_ast[0] == 'exists'
    assert len(actual_ast[1]) == 1
    new_var, new_var_type = actual_ast[1][0]
    assert new_var_type == 'Int'

    lower_bound = Relation.new_lin_relation(variable_names=[new_var], variable_coefficients=[-1],
                                            predicate_symbol='<=', absolute_part=0)
    upper_bound = Relation.new_lin_relation(variable_names=[new_var], variable_coefficients=[1],
                                            predicate_symbol='<=', absolute_part=term.modulo - 1)

    congruence_term = ModuloTerm(variables=('x', new_var), variable_coefficients=(1, -1), constant=0, modulo=3)
    congruence_term = congruence_term.into_sorted()
    congruence = Relation.new_congruence_relation(modulo_terms=[congruence_term], modulo_term_coefficients=[1])

    original_relation = Relation.new_lin_relation(variable_names=['y', new_var], variable_coefficients=[1, -1],
                                                  predicate_symbol='<=', absolute_part=10)

    original_relation.sort_variables_alphabetically()

    conjunction = actual_ast[2]
    assert conjunction[0] == 'and'

    actual_atoms = conjunction[1:]
    assert len(actual_atoms) == 4, actual_atoms

    assert lower_bound in actual_atoms
    assert upper_bound in actual_atoms
    assert congruence in actual_atoms
    assert original_relation in actual_atoms
