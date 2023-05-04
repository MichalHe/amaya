from typing import List
from amaya.preprocessing.eval import Expr, NonlinTerm, NonlinTermGraph, NonlinTermType, _convert_ast_into_evaluable_form, normalize_expr
from amaya.relations_structures import (
    Congruence,
    ModuloTerm,
    Relation,
)
from amaya.preprocessing import rewrite_nonlinear_terms

import pytest


def make_ineq(vars: List[str], coefs: List[int], rhs: int) -> Relation:
    return Relation.new_lin_relation(variable_names=vars, variable_coefficients=coefs,
                                     absolute_part=rhs, predicate_symbol='<=')


def make_eq(vars: List[str], coefs: List[int], rhs: int) -> Relation:
    return Relation.new_lin_relation(variable_names=vars, variable_coefficients=coefs,
                                     absolute_part=rhs, predicate_symbol='=')


def make_congruence(vars: List[str], coefs: List[int], modulus: int, rhs: int) -> Congruence:
    return Congruence(vars=vars, coefs=coefs, rhs=rhs, modulus=modulus)


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


def test_expr_rewriting_with_nonlinear_terms1():
    ast = ['*', ['mod', ['mod', 'x', '3'], '4'], '2']
    graph = NonlinTermGraph()
    result, deps, support = normalize_expr(ast, graph)

    root_term = NonlinTerm(lin_terms=(('x', 1), ), type=NonlinTermType.MOD, nonlin_constant=3)
    root_term_node = graph.term_nodes[root_term]

    dep_term = NonlinTerm(lin_terms=((root_term_node.var, 1), ), type=NonlinTermType.MOD, nonlin_constant=4)
    dep_term_node = graph.term_nodes[dep_term]

    assert deps == {dep_term_node}
    assert result == Expr(linear_terms={dep_term_node.var: 2})
    assert root_term_node.dependent_terms == {dep_term_node}

    assert support == {'x', root_term_node.var, dep_term_node.var}


def test_expr_rewriting_with_nonlinear_terms2():
    ast = ['+', ['mod', ['div', 'x', '3'], '4'], ['div', ['mod', ['*', 'y', '2'], '10'], '6'], '11']
    graph = NonlinTermGraph()
    result, deps, support = normalize_expr(ast, graph)

    root_term1 = NonlinTerm(lin_terms=(('x', 1), ), type=NonlinTermType.DIV, nonlin_constant=3)
    root_term2 = NonlinTerm(lin_terms=(('y', 2), ), type=NonlinTermType.MOD, nonlin_constant=10)

    root1_node = graph.term_nodes[root_term1]
    root2_node = graph.term_nodes[root_term2]

    assert len(deps) == 2

    assert len(root1_node.dependent_terms) == 1
    dependent_node1 = next(iter(root1_node.dependent_terms))
    assert dependent_node1.body == NonlinTerm(lin_terms=((root1_node.var, 1),), type=NonlinTermType.MOD, nonlin_constant=4)

    assert len(root2_node.dependent_terms) == 1
    dependent_node2 = next(iter(root2_node.dependent_terms))
    assert dependent_node2.body == NonlinTerm(lin_terms=((root2_node.var, 1),), type=NonlinTermType.DIV, nonlin_constant=6)

    assert deps == {dependent_node1, dependent_node2}
    assert result == Expr(constant_term=11, linear_terms={dependent_node1.var: 1, dependent_node2.var: 1})
    assert support == {'x', 'y', dependent_node1.var, dependent_node2.var, root1_node.var, root2_node.var}


@pytest.mark.parametrize(
    ('input_ast', 'expected_result'),
    [
        (['<=', 'x', '3'], make_ineq(['x'], [1], 3)),
        (['<=', ['*', 'x', '3'], '1'], make_ineq(['x'], [3], 1)),
        (['<=', ['-', ['*', 'x', '3'], ['-', 'y']], '1'], make_ineq(['x', 'y'], [3, 1], 1)),
        (['=', ['-', ['*', 'x', '3'], ['-', 'y']], '1'], make_eq(['x', 'y'], [3, 1], 1)),
        (['<=', ['+', ['*', 'x', '3'], '1'], '0'], make_ineq(['x'], [3], -1)),
    ])
def test_convert_relation_into_evaluable_form(input_ast, expected_result):
    graph = NonlinTermGraph()
    result, ast_info = _convert_ast_into_evaluable_form(input_ast, graph, set())
    assert result == expected_result


def test_convert_relation_into_evaluable_form_with_mod_terms():
    ast = ['<=', ['*', '7', ['mod', 'x', '3']], '4']
    graph = NonlinTermGraph()
    result, ast_info = _convert_ast_into_evaluable_form(ast, graph, set())

    assert len(graph.term_nodes) == 1
    var = next(iter(graph.term_nodes.values())).var
    assert result == make_ineq([var], [7], 4)


def test_convert_relation_into_evaluable_form_with_nested_mod_terms():
    ast = ['<=', ['div', ['mod', 'x', '3'], '5'], '4']
    graph = NonlinTermGraph()
    result, ast_info = _convert_ast_into_evaluable_form(ast, graph, set())

    assert len(graph.term_nodes) == 2

    root = next(iter(graph.index['x']))
    dep = next(iter(root.dependent_terms))

    assert result == make_ineq([dep.var], [1], 4)


def test_term_dropping():
    ast = ['exists', [['x', 'Int']], ['<=', ['mod', 'x', '3'], '0']]
    graph = NonlinTermGraph()
    result, ast_info = _convert_ast_into_evaluable_form(ast, graph, set())

    var = next(iter(graph.term_nodes.values())).var

    assert isinstance(result, list)
    assert result[0] == 'exists'
    assert result[1] == [['x', 'Int'], [var, 'Int']]
    assert isinstance(result[2], list)
    assert result[2][0] == 'and'

    atoms = result[2][1:]
    assert len(atoms) == 4

    assert make_ineq([var], [1], 0) in atoms
    assert make_ineq([var], [-1], 0) in atoms
    assert make_ineq([var], [1], 2) in atoms
    assert make_congruence([var, 'x'], [-1, 1], 3, 0) in atoms


def assert_commutative_nodes_eq(actual, expected):
    """Assert the equality of nodes regardless of children order."""
    assert type(actual) == type(expected)

    if isinstance(actual, str):
        assert actual == expected

    assert actual[0] == expected[0]
    actual_children, expected_children = actual[1:], expected[1:]
    assert len(actual_children)  == len(expected_children)

    for actual_child in actual_children:
        assert actual_child in expected_children


def test_term_dropping2():
    ast = ['exists', [['x', 'Int']], ['<=', ['mod', ['div', 'x', '3'], '5'], '0']]
    graph = NonlinTermGraph()
    result, ast_info = _convert_ast_into_evaluable_form(ast, graph, set())

    div_node = next(iter(graph.index['x']))
    div_var = div_node.var
    mod_var = next(iter(div_node.dependent_terms)).var

    assert isinstance(result, list)
    assert result[0] == 'exists'

    assert_commutative_nodes_eq(result[1], [['x', 'Int'], [div_var, 'Int'], [mod_var, 'Int']])

    assert isinstance(result[2], list)
    assert result[2][0] == 'and'
    atoms = result[2][1:]

    expected_atoms = [
        make_ineq([mod_var], [1], 0),   # original inequation
        make_ineq([mod_var], [-1], 0),  # lower bound on mod
        make_ineq([mod_var], [1], 4),   # upper bound on mod
        make_congruence([div_var, mod_var], [1, -1], 5, 0), # mod var is a reminder
        make_ineq([div_var, 'x'], [3, -1], 0), # x - 3*div_var lower bound (reminder)
        make_ineq([div_var, 'x'], [-3, 1], 2), # x - 3*div_var upper bound (reminder)
    ]

    assert_commutative_nodes_eq(atoms, expected_atoms)