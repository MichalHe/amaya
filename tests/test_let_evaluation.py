from amaya.ast_definitions import AST_Node
from amaya.preprocessing import expand_let_macros

import pytest


def test_simple_let_folding():
    ast = ['let', [['T', ['=', 'x', '0']]], 'T']
    ast_with_macros_folded = expand_let_macros(ast, [])
    expected_ast = ['=', 'x', '0']

    assert ast_with_macros_folded == expected_ast


def test_nested_let_expressions():
    ast = ['let', [['B0', ['<=', 'x', '0']]], ['let', [['B1', ['=', 'x', '0']]], ['and', 'B0', 'B1']]]
    ast_with_macros_folded = expand_let_macros(ast, [])
    expected_ast = ['and', ['<=', 'x', '0'], ['=', 'x', '0']]

    assert ast_with_macros_folded == expected_ast

    ast = ['let', [['B0', ['<=', 'x', '0']]], ['let', [['B0', ['=', 'x', '0']]], ['and', 'B0', 'B1']]]
    ast_with_macros_folded = expand_let_macros(ast, [])
    expected_ast = ['and', ['=', 'x', '0'], 'B1']

    assert ast_with_macros_folded == expected_ast


def test_simple_let_term_with_ite():
    ast = ['let', [['T0', ['<=', ['ite', 'b0', 'x', ['*', '2', 'x']], 1]]], ['and', 'T0', ['<=', 'x', '2']]]
    ast_with_macros_folded = expand_let_macros(ast, [])
    expected_ast = ['and', ['<=', ['ite', 'b0', 'x', ['*', '2', 'x']], 1], ['<=', 'x', '2']]

    assert ast_with_macros_folded == expected_ast

    ast = ['let', [['B0', 'B1'], ['T0', 'T1']], ['ite', ['not', 'B0'], 'T0', 'X0']]
    ast_with_macros_folded = expand_let_macros(ast, [])
    expected_ast = ['ite', ['not', 'B1'], 'T1', 'X0']
