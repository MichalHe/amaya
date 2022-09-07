from typing import List

from amaya import parse, preprocessing, utils
from amaya.tokenize import tokenize

import pytest


@pytest.fixture
def smt_formula():
    source_text = '''
    (set-info :category "industrial")
    (set-info :status unsat)
    (assert (not (exists ((?X Int)) (<= 2 ?X))))
    (check-sat)
    (exit)
    '''
    return source_text


def test_lex(smt_formula: str):
    actual_tokens = list(tokenize(smt_formula))
    expected_tokens = ['(', 'set-info', ':category', 'industrial', ')']
    expected_tokens += ['(', 'set-info', ':status', 'unsat', ')']
    expected_tokens += ['(', 'assert', '(', 'not', '(', 'exists', '(', '(', '?X', 'Int', ')', ')', '(', '<=', '2', '?X', ')', ')', ')', ')']
    expected_tokens += ['(', 'check-sat', ')']
    expected_tokens += ['(', 'exit', ')']

    assert actual_tokens == expected_tokens


def test_parse(smt_formula: str):
    tokens = tokenize(smt_formula)
    ast = parse.build_syntax_tree(tokens)
    expected_ast = [
        ['set-info', ':category', 'industrial'],
        ['set-info', ':status', 'unsat'],
        ['assert', ['not', ['exists', [['?X', 'Int']], ['<=', '2', '?X']]]],
        ['check-sat'],
        ['exit'],
    ]

    assert ast == expected_ast
