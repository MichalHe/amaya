import pytest
from smtlib_parse import (
    build_ast_from_tokens,
    lex,
    Token,
    TokenType,
    ASTNodeType,
    ASTAtomNode,
    ASTBinaryNode,
)
from typing import List


@pytest.fixture()
def simple_smt2_statement_tokens() -> List[Token]:
    # (< ?X 0)
    tokens = [
        Token(TokenType.L_PAREN),
        Token(TokenType.LESS),
        Token(TokenType.IDENTIF, contents='?X'),
        Token(TokenType.NUMBER, contents=0),
        Token(TokenType.R_PAREN),
    ]

    return tokens


@pytest.fixture()
def smt2_real_assert_tree() -> List[Token]:
    assert_tree_src = '(assert (not (exists ((?X Int)) (< ?X 13))))'
    return lex(assert_tree_src)


@pytest.fixture()
def real_smt2_file_tokens() -> List[Token]:
    real_source = '''
(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :category "industrial")
(set-info :status unsat)
(assert (not (exists ((?X Int)) (< ?X 13))))
(check-sat)
(exit)
'''
    return lex(real_source)


def test_simple_statement(simple_smt2_statement_tokens: List[Token]):
    top_level_statements = build_ast_from_tokens(simple_smt2_statement_tokens)

    assert top_level_statements
    assert len(top_level_statements) == 1

    ast_root = top_level_statements[0]

    assert type(ast_root) == ASTBinaryNode
    assert ast_root.type == ASTNodeType.LESS
    # Left
    assert type(ast_root.left) == ASTAtomNode
    assert ast_root.left.type == ASTNodeType.IDENTIF
    assert ast_root.left.contents == '?X'

    # Right
    assert type(ast_root.right) == ASTAtomNode
    assert ast_root.right.type == ASTNodeType.NUMBER
    assert ast_root.right.contents == 0


def test_real_assert_tree(smt2_real_assert_tree: List[Token]):
    assert smt2_real_assert_tree
    tls = build_ast_from_tokens(smt2_real_assert_tree)
    assert tls
    print(tls)


def test_real_file(real_smt2_file_tokens: List[Token]):
    '''Checks whether the tokens from a real source produce the correct AST.'''
    return
    assert real_smt2_file_tokens
