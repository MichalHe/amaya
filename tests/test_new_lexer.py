import pytest
from smtlib_parse import lex, TokenType, Token


@pytest.fixture()
def fx_real_smtlib2_src() -> str:
    src = '''
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
    return src


def test_edge():
    assert lex('') == []


def test_real_smtlib2_tokens(fx_real_smtlib2_src: str):
    tokens = lex(fx_real_smtlib2_src)
    assert tokens

    stmt = [
        # Statement 1
        Token(TokenType.L_PAREN),
        Token(TokenType.IDENTIF, 'set-info'),
        Token(TokenType.COLON),
        Token(TokenType.IDENTIF, 'smt-lib-version'),
        Token(TokenType.IDENTIF, '2.6'),
        Token(TokenType.R_PAREN),

        # Statement 2
        Token(TokenType.L_PAREN),
        Token(TokenType.IDENTIF, 'set-logic'),
        Token(TokenType.IDENTIF, 'LIA'),
        Token(TokenType.R_PAREN),

        Token(TokenType.L_PAREN),
        Token(TokenType.IDENTIF, 'set-info'),
        Token(TokenType.COLON),
        Token(TokenType.IDENTIF, 'source'),
        Token(TokenType.QUOTED_SYMBOL, None),
        Token(TokenType.R_PAREN),
    ]

    for i, tk in enumerate(stmt):
        assert tokens[i].type == tk.type
        if tk.type == TokenType.IDENTIF:
            assert tk.contents == tokens[i].contents
        if tk.type == TokenType.QUOTED_SYMBOL:
            print(tokens[i])