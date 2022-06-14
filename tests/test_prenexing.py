from amaya.preprocessing.prenexing import (
    PrenexingContext,
    convert_formula_to_pnf
)

import pytest


def test_prenexing_simple():
    ast = ['and', ['exists', [['X', 'Int']], 'phi'], 'psi']
    result = convert_formula_to_pnf(ast)
    assert result == ['exists', [['X', 'Int']], ['and', 'phi', 'psi']]


def test_prenexing_simple_deeper():
    ast = ['and', ['and', ['exists', [['X', 'Int']], 'phi'], 'eta'], 'psi']
    result = convert_formula_to_pnf(ast)
    assert result == ['exists', [['X', 'Int']], ['and', ['and', 'phi', 'eta'], 'psi']]


def test_prenexing_multiple_quantifiers_simple():
    ast = ['and', ['exists', [['X', 'Int']], 'phi'], ['not', ['exists', [['Y', 'Int']], 'eta']]]
    result = convert_formula_to_pnf(ast)
    assert result == ['exists', 
                      [['X', 'Int']], 
                      ['forall', [['Y', 'Int']], 
                      ['and', 'phi', ['not', 'eta']]]]
    

    ast = ['and', ['not', ['exists', [['Y', 'Int']], 'eta']], ['exists', [['X', 'Int']], 'phi']]
    result = convert_formula_to_pnf(ast)
    assert result == ['forall', [['Y', 'Int']], ['exists', [['X', 'Int']], ['and', ['not', 'eta'], 'phi']]]


def test_prenexing_moving_quantifiers_through_negation():
    ast = ['not', ['exists', [['X', 'Int']], 'phi']]
    result = convert_formula_to_pnf(ast)
    assert result == ['forall', [['X', 'Int']], ['not', 'phi']]
    
    ast = ['not', ['not', ['exists', [['X', 'Int']], 'phi']]]
    result = convert_formula_to_pnf(ast)
    assert result == ['exists', [['X', 'Int']], ['not', ['not', 'phi']]]
