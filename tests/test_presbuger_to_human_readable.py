from amaya.parse import build_syntax_tree
from amaya.tokenize import tokenize
from smt_tools import translate_smtformula_to_human_readable

import pytest


formula_src = '''
(not
    (exists
        ((X Int) (Y Int))
        (forall
            ((Z Int))
            (and
                (<= (+ X Y) 0)
                (> (- Z) 0)))))
'''


def test_convert_smtformula_to_human_readable():
    formula = build_syntax_tree(tokenize(formula_src))[0]

    converted = translate_smtformula_to_human_readable(formula).replace(' ', '')
    expected = '¬(∃X,Y(∀Z(((X+Y<=0)∧(-Z>0)))))'

    assert converted == expected
