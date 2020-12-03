import pytest  # noqa
from smt_tools import translate_smtformula_to_human_readable
from parse import lex, build_syntax_tree


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
    formula = build_syntax_tree(lex(formula_src))[0]

    converted = translate_smtformula_to_human_readable(formula).replace(' ', '')
    expected = '¬(∃X,Y(∀Z(((X+Y<=0)∧(-Z>0)))))'

    # print(formula_src)
    # print('Human readable:', converted)

    assert converted == expected
