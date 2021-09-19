import pytest

import parse
from parse import replace_modulo_with_exists_handler


def test_spectial_form_equation_not_expanded(monkeypatch):
    equation = ['=', ['mod', 'x', 10], 5]

    def mocked_replace_modulo_operators_in_expr(*args, **kwargs):
        assert False

    monkeypatch.setattr(parse, 'replace_modulo_operators_in_expr', mocked_replace_modulo_operators_in_expr)

    replace_modulo_with_exists_handler(equation, is_reeval=False, ctx={})


def test_ordinary_form_equation_gets_expanded():
    equation_ast = ['=', ['+', ['mod', 'x', '10'], 'y'], '10']

    ctx = {'modulos_replaced_cnt': 0}
    replace_modulo_with_exists_handler(equation_ast, is_reeval=False, ctx=ctx)
    reminder_fragment = ['-', 'x', ['*', 'Mod_Var_0', '10']]
    expected_result_ast = [
            'exists', 
            [['Mod_Var_0', 'Int']], 
            ['and', 
                ['=', ['+', reminder_fragment, 'y'], '10'],  # Original formula with modvar
                ['<=', 0, reminder_fragment],  # Limit on modulo value
                ['<=', reminder_fragment, '9']]]  # Limit on modulo value
    assert ctx['modulos_replaced_cnt'] == 1
    assert expected_result_ast == equation_ast
