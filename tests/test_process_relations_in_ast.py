import pytest
import parse
from parse import process_relations_handler
from relations_structures import ModuloTerm, Relation
from typing import Union, List


def test_process_ast_of_single_equation():
    equation_ast = ['=', ['+', 'x', 'y'], 0]
    result: Relation = process_relations_handler(equation_ast)

    assert isinstance(result, Relation) 
    assert result.operation == '='
    result.ensure_canoical_form_if_equation()

    assert not (result.modulo_terms or result.modulo_term_coeficients)
    assert result.variable_names == ['x', 'y']
    assert result.variable_coeficients == [1, 1]
    assert result.absolute_part == 0


def test_process_ast_of_special_modulo_equation():
    equation_ast = ['=', ['*', 3, ['mod', 'x', 5]], 0]
    result: Relation = process_relations_handler(equation_ast)

    modulo_term = ModuloTerm(variables=('x',),
                             variable_coeficients=(1,),
                             modulo=5,
                             constant=0)           

    equation_with_modvar = Relation(variable_names=[], 
                                    variable_coeficients=[],
                                    modulo_terms=[modulo_term],
                                    modulo_term_coeficients=[3],
                                    absolute_part=0,
                                    operation='=')
    
    assert result == equation_with_modvar


def test_process_ast_of_relation_that_needs_expanding():
    equation_ast = ['=', ['+', 'x', ['mod', ['+', 'x', 1], 5]], 0]
    
    result: List[Union[str, Relation]] = process_relations_handler(equation_ast)

    assert isinstance(result, list)
    assert len(result) == 3 + 1
    assert result[0] == 'and'
    assert type(result[1]) == Relation

    result[1].ensure_canoical_form_if_equation()

    reminder_greater_than_zero, reminder_smaller_than_modulo = result[2], result[3]

    expected_original_eq = Relation(variable_names=['x', 'Mod_Var_0'],
                                    variable_coeficients=[-2, 5],
                                    modulo_terms=[],
                                    modulo_term_coeficients=[],
                                    absolute_part=1,
                                    operation='=')
    
    assert expected_original_eq == result[1] 


@pytest.mark.parametrize('ineq_ast', [
                             ['<=', ['*', 3, ['mod', 'x', 5]], 0], 
                             ['<=', ['+', 'x', ['mod', ['+', 'x', 1], 5]], 0]
                        ])
def test_inequation_gets_always_expanded(monkeypatch, ineq_ast):
    
    class mocked_fn_call(object):
        def __init__(self):
            self.called = False
        def __call__(self, *args, **kwargs):
            self.called = True

    monkeypatch.setattr(parse, 'express_modulo_terms_with_modvars', mocked_fn_call())
    monkeypatch.setattr(parse, 'ast_iter_subtrees', mocked_fn_call())

    process_relations_handler(ineq_ast)

    assert parse.express_modulo_terms_with_modvars.called
    assert not parse.ast_iter_subtrees.called


def test_process_whole_trees_simple():
    ast = [
            'assert', 
            ['not', 
                ['and', 
                    ['<=', 'x', 0], 
                    ['=', ['mod', 'x', 5], 0]]]]

    processed_tree = process_relations_handler(ast)
    relation0 = Relation(variable_names=['x'], variable_coeficients=[1], 
                         modulo_terms=[], modulo_term_coeficients=[], 
                         absolute_part=0, operation='<=')
    modulo_term = ModuloTerm(variables=('x',), variable_coeficients=(1,), modulo=5, constant=0)
    relation1 = Relation(variable_names=[], variable_coeficients=[], 
                         modulo_terms=[modulo_term], modulo_term_coeficients=[1], 
                         absolute_part=0, operation='=')
    expected_tree = ['assert', ['not', ['and', relation0, relation1]]]

    assert processed_tree == expected_tree


def test_process_whole_trees_with_expanded_modulo():
    ast = [
            'assert', 
            ['not', 
                ['and', 
                    ['<=', 'x', 0], 
                    ['=', ['+', 'x', ['mod', 'x', 5]], 0]]]]

    processed_tree = process_relations_handler(ast)
    relation0 = Relation(variable_names=['x'], variable_coeficients=[1], 
                         modulo_terms=[], modulo_term_coeficients=[], 
                         absolute_part=0, operation='<=')
    relation1 = Relation(variable_names=['x', 'Mod_Var_0'], variable_coeficients=[2, -5], 
                         modulo_terms=[], modulo_term_coeficients=[], 
                         absolute_part=0, operation='=')
    relation2 = Relation(variable_names=['x', 'Mod_Var_0'], variable_coeficients=[-1, 5], 
                         modulo_terms=[], modulo_term_coeficients=[], 
                         absolute_part=0, operation='<=')
    relation3 = Relation(variable_names=['x', 'Mod_Var_0'], variable_coeficients=[1, -5], 
                         modulo_terms=[], modulo_term_coeficients=[], 
                         absolute_part=4, operation='<=')
    
    expanded_modulo_relation_ast = ['and', relation1, relation2, relation3]

    expected_tree = ['assert', ['not', ['and', relation0, expanded_modulo_relation_ast]]]

    assert processed_tree == expected_tree
