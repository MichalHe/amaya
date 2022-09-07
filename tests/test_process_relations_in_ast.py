from typing import (
    List,
    Union,
)

from amaya.preprocessing import condense_relation_asts_to_relations
from amaya.relations_structures import (
    ModuloTerm,
    Relation
)

import pytest


def test_condense_simple_equation_ast():
    equation_ast = ['=', ['+', 'x', 'y'], 0]
    result: Relation = condense_relation_asts_to_relations(equation_ast, bool_fn_symbols=set())
    expected_result = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                                predicate_symbol='=', absolute_part=0)
    assert result == expected_result


def test_condense_congruence():
    equation_ast = ['=', ['*', 3, ['mod', 'x', 5]], 0]
    result: Relation = condense_relation_asts_to_relations(equation_ast, bool_fn_symbols=set())

    modulo_term = ModuloTerm(variables=('x',), variable_coefficients=(1,),
                             modulo=5, constant=0)

    expected_congruence = Relation.new_congruence_relation(modulo_terms=[modulo_term],
                                                           modulo_term_coefficients=[3],
                                                           absolute_part=0)

    assert result == expected_congruence


def test_relation_ast_condensation_on_rich_ast():
    ast = [
            'assert',
            ['not',
                ['and',
                    ['<=', 'x', 0],
                    ['=', ['mod', 'x', 5], 0]]]]

    ast_with_relations_condensed = condense_relation_asts_to_relations(ast, bool_fn_symbols=set())

    relation0 = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                          absolute_part=0, predicate_symbol='<=')
    modulo_term = ModuloTerm(variables=('x',), variable_coefficients=(1,), modulo=5, constant=0)
    relation1 = Relation.new_congruence_relation(modulo_terms=[modulo_term], modulo_term_coefficients=[1],
                                                 absolute_part=0)
    expected_ast = ['assert', ['not', ['and', relation0, relation1]]]

    assert ast_with_relations_condensed == expected_ast


def test_relation_ast_condensation_on_rich_ast_with_modulo_terms():
    ast = [
            'assert',
            ['not',
                ['and',
                    ['<=', 'x', 0],
                    ['=', ['+', 'x', ['mod', 'x', 5]], 0]]]]

    ast_with_relations_condensed = condense_relation_asts_to_relations(ast, bool_fn_symbols=set())
    relation0 = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                          absolute_part=0, predicate_symbol='<=')
    
    mod_term = ModuloTerm(variables=('x', ), variable_coefficients=(1, ), modulo=5, constant=0)
    relation1 = Relation(variable_names=['x'], variable_coefficients=[1],
                         modulo_terms=[mod_term], modulo_term_coefficients=[1],
                         div_terms=[], div_term_coefficients=[],
                         absolute_part=0, predicate_symbol='=')

    expected_result = ['assert', ['not', ['and', relation0, relation1]]]

    assert ast_with_relations_condensed == expected_result
