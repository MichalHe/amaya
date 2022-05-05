"""
Division term syntax: (div <expr> <constexpr>)
"""
from functools import partial
from typing import (
    Union,
)

from amaya.ast_definitions import AST_Node
from amaya.ast_relations import extract_relation
from amaya.relations_structures import (
    DivTerm,
    ModuloTerm,
    NonlinearTermReplacementInfo,
    Relation,
)
from amaya.preprocessing import reduce_relation_asts_to_evaluable_leaves

import pytest

def negate(coefs):
    return [-coef for coef in coefs]

@pytest.mark.parametrize(
    ('relation_ast', 'expected_relation'),
    (
        (
            ['=', ['div', 'y', '10'], 3],
            Relation(variable_names=[], variable_coeficients=[], modulo_terms=[], modulo_term_coeficients=[],
                     div_terms=[DivTerm(variables=('y',), variable_coeficients=(1,), divisor=10, constant=0)],
                     div_term_coeficients=[1], operation='=', absolute_part=3)
        ),
        (
            ['<=', ['+', ['*', '2', ['div', 'y', '10']], ['div', 'y', '10']], 0],
            Relation(variable_names=[], variable_coeficients=[], modulo_terms=[], modulo_term_coeficients=[],
                     div_terms=[DivTerm(variables=('y',), variable_coeficients=(1,), divisor=10, constant=0)],
                     div_term_coeficients=[2], operation='<=', absolute_part=0)
        ),
        (
            ['<=', ['div', 'y', 'x'], 0],
            ValueError
        ),
        (
            ['<=', ['div', 'y', ['div', 'x', '10']], 0],
            ValueError
        )
    )
)
def test_relation_extraction_with_div(relation_ast: AST_Node, expected_relation: Union[Relation, ValueError]):
    """Check that (div) terms are recognized when extracting relations from the given SMT source."""
    if isinstance(expected_relation, Relation):
        relation = extract_relation(relation_ast)
        if expected_relation.operation == '=':
            # Handle normalized equations having different signs
            absolute_part_matches_expected_sign = (
                (expected_relation.absolute_part > 0) == (relation.absolute_part > 0)
            )
            if absolute_part_matches_expected_sign:
                assert relation == expected_relation
            else:
                assert relation.div_terms
                relation.absolute_part = -relation.absolute_part
                relation.variable_coeficients = negate(relation.variable_coeficients)
                relation.modulo_term_coeficients = negate(relation.modulo_term_coeficients)
                relation.div_term_coeficients = negate(relation.div_term_coeficients)
                assert relation == expected_relation
    else:
        with pytest.raises(ValueError):
            relation = extract_relation(relation_ast)


def test_reduce_ast_to_evaluable_leaves():
    ast = ['<=', ['div', ['*', 2, 'y'], '10'], '0']
    reduced_ast = reduce_relation_asts_to_evaluable_leaves(ast, set())
    LinRelation = partial(Relation, modulo_terms=[], modulo_term_coeficients=[], div_terms=[], div_term_coeficients=[])
    CongruenceRelation = partial(Relation, div_terms=[], div_term_coeficients=[], operation='=',
                                 variable_names=[], variable_coeficients=[])
    expected_ast = [
        'exists', [['DivVar0', 'Int']],
        [
            'and',
            LinRelation(variable_names=['DivVar0'], variable_coeficients=[1], operation='<=', absolute_part=0),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coeficients=[10, -2], operation='<=', absolute_part=0),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coeficients=[-10, 2], operation='<=', absolute_part=9),
        ]
    ]

    assert reduced_ast == expected_ast

    ast = ['<=', ['+', ['div', 'y', '10'], ['mod', 'y', '11']], 1]
    reduced_ast = reduce_relation_asts_to_evaluable_leaves(ast, set())
    congruence_mod_term = ModuloTerm(variables=('ModVar0', 'y'), variable_coeficients=(-1, 1), constant=0, modulo=11)
    expected_ast = [
        'exists', [['DivVar0', 'Int'], ['ModVar0', 'Int']],
        [
            'and',
            LinRelation(variable_names=['DivVar0', 'ModVar0'], variable_coeficients=[1, 1], operation='<=', absolute_part=1),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coeficients=[10, -1], operation='<=', absolute_part=0),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coeficients=[-10, 1], operation='<=', absolute_part=9),
            LinRelation(variable_names=['ModVar0'], variable_coeficients=[-1], operation='<=', absolute_part=0),
            LinRelation(variable_names=['ModVar0'], variable_coeficients=[1], operation='<=', absolute_part=10),
            CongruenceRelation(modulo_terms=[congruence_mod_term], modulo_term_coeficients=[1], absolute_part=0),
        ]
    ]

    assert reduced_ast[2] == expected_ast[2]



def test_div_replacement_inside_relation():
    mod_terms = [
        ModuloTerm(variables=('m0', ), variable_coeficients=(1, ), constant=0, modulo=13),
        ModuloTerm(variables=('m1', 'm2'), variable_coeficients=(1, 2), constant=0, modulo=10),
    ]

    div_terms = [
        DivTerm(variables=('d0', ), variable_coeficients=(1, ), constant=0, divisor=3),
        DivTerm(variables=('d1', 'd2'), variable_coeficients=(3, 4), constant=0, divisor=4),
    ]

    relation = Relation(variable_coeficients=[1], variable_names=['x'],
                        modulo_terms=mod_terms, modulo_term_coeficients=[1, 2],
                        div_terms=div_terms, div_term_coeficients=[3, 4],
                        absolute_part=10, operation='<')

    replaced_relation, mod_replacements, div_replacements = relation.replace_nonlinear_terms_with_variables()

    exp_relation = Relation(
        variable_names=['DivVar0', 'DivVar1', 'ModVar0', 'ModVar1', 'x'], variable_coeficients=[3, 4, 1, 2, 1],
        modulo_terms=[], modulo_term_coeficients=[], div_terms=[], div_term_coeficients=[],
        absolute_part=10, operation='<')

    assert replaced_relation == exp_relation

    exp_div_replacements = [
        NonlinearTermReplacementInfo(term=div_terms[0], variable='DivVar0'),
        NonlinearTermReplacementInfo(term=div_terms[1], variable='DivVar1'),
    ]
    assert div_replacements == exp_div_replacements

    exp_mod_replacements = [
        NonlinearTermReplacementInfo(term=mod_terms[0], variable='ModVar0'),
        NonlinearTermReplacementInfo(term=mod_terms[1], variable='ModVar1'),
    ]
    assert mod_replacements == exp_mod_replacements
