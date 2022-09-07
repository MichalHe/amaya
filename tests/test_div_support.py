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
from amaya.preprocessing import rewrite_relations_with_mod_and_div_terms_to_evaluable_atoms

import pytest


def negate(coefs):
    return [-coef for coef in coefs]


@pytest.mark.parametrize(
    ('relation_ast', 'expected_relation'),
    (
        (
            ['=', ['div', 'y', '10'], 3],
            Relation(variable_names=[], variable_coefficients=[], modulo_terms=[], modulo_term_coefficients=[],
                     div_terms=[DivTerm(variables=('y',), variable_coefficients=(1,), divisor=10, constant=0)],
                     div_term_coefficients=[1], predicate_symbol='=', absolute_part=3)
        ),
        (
            ['<=', ['+', ['*', '2', ['div', 'y', '10']], ['div', 'y', '10']], 0],
            Relation(variable_names=[], variable_coefficients=[], modulo_terms=[], modulo_term_coefficients=[],
                     div_terms=[DivTerm(variables=('y',), variable_coefficients=(1,), divisor=10, constant=0)],
                     div_term_coefficients=[2], predicate_symbol='<=', absolute_part=0)
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
        if expected_relation.predicate_symbol == '=':
            # Handle normalized equations having different signs
            absolute_part_matches_expected_sign = (
                (expected_relation.absolute_part > 0) == (relation.absolute_part > 0)
            )
            if absolute_part_matches_expected_sign:
                assert relation == expected_relation
            else:
                assert relation.div_terms
                relation.absolute_part = -relation.absolute_part
                relation.variable_coefficients = negate(relation.variable_coefficients)
                relation.modulo_term_coefficients = negate(relation.modulo_term_coefficients)
                relation.div_term_coefficients = negate(relation.div_term_coefficients)
                assert relation == expected_relation
    else:
        with pytest.raises(ValueError):
            relation = extract_relation(relation_ast)


def test_reduce_ast_to_evaluable_leaves():
    div_term = DivTerm(variables=('y', ), variable_coefficients=(2, ), divisor=10, constant=0)
    ineq_with_div_term = Relation(variable_names=[], variable_coefficients=[], modulo_terms=[], modulo_term_coefficients=[],
                                  div_terms=[div_term], div_term_coefficients=[1], absolute_part=0, predicate_symbol='<=')
    
    rewritten_ast = rewrite_relations_with_mod_and_div_terms_to_evaluable_atoms(ineq_with_div_term)

    LinRelation = partial(Relation, modulo_terms=[], modulo_term_coefficients=[], div_terms=[], div_term_coefficients=[])
    CongruenceRelation = partial(Relation, div_terms=[], div_term_coefficients=[], predicate_symbol='=',
                                 variable_names=[], variable_coefficients=[])
    expected_ast = [
        'exists', [['DivVar0', 'Int']],
        [
            'and',
            LinRelation(variable_names=['DivVar0'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=0),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coefficients=[10, -2], predicate_symbol='<=', absolute_part=0),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coefficients=[-10, 2], predicate_symbol='<=', absolute_part=9),
        ]
    ]

    assert rewritten_ast == expected_ast

    div_term = DivTerm(variables=('y', ), variable_coefficients=(1, ), divisor=10, constant=0)
    mod_term = ModuloTerm(variables=('y', ), variable_coefficients=(1, ), modulo=11, constant=0)
    ineq_with_mixed_term = Relation(variable_names=[], variable_coefficients=[], modulo_terms=[mod_term], modulo_term_coefficients=[1],
                                    div_terms=[div_term], div_term_coefficients=[1], absolute_part=1, predicate_symbol='<=')

    reduced_ast = rewrite_relations_with_mod_and_div_terms_to_evaluable_atoms(ineq_with_mixed_term)
    congruence_mod_term = ModuloTerm(variables=('ModVar0', 'y'), variable_coefficients=(-1, 1), constant=0, modulo=11)
    expected_ast = [
        'exists', [['DivVar0', 'Int'], ['ModVar0', 'Int']],
        [
            'and',
            LinRelation(variable_names=['DivVar0', 'ModVar0'], variable_coefficients=[1, 1], predicate_symbol='<=', absolute_part=1),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coefficients=[10, -1], predicate_symbol='<=', absolute_part=0),
            LinRelation(variable_names=['DivVar0', 'y'], variable_coefficients=[-10, 1], predicate_symbol='<=', absolute_part=9),
            LinRelation(variable_names=['ModVar0'], variable_coefficients=[-1], predicate_symbol='<=', absolute_part=0),
            LinRelation(variable_names=['ModVar0'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=10),
            CongruenceRelation(modulo_terms=[congruence_mod_term], modulo_term_coefficients=[1], absolute_part=0),
        ]
    ]

    assert reduced_ast[2] == expected_ast[2]



def test_div_replacement_inside_relation():
    mod_terms = [
        ModuloTerm(variables=('m0', ), variable_coefficients=(1, ), constant=0, modulo=13),
        ModuloTerm(variables=('m1', 'm2'), variable_coefficients=(1, 2), constant=0, modulo=10),
    ]

    div_terms = [
        DivTerm(variables=('d0', ), variable_coefficients=(1, ), constant=0, divisor=3),
        DivTerm(variables=('d1', 'd2'), variable_coefficients=(3, 4), constant=0, divisor=4),
    ]

    relation = Relation(variable_coefficients=[1], variable_names=['x'],
                        modulo_terms=mod_terms, modulo_term_coefficients=[1, 2],
                        div_terms=div_terms, div_term_coefficients=[3, 4],
                        absolute_part=10, predicate_symbol='<')

    replaced_relation, mod_replacements, div_replacements = relation.replace_nonlinear_terms_with_variables()

    exp_relation = Relation(
        variable_names=['DivVar0', 'DivVar1', 'ModVar0', 'ModVar1', 'x'], variable_coefficients=[3, 4, 1, 2, 1],
        modulo_terms=[], modulo_term_coefficients=[], div_terms=[], div_term_coefficients=[],
        absolute_part=10, predicate_symbol='<')

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
