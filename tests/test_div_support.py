"""
Division term syntax: (div <expr> <constexpr>)
"""
from typing import (
    Union,
)

from amaya.ast_relations import extract_relation
from amaya.relations_structures import (
    DivTerm,
    Relation,
)
from amaya.ast_definitions import AST_Node

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
