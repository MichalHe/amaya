from typing import Optional

from amaya.ast_definitions import AST_Node
from amaya.relations_structures import Relation
from amaya.preprocessing.antiprenexing import perform_antiprenexing


def find_ast_difference(ast1: AST_Node, ast2: AST_Node) -> Optional[str]:
    """Perform AST comparison, respecting commutativity of some nodes."""
    if type(ast1) != type(ast2):
        return f'Parts of ASTs differ in type: {ast1=} {ast2=}'

    if isinstance(ast1, str) and ast1 != ast2:
        return f'AST leaves do not match: {ast1=} {ast2=}'

    if isinstance(ast1, Relation):
        if ast1 != ast2:
            return f'AST leaves (reletions) differ: {ast1=} {ast2=}'
        else:
            return None

    ast1_root_type = ast1[0]
    ast2_root_type = ast2[0]

    if ast1_root_type != ast2_root_type:
        return f'Parts of ASTs differ (different root type): {ast1=} {ast2=}'

    if len(ast1) != len(ast2):
        return f'Parts of ASTs differ (different number of subtrees): {ast1=} {ast2=}'

    if ast1_root_type in ('and', 'or'):
        # Handle the fact that nodes are commutative
       unmatched_ast2_subtree_indices = set(i + 1 for i in range(len(ast2) - 1))
       for ast1_subtree in ast1[1:]:

           # Search for a matching subtree in ast2
           ast2_subtree_match_index = -1
           for ast2_subtree_index in unmatched_ast2_subtree_indices:
               ast2_subtree = ast2[ast2_subtree_index]
               if not find_ast_difference(ast1_subtree, ast2_subtree):
                   ast2_subtree_match_index = ast2_subtree_index
                   break
           if ast2_subtree_match_index == -1:
               return (f'ASTs differ due different subtrees: {ast1=} {ast2=} \n',
                       f'ast2 does not have {ast1_subtree}')
           else:
               unmatched_ast2_subtree_indices.remove(ast2_subtree_match_index)
    return None

    if ast1_root_type in ('not',):
        return find_ast_difference(ast1[1], ast1[2])

    raise ValueError(f'Don\'t know how to compare ast of type: {ast1_root_type}')


def test_simple():
    relation_with_x = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                                absolute_part=0, predicate_symbol='=')
    relation_without_x = Relation.new_lin_relation(variable_names=['y'], variable_coefficients=[1],
                                                   absolute_part=0, predicate_symbol='=')
    formula = ['exists', [['x', 'Int']], ['and', relation_with_x, relation_without_x]]

    expected_result = ['and', ['exists', [['x', 'Int']], relation_with_x], relation_without_x]
    actual_result = perform_antiprenexing(formula)

    ast_difference = find_ast_difference(actual_result, expected_result)
    assert not ast_difference


def test_no_quantifiers():
    relation = Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1],
                                         absolute_part=0, predicate_symbol='=')

    ast = ['or', ['and', relation, relation], ['not', relation]]

    assert not find_ast_difference(ast, perform_antiprenexing(ast))
