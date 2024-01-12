from __future__ import annotations

from dataclasses import dataclass, field
import copy
from typing import (
    Any,
    Dict,
    List,
    Set,
    Union,
    Tuple,
)

from amaya.relations_structures import (
    AST_NaryNode,
    AST_Node,
    Frozen_AST,
    NodeEncounteredHandlerStatus,
    Raw_AST,
    Relation,
)
from amaya.utils import number_to_bit_tuple


def freeze_ast_node(ast_node: Raw_AST) -> Frozen_AST:
    if isinstance(ast_node, (str, int)):
        return ast_node

    ret = tuple(freeze_ast_node(node) for node in ast_node)
    return ret  # type: ignore


def unfreeze_ast_node(ast_node: Raw_AST) -> AST_With_Placeholders:
    if isinstance(ast_node, (str, int)):
        return ast_node

    ret = [unfreeze_ast_node(node) for node in ast_node]
    return ret  # type: ignore


@dataclass
class ConditionTable:
    """Table of all ite control conditions seen in an AST."""
    value: int = 0
    conditions: Dict[Any, int] = field(default_factory=dict)

    def fetch_and_add(self) -> int:
        ret = self.value
        self.value += 1
        return ret

    def store_condition(self, raw_condition: Raw_AST) -> int:
        condition = freeze_ast_node(raw_condition)
        if condition in self.conditions:
            return self.conditions[condition]

        cond_id = len(self.conditions)
        self.conditions[condition] = cond_id
        return cond_id


AST_With_Placeholders = Raw_AST

PlaceholderInfo = Tuple[int, AST_With_Placeholders]
"""Information about what a placeholder (int) stands for (node)"""


def mark_and_collect_ite_conditions(ast: Raw_AST, cond_table: ConditionTable) -> AST_With_Placeholders:
    """Return a list of ite conditions found in the given tree. All conditions founnd in the tree are assigned a unique integer. """
    if not isinstance(ast, list):
        return ast

    node_type = ast[0]
    if node_type == 'ite':
        assert len(ast) == 4, 'if-then-else expressions should have the form of (ite <condition> <positive_branch> <negative_branch>)'
        condition = ast[1]

        positive_branch = ast[2]
        negative_branch = ast[3]

        pos_branch_marked_ast = mark_and_collect_ite_conditions(positive_branch, cond_table)
        neg_branch_marked_ast = mark_and_collect_ite_conditions(negative_branch, cond_table)

        # Nothing prevents if-then-else from having another if-then-else inside the condition
        marked_cond_ast = mark_and_collect_ite_conditions(condition, cond_table)
        condition_id = cond_table.store_condition(marked_cond_ast)

        # @Todo: We need to descend into the condition as if-then-else expressions can be nested, e.g., (ite (ite B B1 B2) P N)
        #        should be equivalend to (ite (or (and B B1) (and (not B) B2)) -> (ite (or (and B B1) (and (not B) B2)) P N) which yields
        #        (or (and (or (and B B1) (and (not B) B2)) P) (and (nor (or (and B B1) (and (not B) B2))) N)

        ast[1] = condition_id  # type: ignore

        placeholdered_ast = ['ite', condition_id, pos_branch_marked_ast, neg_branch_marked_ast]
        return placeholdered_ast

    elif node_type == '+':  # The sum can be N-ary
        marked_subtrees = [mark_and_collect_ite_conditions(subtree, cond_table) for subtree in ast[1:]]
        return ['+'] + marked_subtrees

    elif node_type in ['*', '<=', '>=', '>', '<', '=', 'mod', 'div']:
        left_marked_ast = mark_and_collect_ite_conditions(ast[1], cond_table)
        right_marked_ast = mark_and_collect_ite_conditions(ast[2], cond_table)

        marked_ast = [node_type, left_marked_ast, right_marked_ast]
        return marked_ast

    elif node_type in ['and', 'or']:
        # @Todo: Remove this. We are handling this because we cannot distinguish between Boolean equivalency
        #        and equations. A proper solution is to extend disambiguation of variables to disambiguate
        #        entire tree (rename Boolean equivalency to some internal name), so that we don't have to
        #        deal with those kinds of problems.
        left_marked_ast = mark_and_collect_ite_conditions(ast[1], cond_table)
        right_marked_ast = mark_and_collect_ite_conditions(ast[2], cond_table)

        marked_ast = [node_type, left_marked_ast, right_marked_ast]
        return marked_ast

    elif node_type == 'not':
        body_marked_ast = mark_and_collect_ite_conditions(ast[1], cond_table)
        marked_ast = [node_type, body_marked_ast]
        return marked_ast

    elif node_type in ['-']:
        if len(node_type) == 3:
            left_marked_ast = mark_and_collect_ite_conditions(ast[1], cond_table)
            right_marked_ast = mark_and_collect_ite_conditions(ast[2], cond_table)
            marked_ast = [node_type, left_marked_ast, right_marked_ast]
            return marked_ast
        else:
            marked_ast = mark_and_collect_ite_conditions(ast[1], cond_table)
            return [node_type, marked_ast]

    assert False, f'Unknown node type: {node_type}'
    return ([], [])


def copy_ast(ast: AST_With_Placeholders) -> AST_With_Placeholders:
    return copy.deepcopy(ast)


def instantiate_condition_handles(ast: AST_With_Placeholders, conditions: Dict[int, AST_With_Placeholders], valuation_bits: int) -> Raw_AST:
    if not isinstance(ast, list):
        return ast  # type: ignore
    node_type: str = ast[0]  # type: ignore
    if node_type == 'ite':
        cond_id: int = ast[1]  # type: ignore
        is_cond_positive = (valuation_bits >> cond_id) % 2
        cond = copy_ast(conditions[cond_id])

        cond_body = ast[2] if is_cond_positive else ast[3]
        instantiated_body = instantiate_condition_handles(cond_body, conditions, valuation_bits)

        return instantiated_body
    else:
        inst_subtrees = (instantiate_condition_handles(subtree, conditions, valuation_bits) for subtree in ast[1:])
        return [node_type, *inst_subtrees]


def rewrite_ite_expressions(ast: Raw_AST) -> Raw_AST:
    if not isinstance(ast, list):
        return ast

    node_type: str = ast[0]  # type: ignore

    if node_type == 'ite':
        assert len(ast) == 4, 'The ite expr should have the form of (ite C P N)'
        condition, positive_branch, negative_branch = ast[1:]

        rewritten_positive_branch = rewrite_ite_expressions(positive_branch)  # type: ignore
        rewritten_negative_branch = rewrite_ite_expressions(negative_branch)  # type: ignore

        positive_branch_expr = ['and', condition, rewritten_positive_branch]
        negative_branch_expr = ['and', ['not', copy_ast(condition)], rewritten_negative_branch]
        ret = ['or', positive_branch_expr, negative_branch_expr]
        return ret
    elif node_type in ('exists', 'forall'):
        return [node_type, ast[1], rewrite_ite_expressions(ast[2])]
    elif node_type in ('<=', '<', '=', '>', '>='):
        # @Note: We have to handle if-then-else expressions also inside atoms as such are not forbidden and they appear in formulae.
        #        Moreover, we cannot just expand them right away, as we would create a malformed AST with Boolean connectives inside
        #        an atom.
        cond_table = ConditionTable()
        marked_ast = mark_and_collect_ite_conditions(ast, cond_table)
        if not cond_table.conditions:
            return ast  # There are no if-then-else expressions in the relation

        # We must be careful with nested conditions as when we instantiate a condition we have to also instantiate
        # the conditions inside it.
        def put_condition_with_positiveness(cond_with_id: Tuple[int, AST_With_Placeholders], conditions: Dict[int, AST_With_Placeholders], valuation_bits: int) -> Raw_AST:
            cond_id, cond = cond_with_id
            is_positive = (valuation_bits >> cond_id) % 2
            cond = copy_ast(cond)
            cond = instantiate_condition_handles(cond, conditions, valuation_bits)
            return cond if is_positive else ['not', cond]

        handle_to_condition_map = dict((cond_id, unfreeze_ast_node(cond_ast)) for cond_ast, cond_id in cond_table.conditions.items())
        cond_count = len(cond_table.conditions)

        result_ast: Raw_AST = ['or']

        # Generate boolean combinations of all conditions and rewrite the relation accordingly
        for cond_valuation_vector in range(2**cond_count):
            branch_guard = [put_condition_with_positiveness(cond_with_handle, handle_to_condition_map, cond_valuation_vector) for cond_with_handle in handle_to_condition_map.items()]
            branch_body = instantiate_condition_handles(marked_ast, handle_to_condition_map, cond_valuation_vector)
            result_ast.append(['and', *branch_guard, branch_body])
        return result_ast

    else:
        return [node_type, *(rewrite_ite_expressions(subtree) for subtree in ast[1:])]
