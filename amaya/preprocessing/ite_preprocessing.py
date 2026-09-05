from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
import copy
from typing import (
    Any,
    Callable,
    Dict,
    cast,
)

from amaya.relations_structures import (
    Frozen_AST,
    Raw_AST,
)


def freeze_ast_node(ast_node: Raw_AST) -> Frozen_AST:
    if isinstance(ast_node, (str, int)):
        return ast_node

    ret = tuple(freeze_ast_node(node) for node in ast_node)
    return ret  # type: ignore


def unfreeze_ast_node(ast_node: Raw_AST) -> Raw_AST:
    if isinstance(ast_node, (str, int)):
        return ast_node

    ret = [unfreeze_ast_node(node) for node in ast_node]
    return ret  # type: ignore



@dataclass
class ITE_Node_Info:
    _id: int

    var_id: int
    var_name: str  # Just some string baked from var_id, e.g., ite_var_{id}

    condition_id: int
    positive_branch: Raw_AST
    negative_branch: Raw_AST


@dataclass
class Variable_Manager():
    next_available_id: int = 0
    allocated_var_names: list[str] = field(default_factory=list)


    def allocate_var(self) -> int:
        _id = self.next_available_id
        self.next_available_id += 1

        var_name = make_ite_var(_id)  # @Temporary: We should get rid of variables being strings sooner than this
        self.allocated_var_names.append(var_name)
        
        return _id


@dataclass
class ITE_Table:
    """Table of all ite control conditions seen in an AST."""
    variable_manager: Variable_Manager

    value: int = 0
    conditions: Dict[Any, int] = field(default_factory=dict)

    conditions_to_nodes: Dict[int, list[int]] = field(default_factory=lambda: defaultdict(list))
    """ Maps condition_id to a list of nodes which have the same condtion. """
    next_ite_id: int = 0
    node_table: dict[int, ITE_Node_Info] = field(default_factory=dict)

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

    def store_node(self, condition_id: int, positive_branch: Raw_AST, negative_branch: Raw_AST) -> int:
        _id = self.next_ite_id
        self.next_ite_id += 1

        var_id = self.variable_manager.allocate_var()
        var_name = make_ite_var(var_id)
        
        node_info = ITE_Node_Info(_id, var_id, var_name, condition_id, positive_branch=positive_branch, negative_branch=negative_branch)
        self.node_table[_id] = node_info

        self.conditions_to_nodes[condition_id].append(_id)

        return _id


def make_ite_var(ite_id: int) -> str:
    return f'ite_{ite_id}'


def mark_and_collect_ite_conditions(ast: Raw_AST, cond_table: ITE_Table, inside_expression: bool = False) -> Raw_AST:
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
        marked_cond_ast = cast(Raw_AST, marked_cond_ast)  # We do not descend into ITE_Node_Infos (only 'unhandled' node)

        condition_id = cond_table.store_condition(marked_cond_ast)

        # @Todo: We need to descend into the condition as if-then-else expressions can be nested, e.g., (ite (ite B B1 B2) P N)
        #        should be equivalend to (ite (or (and B B1) (and (not B) B2)) -> (ite (or (and B B1) (and (not B) B2)) P N) which yields
        #        (or (and (or (and B B1) (and (not B) B2)) P) (and (nor (or (and B B1) (and (not B) B2))) N)

        node_id = cond_table.store_node(condition_id=condition_id, positive_branch=pos_branch_marked_ast, negative_branch=neg_branch_marked_ast)
        # The variable substituted for the expression must be the one the constraints will be written
        # about, i.e. the globally unique variable the `Variable_Manager` handed out - *not* `node_id`,
        # which only counts nodes within this atom's own table and therefore restarts at 0 for every
        # atom. Using `node_id` here made the k-th if-then-else of every atom collapse onto `ite_k`
        # while its defining constraints were emitted about some other, unused variable.
        replacement_var = cond_table.node_table[node_id].var_name
        return replacement_var

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


def copy_ast(ast: Raw_AST) -> Raw_AST:
    return copy.deepcopy(ast)



def make_constraints_for_ite_var_values(node_ids: list[int], ite_table: ITE_Table, get_node_body: Callable[[int], Raw_AST]) -> Raw_AST:
    constraining_relations = [['=',ite_table.node_table[node_id].var_name, get_node_body(node_id)] for node_id in node_ids]

    if len(constraining_relations) == 1:
        return constraining_relations[0]
    
    constraints: Raw_AST = cast(Raw_AST, ['and'] + constraining_relations)
    return constraints


def rewrite_ite_expressions(ast: Raw_AST, variable_manager: Variable_Manager) -> Raw_AST:
    if not isinstance(ast, list):
        return ast

    node_type: str = cast(str, ast[0])

    # We are not inside a relation, so we do not need complicated mechanism to obtain well-structured trees
    if node_type == 'ite':
        assert len(ast) == 4, 'The ite expr should have the form of (ite C P N)'

        condition = ast[1]
        positive_branch, negative_branch = ast[2:]

        rewritten_positive_branch = rewrite_ite_expressions(positive_branch, variable_manager)
        rewritten_negative_branch = rewrite_ite_expressions(negative_branch, variable_manager)

        positive_branch_expr = ['and', condition, rewritten_positive_branch]
        negative_branch_expr = ['and', ['not', copy_ast(condition)], rewritten_negative_branch]
        ret = ['or', positive_branch_expr, negative_branch_expr]
        return ret

    elif node_type in ('exists', 'forall'):
        return [node_type, ast[1], rewrite_ite_expressions(ast[2], variable_manager)]

    elif node_type in ('<=', '<', '=', '>', '>='):
        # @Note: We have to handle if-then-else expressions also inside atoms as such are not forbidden and they appear in formulae.
        #        Moreover, we cannot just expand them right away, as we would create a malformed AST with Boolean connectives inside
        #        an atom.
        cond_table = ITE_Table(variable_manager)
        marked_ast = mark_and_collect_ite_conditions(ast, cond_table)

        if not cond_table.conditions:
            return ast  # There are no if-then-else expressions in the relation

        # We have a marked AST in which all of the ITE conditions were replaced with fresh (int) variables. We need to now constrain the values
        # of these variables according to ITEs
        ite_constraints = []
        for condition_ast_frozen, condition_id in cond_table.conditions.items():
            ite_node_ids = cond_table.conditions_to_nodes[condition_id]

            condition_ast = unfreeze_ast_node(condition_ast_frozen)

            # conditionN => pariable = Positive branch; rewrite as
            # (NOT condition) OR variable = positive branch
            condition_holds_constraints = make_constraints_for_ite_var_values(ite_node_ids, cond_table, lambda node_id: cond_table.node_table[node_id].positive_branch)
            condition_holds_branch = ['or', ['not', condition_ast], condition_holds_constraints]

            condition_does_not_hold_constraints = make_constraints_for_ite_var_values(ite_node_ids, cond_table, lambda node_id: cond_table.node_table[node_id].negative_branch)
            condition_does_not_hold_branch = ['or', condition_ast, condition_does_not_hold_constraints ]

            ite_constraints.append(condition_holds_branch)
            ite_constraints.append(condition_does_not_hold_branch)

        # The fresh variables must be bound by an existential *at the atom*, not declared globally.
        #
        # Their value is a function of the if-then-else condition and branches, which may mention
        # variables bound by enclosing quantifiers - a single global variable cannot track a value that
        # depends on a universally quantified one, and forcing it to try loses models. Binding them here
        # also makes the encoding correct under negation: `NOT (atom AND definition)` is satisfied by
        # simply violating the definition, whereas `NOT (EXISTS v. definition(v) AND atom(v))` is not,
        # because the definition determines `v` uniquely from the condition, so the existential is
        # equivalent to the original atom in either polarity.
        ite_var_binders = [(node_info.var_name, 'Int') for node_info in cond_table.node_table.values()]
        return ['exists', ite_var_binders, ['and', marked_ast, *ite_constraints]]
        
    else:
        return [node_type, *(rewrite_ite_expressions(subtree, variable_manager) for subtree in ast[1:])]
