from __future__ import annotations
from collections import defaultdict
from dataclasses import (
    dataclass,
    field
)
import functools
from typing import (
    Dict,
    Union,
    Set,
)

from amaya.ast_definitions import AST_Node
from amaya.relations_structures import Relation


@dataclass
class Variable_Bounds_Info:
    has_upper_bound: bool = False
    has_lower_bound: bool = False


@dataclass
class AST_Internal_Node_With_Bounds_Info:
    node_type: str
    children: AST_Node_With_Bounds_Info
    bounds: Dict[str, Variable_Bounds_Info] = field(default_factory=lambda: defaultdict(Variable_Bounds_Info))


@dataclass
class AST_Quantifier_Node_With_Bounds_Info:
    node_type: str
    children: AST_Node_With_Bounds_Info
    bindings: List[Tuple[str, str]]
    bounds: Dict[str, Variable_Bounds_Info] = field(default_factory=lambda: defaultdict(Variable_Bounds_Info))


@dataclass
class AST_Leaf_Node_With_Bounds_Info:
    contents: Union[Relation, str]
    bounds: Dict[str, Variable_Bounds_Info] = field(default_factory=lambda: defaultdict(Variable_Bounds_Info))



AST_Node_With_Bounds_Info = Union[AST_Leaf_Node_With_Bounds_Info, AST_Quantifier_Node_With_Bounds_Info, AST_Internal_Node_With_Bounds_Info]


def perform_variable_bounds_analysis_on_ast(ast: AST_Node) -> AST_Node_With_Bounds_Info:
    if isinstance(ast, Relation):
        relation: Relation = ast
        relation_with_bounds_info = AST_Leaf_Node_With_Bounds_Info(contents=relation)

        if relation.operation in ('<=', '<', '='):
            for var_name in relation.variable_names:
                relation_with_bounds_info.bounds[var_name].has_upper_bound = True

        if relation.operation in ('>', '>=', '='):
            for var_name in relation.variable_names:
                relation_with_bounds_info.bounds[var_name].has_lower_bound = True

        return relation_with_bounds_info
    elif isinstance(ast, str):
        return AST_Leaf_Node_With_Bounds_Info(contents=ast)  # A Boolean variable does not tell us anything about bounds

    node_type = ast[0]
    # We check for both quantifiers, because we have to remove consequent negation after quantifier simplification
    # due to bounds, since the simplification might remove a quantifier node altogether, causing consequent negation
    # to appear
    if node_type in ('exists', 'forall'):
        subtree_bounds_info = perform_variable_bounds_analysis_on_ast(ast[2])

        quantifier_node_with_bounds_info = AST_Quantifier_Node_With_Bounds_Info(node_type=node_type,
                                                                                children=[subtree_bounds_info],
                                                                                bindings=ast[1],
                                                                                bounds=subtree_bounds_info.bounds)
        return quantifier_node_with_bounds_info

    elif node_type in ('and', 'or'):
        subtrees_with_bounds = [perform_variable_bounds_analysis_on_ast(subtree) for subtree in ast[1:]]

        internal_node_with_bounds_info = AST_Internal_Node_With_Bounds_Info(node_type=node_type,
                                                                            children=subtrees_with_bounds)
        if node_type == 'and':
            for subtree_with_bounds in subtrees_with_bounds:
                for var_name, bounds_info in subtree_with_bounds.bounds.items():
                    internal_node_with_bounds_info.bounds[var_name].has_lower_bound |= bounds_info.has_lower_bound
                    internal_node_with_bounds_info.bounds[var_name].has_upper_bound |= bounds_info.has_upper_bound
        else:
            # We collect bounds information so we can simplify existential quantification. Therefore, we need certainty
            # that the variables is unbound, thus we consider the variable as having an upper bound only when it has
            # a bound in both branches of disjunction.
            
            all_vars_in_subtrees = functools.reduce(
                set.union, (set(subtree_bounds_info.bounds.keys()) for subtree_bounds_info in subtrees_with_bounds)
            )
            vars_unbound_in_some_branch: Set[str] = set()
            
            for subtree_with_bounds in subtrees_with_bounds:
                for var_name, bounds_info in subtree_with_bounds.bounds.items():
                    if var_name not in internal_node_with_bounds_info.bounds:
                        internal_node_with_bounds_info.bounds[var_name] = Variable_Bounds_Info(has_lower_bound=True,
                                                                                               has_upper_bound=True)
                    internal_node_with_bounds_info.bounds[var_name].has_lower_bound &= bounds_info.has_lower_bound
                    internal_node_with_bounds_info.bounds[var_name].has_upper_bound &= bounds_info.has_upper_bound

                vars_unbound_in_some_branch |= all_vars_in_subtrees.difference(subtree_with_bounds.bounds.keys())

            for var_unbound_in_some_branch in vars_unbound_in_some_branch:
                internal_node_with_bounds_info.bounds[var_unbound_in_some_branch].has_upper_bound = False
                internal_node_with_bounds_info.bounds[var_unbound_in_some_branch].has_lower_bound = False

        return internal_node_with_bounds_info

    elif node_type == 'not':
        subtree_bounds_info = perform_variable_bounds_analysis_on_ast(ast[1])
        return AST_Internal_Node_With_Bounds_Info(node_type=node_type,
                                                  children=[subtree_bounds_info],
                                                  bounds=subtree_bounds_info.bounds)

    raise ValueError(f'[Variable bounds analysis] Cannot descend into AST - unknown node: {node_type=}, {ast=}')



def simplify_existential_quantif_of_unbound_var(ast: AST_Node) -> AST_Node:
    pass
