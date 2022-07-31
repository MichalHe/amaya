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

        # @FIXME: This is wrong - we should reflect the variable coefficient when we are determining whether it has
        #         a bound
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
            # FIXME: This is wrong - this would mean that we will be making local modifications in predicates (leaves)
            #        based on information we got from other branch of the 'or' node. However, the in the modified
            #        predicates the variable might have both bounds (e.g. it is a part of an 'and'). We should
            #        propagate bounds information same way as with 'and'. It will be a less detailed information, but
            #        we will deal with that later.
            #
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



def will_relation_be_always_satisfied_due_to_unbound_var(relation: Relation,
                                                         quantified_vars_with_bounds: Dict[str, Variable_Bounds_Info]
                                                         ) -> bool:
    # We know that the Relation can be always satisfied, and thus reduced to True if:
    # - it has the form of `ax + by ... >= C`, y has no upper bound and b > 0
    # - it has the form of `ax + by ... >= C`, y has no lower bound and b < 0
    # - it has the form of `ax + by ... <= C`, y has no lower bound and b > 0
    # - it has the form of `ax + by ... <= C`, y has no upper bound and b < 0
    for i, var_name in enumerate(relation.variable_names):
        if var_name not in quantified_vars_with_bounds:
            continue
        var_coef = relation.variable_coeficients[i]
        var_bounds = quantified_vars_with_bounds[var_name]

        if relation.operation in ('<', '<='):
            can_var_term_be_arbitrarly_small = (
                (var_coef > 0 and not var_bounds.has_lower_bound) or (var_coef < 0 and not var_bounds.has_upper_bound)
            )
            return can_var_term_be_arbitrarly_small
        if relation.operation in ('>', '>='):
            can_var_term_be_arbitrarly_large = (
                (var_coef > 0 and not var_bounds.has_upper_bound) or (var_coef < 0 and not var_bounds.has_lower_bound)
            )
            return can_var_term_be_arbitrarly_large
    return False


def simplify_modulo_terms_with_unbound_vars_in_relation(relation: Relation,
                                                        quantified_vars_with_bounds: Dict[str, Variable_Bounds_Info]
                                                        ) -> Relation:
    simplified_relation = Relation(variable_names=relation.variable_names,
                                   variable_coeficients=relation.variable_coeficients,
                                   modulo_terms=[],  # We will fill them with the terms that could not be simplified
                                   modulo_term_coeficients=[],
                                   div_terms=relation.div_terms,
                                   div_term_coeficients=relation.div_term_coeficients,
                                   absolute_part=relation.absolute_part, operation=relation.operation)

    for modulo_term_coef, modulo_term in zip(relation.modulo_term_coeficients, relation.modulo_terms):
        simplified_modulo_value: Optional[int] = None
        for var_name in modulo_term.variables:
            if not var_name in quantified_vars_with_bounds:
                continue
            var_bounds = quantified_vars_with_bounds[var_name]
            if not var_bounds.has_lower_bound or not var_bounds.has_upper_bound:
                simplified_modulo_value = modulo_term.constant
                break

        if simplified_modulo_value is not None:
            # Move the constant to which was the modulo term simplified directly to the right side
            simplified_relation.absolute_part -= modulo_term_coef * simplified_modulo_value
        else:
            # The term could not be simplified, append it as it is
            simplified_relation.modulo_terms.append(modulo_terms)
            simplified_relation.modulo_term_coeficients.append(modulo_term_coef)

    return simplified_relation


def remove_existential_quantification_of_unbound_vars(ast: AST_Node_With_Bounds_Info,
                                                      quantified_vars_with_bounds: Dict[str, Variable_Bounds_Info]
                                                      ) -> Union[bool, AST_Node_With_Bounds_Info]:

    if isinstance(ast, AST_Leaf_Node_With_Bounds_Info):
        if isinstance(ast.contents, Relation):
            if will_relation_be_always_satisfied_due_to_unbound_var(ast.contents, quantified_vars_with_bounds):
                return True
            simplified_relation = simplify_modulo_terms_with_unbound_vars_in_relation(ast.contents,
                                                                                      quantified_vars_with_bounds)
            return AST_Leaf_Node_With_Bounds_Info(contents=simplified_relation, bounds=ast.bounds)
        return ast

    elif isinstance(ast, AST_Quantifier_Node_With_Bounds_Info):
        for var_name, dummy_type in ast.bindings:
            quantified_vars_with_bounds[var_name] = ast.bounds[var_name]

        # @Optimize: Here we should also propagate back information that some variables are not present in the subtree,
        #            so we can drop some of the variables from the quantifier altogether
        subtree = remove_existential_quantification_of_unbound_vars(ast.children[0], quantified_vars_with_bounds)
        if isinstance(subtree, bool):
            return subtree  # The entire subtree was trivially satisfiable

        for var_name, dummy_type in ast.bindings:
            del quantified_vars_with_bounds[var_name]

        return AST_Quantifier_Node_With_Bounds_Info(node_type=ast.node_type, bindings=ast.bindings,
                                                    bounds=ast.bounds, children=[subtree])

    elif isinstance(ast, AST_Internal_Node_With_Bounds_Info):
        simplified_children = [
            remove_existential_quantification_of_unbound_vars(child, quantified_vars_with_bounds) for child in ast.children
        ]
        if ast.node_type == 'and':
            if any((child is False for child in simplified_children)):
                return False
            new_node_children = [child for child in simplified_children if not isinstance(child, bool)]
            if not new_node_children:
                return True  # All children are Booleans, but none of them is False, thus all must be True
            if len(new_node_children) == 1:
                return new_node_children[0]
        elif ast.node_type == 'or':
            if any((child is True for child in simplified_children)):
                return True
            new_node_children = [child for child in simplified_children if not isinstance(child, bool)]
            if not new_node_children:
                return False  # All children are Booleans, but none of them is True, thus all must be False
            if len(new_node_children) == 1:
                return new_node_children[0]
        elif ast.node_type == 'not':
            new_node_children = list(simplified_children)  # There is only one child
            if isinstance(new_node_children[0], bool):
                return not new_node_children[0]
        else:
            err_msg = (f'[Simplify quantification with var bounds]: Cannot descend into internal node '
                       f'{ast.node_type=} {ast=}')
            raise ValueError(err_msg)

        return AST_Internal_Node_With_Bounds_Info(node_type=ast.node_type, bounds=ast.bounds,
                                                  children=new_node_children)
    assert False


def simplify_existential_quantif_of_unbound_var(ast: AST_Node) -> AST_Node:
    ast_with_bounds = perform_variable_bounds_analysis_on_ast(ast)
