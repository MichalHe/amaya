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
class Bounds_Info:
    has_upper_bound: bool = False
    has_lower_bound: bool = False


@dataclass
class Mod_Term_Bounds:
    lower_bound: int
    upper_bound: int


@dataclass
class AST_Internal_Node_With_Bounds_Info:
    node_type: str
    children: AST_Node_With_Bounds_Info
    bounds: Dict[str, Bounds_Info] = field(default_factory=lambda: defaultdict(Bounds_Info))
    mod_term_bounds: Dict[ModuloTerm, Mod_Term_Bounds] = field(default_factory=dict)


@dataclass
class AST_Quantifier_Node_With_Bounds_Info:
    node_type: str
    children: AST_Node_With_Bounds_Info
    bindings: List[Tuple[str, str]]
    bounds: Dict[str, Bounds_Info] = field(default_factory=lambda: defaultdict(Bounds_Info))
    mod_term_bounds: Dict[ModuloTerm, Mod_Term_Bounds] = field(default_factory=dict)


@dataclass
class AST_Leaf_Node_With_Bounds_Info:
    contents: Union[Relation, str]
    bounds: Dict[str, Bounds_Info] = field(default_factory=lambda: defaultdict(Bounds_Info))
    mod_term_bounds: Dict[ModuloTerm, Mod_Term_Bounds] = field(default_factory=dict)


AST_Node_With_Bounds_Info = Union[AST_Leaf_Node_With_Bounds_Info, AST_Quantifier_Node_With_Bounds_Info, AST_Internal_Node_With_Bounds_Info]


def extract_bounds_set_on_mod_terms(relation: Relation, ast_node_with_bounds_info: AST_Node_With_Bounds_Info) -> bool:
    # Detect restrictions put forth on the values of the modulo terms, e.g., `(x mod 10) >= 1` so if x does not have 
    # an upper bound, we will replace the term with correct value and not, e.g., 0.
    if len(relation.modulo_terms) == 1 and not relation.div_terms and not relation.variable_names:
        mod_term = relation.modulo_terms[0]
        mod_term_coef = relation.modulo_term_coefficients[0]
        if mod_term_coef == 0:
            return True  # Propagate, that the relation had the form this function looks for
        if relation.operation == '=': 
            mod_term_bounds = Mod_Term_Bounds(lower_bound=max(0, relation.absolute_part),
                                              upper_bound=min(mod_term.modulo - 1, relation.absolute_part))
        else: 
            relation_rhs_constant = relation.absolute_part

            # Change the relation predicate symbol to be only < or <=
            if relation.operation in ('>', '<='):
                mod_term_coef *= -1
                relation_rhs_constant *= -1

            # Change the relation predicate symbol to be only <=
            if relation.operation in ('<', '>'): 
                relation_rhs_constant -= 1

            if mod_term_coef > 0:
                mod_term_bounds = Mod_Term_Bounds(lower_bound=0, upper_bound=relation_rhs_constant)
            elif mod_term_coef < 0:
                mod_term_bounds = Mod_Term_Bounds(lower_bound=relation_rhs_constant, upper_bound=mod_term.modulo - 1)
        ast_node_with_bounds_info.mod_term_bounds[mod_term] = mod_term_bounds
        return True
    return False
    

def perform_variable_bounds_analysis_on_ast(ast: AST_Node) -> AST_Node_With_Bounds_Info:
    if isinstance(ast, Relation):
        relation: Relation = ast
        relation_with_bounds_info = AST_Leaf_Node_With_Bounds_Info(contents=relation)
        
        if extract_bounds_set_on_mod_terms(relation, relation_with_bounds_info):
            # The relation has the form (x mod K) <> C, thus we don't have to continue as there are no variables
            return relation_with_bounds_info

        if relation.operation in ('<=', '<', '='):
            for var_coef, var_name in zip(relation.variable_coefficients, relation.variable_names):
                if var_coef > 0:
                    relation_with_bounds_info.bounds[var_name].has_upper_bound = True
                elif var_coef < 0:
                    relation_with_bounds_info.bounds[var_name].has_lower_bound = True

        if relation.operation in ('>', '>=', '='):
            for var_coef, var_name in zip(relation.variable_coefficients, relation.variable_names):
                if var_coef > 0:
                    relation_with_bounds_info.bounds[var_name].has_lower_bound = True
                elif var_coef < 0:
                    relation_with_bounds_info.bounds[var_name].has_upper_bound = True

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
                                                                                bounds=subtree_bounds_info.bounds,
                                                                                mod_term_bounds=subtree_bounds_info.mod_term_bounds)
        return quantifier_node_with_bounds_info

    elif node_type in ('and', 'or'):
        subtrees_with_bounds = [perform_variable_bounds_analysis_on_ast(subtree) for subtree in ast[1:]]

        internal_node_with_bounds_info = AST_Internal_Node_With_Bounds_Info(node_type=node_type,
                                                                            children=subtrees_with_bounds)
        # NOTE(OR-nodes): We collect bounds information so we can simplify existential quantification. Therefore,
        # we need certainty that a variable is unbound in all branches of the OR-node. Otherwise we would simplify
        # relations in an OR-node branch based on information coming from another branch, which is obviously wrong.
        for subtree_with_bounds in subtrees_with_bounds:
            for var_name, bounds_info in subtree_with_bounds.bounds.items():
                internal_node_with_bounds_info.bounds[var_name].has_lower_bound |= bounds_info.has_lower_bound
                internal_node_with_bounds_info.bounds[var_name].has_upper_bound |= bounds_info.has_upper_bound

            for mod_term, mod_term_bounds in subtree_with_bounds.mod_term_bounds.items():
                if mod_term not in internal_node_with_bounds_info.mod_term_bounds:
                    internal_node_with_bounds_info.mod_term_bounds[mod_term] = mod_term_bounds
                else:
                    propagated_mod_term = internal_node_with_bounds_info.mod_term_bounds[mod_term]
                    propagated_mod_term.lower_bound = max(propagated_mod_term.lower_bound, mod_term_bounds.lower_bound)
                    propagated_mod_term.upper_bound = min(propagated_mod_term.upper_bound, mod_term_bounds.upper_bound)

        return internal_node_with_bounds_info

    elif node_type == 'not':
        subtree_bounds_info = perform_variable_bounds_analysis_on_ast(ast[1])
        return AST_Internal_Node_With_Bounds_Info(node_type=node_type,
                                                  children=[subtree_bounds_info],
                                                  bounds=subtree_bounds_info.bounds,
                                                  mod_term_bounds=subtree_bounds_info.mod_term_bounds)

    raise ValueError(f'[Variable bounds analysis] Cannot descend into AST - unknown node: {node_type=}, {ast=}')


def will_relation_be_always_satisfied_due_to_unbound_var(relation: Relation,
                                                         quantified_vars_with_bounds: Dict[str, Bounds_Info]
                                                         ) -> bool:
    # We know that the Relation can be always satisfied, and thus reduced to True if:
    # - it has the form of `ax + by ... >= C`, y has no upper bound and b > 0
    # - it has the form of `ax + by ... >= C`, y has no lower bound and b < 0
    # - it has the form of `ax + by ... <= C`, y has no lower bound and b > 0
    # - it has the form of `ax + by ... <= C`, y has no upper bound and b < 0
    for i, var_name in enumerate(relation.variable_names):
        if var_name not in quantified_vars_with_bounds:
            continue
        var_coef = relation.variable_coefficients[i]
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
                                                        quantified_vars_with_bounds: Dict[str, Bounds_Info]
                                                        ) -> Relation:
    simplified_relation = Relation(variable_names=relation.variable_names,
                                   variable_coefficients=relation.variable_coefficients,
                                   modulo_terms=[],  # We will fill them with the terms that could not be simplified
                                   modulo_term_coefficients=[],
                                   div_terms=relation.div_terms,
                                   div_term_coefficients=relation.div_term_coefficients,
                                   absolute_part=relation.absolute_part, operation=relation.operation)

    for modulo_term_coef, modulo_term in zip(relation.modulo_term_coefficients, relation.modulo_terms):
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
            simplified_relation.modulo_term_coefficients.append(modulo_term_coef)

    return simplified_relation


def remove_existential_quantification_of_unbound_vars(ast: AST_Node_With_Bounds_Info,
                                                      quantified_vars_with_bounds: Dict[str, Bounds_Info]
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
