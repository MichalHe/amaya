from collections import defaultdict
import functools

from typing import Dict, Iterable, List, Set, cast
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Leaf_Type_List,
    ASTp_Node,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    pprint_formula
)


def _get_referenced_vars(ast: ASTp_Node) -> Iterable[Var]:
    match ast:
        case Var():
            return (ast,)
        case Relation() | Congruence():
            return ast.vars
        case BoolLiteral():
            return tuple()
        case _:
            return ast.referenced_vars


def _push_quantifier_trough_conjunction(quantif_node: AST_Quantifier) -> ASTp_Node:
    connective: AST_Connective = cast(AST_Connective, quantif_node.child)
    bound_vars = set(quantif_node.bound_vars)
    scope_range = connective.children

    min_var_covers_entire_scope = False
    while not min_var_covers_entire_scope and bound_vars:
        # Select var with min scope
        var_to_child_indices: Dict[Var, List[int]] = defaultdict(list)
        for child_idx, child in enumerate(scope_range):
            for var in _get_referenced_vars(child):
                if var not in bound_vars:
                    continue
                var_to_child_indices[var].append(child_idx)
        min_scope_var = min(var_to_child_indices, key=lambda var: len(var_to_child_indices[var]))

        if len(var_to_child_indices[min_scope_var]) == len(scope_range):
            min_var_covers_entire_scope = True
            break

        # Make a new node capturing the min scope
        min_scope = tuple(scope_range[child_idx] for child_idx in var_to_child_indices[min_scope_var])
        _referenced_vars: Set[Var] = functools.reduce(set.union, tuple(_get_referenced_vars(child) for child in min_scope), set())
        referenced_vars = tuple(sorted(_referenced_vars))

        if len(min_scope) > 1:
            miniscoped_subtree = AST_Connective(referenced_vars=referenced_vars,
                                                type=connective.type,
                                                children=min_scope,
                                                variable_bounds=connective.variable_bounds)
            miniscoped_node = AST_Quantifier(referenced_vars=referenced_vars,
                                             bound_vars=(min_scope_var,),
                                             child=miniscoped_subtree)
        else:
            miniscoped_subtree = min_scope[0]
            miniscoped_node = AST_Quantifier(referenced_vars=referenced_vars,
                                             bound_vars=(min_scope_var,),
                                             child=miniscoped_subtree)
            # Since the miniscoped quantifier spans only a single node, e.g., EXISTS x (PSI(x)), it might be the case
            # that PSI(x) is, in fact, a conjuction PSI(x) = ALPHA(X) AND BETA(Z), so the quantifier can be distributed
            # even further.
            miniscoped_node = miniscope_quantifiers(miniscoped_node)

        # Modify tree by removing the min_scope nodes that were put into one new node
        untouched_subtrees = [child for child_idx, child in enumerate(scope_range) if child_idx not in var_to_child_indices[min_scope_var]]
        scope_range = untouched_subtrees + [miniscoped_node]

        bound_vars.remove(min_scope_var)

    if len(scope_range) > 1:
        scope = AST_Connective(referenced_vars=quantif_node.referenced_vars, type=connective.type, children=tuple(scope_range))
        if not bound_vars:
            return scope
        result = AST_Quantifier(referenced_vars=quantif_node.referenced_vars, bound_vars=tuple(sorted(bound_vars)), child=scope)
        return result

    # Scope size is 1
    return scope_range[0]


def _push_quantifier_trough_disjunction(quantif_node: AST_Quantifier) -> ASTp_Node:
    disjunction: AST_Connective = cast(AST_Connective, quantif_node.child)
    bound_vars = set(quantif_node.bound_vars)

    new_children: List[ASTp_Node] = []
    for node in disjunction.children:
        if isinstance(node, (Relation, Congruence)):
            refd_vars = bound_vars.intersection(node.vars)
            if refd_vars:
                new_node = AST_Quantifier(referenced_vars=tuple(node.vars), bound_vars=tuple(sorted(refd_vars)), child=node)
                new_node = _perform_miniscoping(new_node)
                new_children.append(new_node)
            else:
                new_children.append(node)
        elif isinstance(node, BoolLiteral):
            new_children.append(node)
        elif isinstance(node, Var):
            if node in bound_vars:
                new_children.append(BoolLiteral(True))  # EXISTS (X BOOL) X
            else:
                new_children.append(node)
        else:
            refd_vars = bound_vars.intersection(node.referenced_vars)
            if refd_vars:
                new_node = AST_Quantifier(referenced_vars=node.referenced_vars, bound_vars=tuple(sorted(refd_vars)), child=node)
                new_node = _perform_miniscoping(new_node)
                new_children.append(new_node)
            else:
                new_children.append(node)

    return AST_Connective(referenced_vars=quantif_node.referenced_vars, type=Connective_Type.OR, children=tuple(new_children))


def _perform_miniscoping(quantif_node: AST_Quantifier) -> ASTp_Node:
    match quantif_node.child:
        case AST_Negation():
            return quantif_node

        case AST_Connective():
            match quantif_node.child.type:
                case Connective_Type.EQUIV:
                    # If we rewrite the EQUIV into (...) AND (...) we would see that both children refer to the same vars
                    # so the quantifier cannot be pushed in any further.
                    return quantif_node
                case Connective_Type.OR:
                    return _push_quantifier_trough_disjunction(quantif_node)
                case Connective_Type.AND:
                    return _push_quantifier_trough_conjunction(quantif_node)
        case AST_Quantifier():
            bound_vars = sorted(set(quantif_node.bound_vars).union(quantif_node.child.bound_vars))
            merged_quantifier = AST_Quantifier(referenced_vars=quantif_node.referenced_vars, bound_vars=tuple(bound_vars), child=quantif_node.child.child)
            return _perform_miniscoping(merged_quantifier)

        case Relation() | Congruence() | Var() | BoolLiteral():
            return quantif_node

        case _:
            raise ValueError(f'Unhandled node when pushing a quantifier through its child node of type={type(quantif_node.child)}')


def miniscope_quantifiers(ast: ASTp_Node):
    match ast:
        case Var() | Congruence() | Relation() | BoolLiteral():
            return ast
        case AST_Quantifier():
            result = _perform_miniscoping(ast)
            return result
        case AST_Connective():
            children = tuple(miniscope_quantifiers(child) for child in ast.children)
            return AST_Connective(referenced_vars=ast.referenced_vars, type=ast.type, children=children)
        case AST_Negation():
            child = miniscope_quantifiers(ast.child)
            return AST_Negation(referenced_vars=ast.referenced_vars, child=child)
        case _:
            raise NotImplementedError(f'Node {ast} is not handled when miniscoping quantifiers.')
