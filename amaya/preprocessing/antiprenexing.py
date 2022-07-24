from dataclasses import dataclass
from typing import (
    List,
    Set,
    Tuple,
)

from amaya.ast_definitions import AST_Node
from amaya.relations_structures import Relation


@dataclass
class Tagged_AST_Node:
    node: AST_Node
    variables: Set[str]


def tag_ast_nodes_with_variables_used_inside_their_ast(root: AST_Node) -> Tagged_AST_Node:
    """Tag every inner AST node with information about variables used in their AST-subtrees."""
    if not isinstance(root, list):
        relation: Relation = root
        variables = set(relation.get_used_variables())
        return Tagged_AST_Node(node=root, variables=variables)

    root_node_type = root[0]

    if root_node_type in ('exists', 'forall'):
        tagged_subtree = tag_ast_nodes_with_variables_used_inside_their_ast(root[2])
        tagged_node = [root_node_type, root[1], tagged_subtree]
        return Tagged_AST_Node(node=tagged_node, variables=tagged_subtree.variables)

    if root_node_type in ('and', 'or', 'not'):
        vars_used_in_subtrees: Set[str] = set()
        tagged_node = [root_node_type]

        for subtree in root[1:]:
            tagged_subtree = tag_ast_nodes_with_variables_used_inside_their_ast(subtree)
            vars_used_in_subtrees.update(tagged_subtree.variables)
            tagged_node.append(tagged_subtree)

        return Tagged_AST_Node(node=tagged_node, variables=vars_used_in_subtrees)

    raise ValueError('A node {} not handled when tagging AST with used variables.'.format(root))


def push_quantifiers_inside_on_tagged_ast(root: Tagged_AST_Node,
                                          carried_quantifiers: Set[Tuple[str, str]]) -> AST_Node:

    if isinstance(root.node, Relation):
        # We might have arrived with to a relation carrying an quantifier binding only variables in this relation
        relation: Relation = root.node
        relation_variables = relation.get_used_variables()
        bindings = [
            [var_name, var_type] for var_name, var_type in carried_quantifiers if var_name in relation_variables
        ]
        if bindings:
            return ['exists', bindings, relation]
        else:
            return relation

    node_type = root.node[0]
    # Pick the quantifier and carry it with us as we recurse deeper until we find a node that uses the var being bound
    if node_type == 'exists':
        carried_quantifiers = set(carried_quantifiers)
        carried_quantifiers.update(tuple(binding) for binding in root.node[1])
        return push_quantifiers_inside_on_tagged_ast(root.node[2], carried_quantifiers)

    if node_type in ('and', 'or'):
        dropped_variables: Set[Tuple[str, str]] = set()

        # Identify what quantifiers we have to drop at this place
        for var_name, var_type in carried_quantifiers:
            if all((var_name in subtree.variables for subtree in root.node[1:])):
                # All subformulae use the variable, we have to drop the carried quantifier here
                dropped_variables.add((var_name, var_type))

        for var_type_pair in dropped_variables:
            carried_quantifiers.remove(var_type_pair)

        subtrees = [push_quantifiers_inside_on_tagged_ast(subtree, carried_quantifiers) for subtree in root.node[1:]]

        if dropped_variables:
            bindings = [list(binding) for binding in dropped_variables]
            return ['exists', bindings, [node_type, *subtrees]]
        else:
            return [node_type, *subtrees]

    if node_type in ('not',):
        return [node_type, push_quantifiers_inside_on_tagged_ast(root.node[1], carried_quantifiers)]

    else:
        raise ValueError(f'Don\'t know how to push quantifiers inside of a node with type: {node_type=}')


def perform_antiprenexing(formula: AST_Node) -> AST_Node:
    """Push quantifiers present in the formula as deep as possible."""
    tagged_ast = tag_ast_nodes_with_variables_used_inside_their_ast(formula)
    print(tagged_ast)
    return push_quantifiers_inside_on_tagged_ast(tagged_ast, carried_quantifiers=set())
