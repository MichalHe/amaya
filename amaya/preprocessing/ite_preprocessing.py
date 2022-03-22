from typing import Dict, Set

from amaya.ast_definitions import AST_Leaf, AST_NaryNode, AST_Node, NodeEncounteredHandlerStatus


def collect_ite_control_variables(ast) -> Set[str]:
    '''Returns the set of boolean variables found in the ITE expressions in the given AST.'''
    if type(ast) != list:
        return set()

    root = ast[0]
    if root == 'ite':
        assert len(ast) == 4
        ite_variable = ast[1]
        ite_true_tree = ast[2]
        ite_false_tree = ast[3]

        ite_true_info = collect_ite_control_variables(ite_true_tree)
        ite_false_info = collect_ite_control_variables(ite_false_tree)

        return set([ite_variable]).union(ite_true_info).union(ite_false_info)
    elif root in ['+',  '*', '<=', '>=', '>', '<', '=', 'mod']:
        return collect_ite_control_variables(ast[1]).union(collect_ite_control_variables(ast[2]))
    elif root in ['-']:
        if len(root) == 3:
            return collect_ite_control_variables(ast[1]).union(collect_ite_control_variables(ast[2]))
        else:
            return collect_ite_control_variables(ast[1])
    return set()


def expand_ite_expressions_inside_presburger_relation(relation_root: AST_NaryNode, 
                                                      is_reeval: bool,
                                                      ctx: Dict) -> NodeEncounteredHandlerStatus:
    from amaya.ast_relations import evaluate_ite_for_var_assignment
    ite_control_variables = collect_ite_control_variables(relation_root)

    if not ite_control_variables:
        # There are no control variables, no modification to the AST needs to be performed.
        return NodeEncounteredHandlerStatus(False, False)

    # Generate the expanded ite-expression
    expanded_expr = ['or']
    for i in range(2**len(ite_control_variables)):
        control_variables_bit_values = number_to_bit_tuple(i, len(ite_control_variables))
        # Convert the bit values into corresponing formulas:
        # (A=0, B=0, C=1) --> ~A, ~B, C
        variable_literals = [variable if variable_bit else ['not', variable] for variable, variable_bit in zip(ite_control_variables, control_variables_bit_values)]

        variable_truth_assignment = dict(zip(ite_control_variables, map(bool, control_variables_bit_values)))

        conjuction = ['and', *variable_literals, evaluate_ite_for_var_assignment(relation_root, variable_truth_assignment)]
        expanded_expr.append(conjuction)

    # replace the contents of `relation_root` with the results.
    relation_root.pop(-1)
    relation_root.pop(-1)
    relation_root.pop(-1)

    for node in expanded_expr:
        relation_root.append(node)

    ctx['ite_expansions_cnt'] += len(ite_control_variables)

    return NodeEncounteredHandlerStatus(True, False)


def ite_expansion_handler(ast: AST_NaryNode, is_reeval: bool, ctx: Dict) -> NodeEncounteredHandlerStatus:
    _, bool_expr, if_branch, else_branch = ast

    presbureger_relation_roots = {'<=', '<', '=', '>', '>='}

    # Walk the history and see whether we are under any of the presb. relation roots
    is_ite_inside_atomic_formula = False
    for parent_tree in ctx['history']:
        if parent_tree[0] in presbureger_relation_roots:
            is_ite_inside_atomic_formula = True

    if is_ite_inside_atomic_formula:
        # We don't want to perform expansions inside atomic relations -
        # the expansions must be performed in a different fashion.
        return NodeEncounteredHandlerStatus(False, False)

    ast[0] = 'or'
    ast[1] = ['and', bool_expr, if_branch]
    ast[2] = ['and', ['not', bool_expr], else_branch]

    ctx['ite_expansions_cnt'] += 1

    return NodeEncounteredHandlerStatus(True, False)
