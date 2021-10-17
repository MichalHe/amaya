from typing import Dict, Generator, List, Optional, Tuple

import ast_relations as relations
from ast_definitions import AST_NaryNode, AST_Node, AST_Leaf, NodeEncounteredHandler, NodeEncounteredHandlerStatus
from relations_structures import Relation, ModuloTerm
from preprocessing.ite_preprocessing import expand_ite_expressions_inside_presburger_relation, ite_expansion_handler
from log import logger


def reduce_relation_asts_to_evaluable_leaves(ast: AST_NaryNode) -> AST_Node:
    '''
    Walks the AST and replaces its subtrees encoding relations (atomic formulas) to canoical representation - Relation.
    Example:
        (and (= x 0) (<= y 1))  --->  (and Relation(..) Relation(..))
    '''
    if type(ast) != list:
        return ast

    if ast[0] in ['<', '>', '<=', '>=', '=']:
        relation = relations.extract_relation(ast)
        relation.ensure_canoical_form_if_equation()

        if relation.direct_construction_exists():
            return relation

        relation_without_modulos, replacement_infos = relation.replace_modulo_terms_with_variables()
        assert replacement_infos, 'Relation did not have a direct construction, yet there were no modulos inside(?)'

        # We need to add relations expressing modulo/reminder domains etc.
        resulting_relations: List[Relation] = [relation_without_modulos]
        for replacement_info in replacement_infos:

            # (variables-inside-modulo - modulo-var) mod orignal-modulo ~ 0

            modulo_term = ModuloTerm(variables=replacement_info.term.variables + (replacement_info.variable,),
                                     variable_coeficients=replacement_info.term.variable_coeficients + (-1,),
                                     constant=replacement_info.term.constant,
                                     modulo=replacement_info.term.modulo)
            modulo_term = modulo_term.into_sorted()

            congruence_relation = Relation(variable_names=[],
                                           variable_coeficients=[],
                                           modulo_terms=[modulo_term],
                                           modulo_term_coeficients=[1],
                                           absolute_part=0,
                                           operation='=')

            reminder_lower_bound = Relation(variable_names=[replacement_info.variable],
                                            variable_coeficients=[-1],
                                            modulo_terms=[],
                                            modulo_term_coeficients=[],
                                            absolute_part=0,
                                            operation='<=')

            reminder_upper_bound = Relation(variable_names=[replacement_info.variable],
                                            variable_coeficients=[1],
                                            modulo_terms=[],
                                            modulo_term_coeficients=[],
                                            absolute_part=replacement_info.term.modulo - 1,
                                            operation='<=')

            resulting_relations.append(reminder_lower_bound)
            resulting_relations.append(reminder_upper_bound)
            resulting_relations.append(congruence_relation)

        variable_binding_list = [[variable, 'Int'] for variable in sorted(map(lambda info: info.variable, replacement_infos))]
        return ['exists', variable_binding_list, ['and', *resulting_relations]]
    else:
        new_subtree: AST_NaryNode = []
        for subtree in ast:
            processed_subtree = reduce_relation_asts_to_evaluable_leaves(subtree)
            new_subtree.append(processed_subtree)
        return new_subtree


def ast_iter_subtrees(root_node: AST_Node) -> Generator[Tuple[AST_Node, Tuple[AST_NaryNode, int]], None, None]:
    if type(root_node) != list:
        return root_node

    node_name = root_node[0]

    node_descriptions = {
        'assert': [1],
        'not': [1],
        'ite': [1, 2, 3],
        '=>': [1, 2],
        '<=': [1, 2],
        '<': [1, 2],
        '=': [1, 2],
        '>=': [1, 2],
        '>': [1, 2],
        '+': [1, 2],
        '*': [1, 2],
        'mod': [1, 2],
        'exists': [2],
        'forall': [2],
    }

    if node_name == 'let':
        for i, binding in enumerate(root_node[1]):
            _, let_binding_subtree = binding
            yield (let_binding_subtree, (root_node[1], i))
        yield (root_node[2], (root_node, 2))
    elif node_name in ['and', 'or', '-', 'div']:
        # - can be both unary and binary
        for i, operand_tree in enumerate(root_node[1:]):
            yield (operand_tree, (root_node, i + 1))
    else:
        assert node_name in node_descriptions, f'Don\'t know how to descent into {node_name} ({root_node})'
        descend_into_subtrees = node_descriptions[node_name]
        for subtree_index in descend_into_subtrees:
            yield (root_node[subtree_index], (root_node, subtree_index))


def transform_ast(ast: AST_Node,  # NOQA
                  ctx: Dict,
                  node_encountered_handlers: Dict[str, NodeEncounteredHandler],
                  parent_backlink: Optional[Tuple[AST_NaryNode, int]] = None,
                  is_tree_reevaluation_pass: bool = False):

    if 'history' not in ctx:
        ctx['history'] = list()

    if type(ast) != list:
        return

    node_name = ast[0]

    ctx['history'].append(ast)  # Keep track of where in the tree we are

    if node_name in node_encountered_handlers:
        handler = node_encountered_handlers[node_name]
        handler_status = handler(ast, is_tree_reevaluation_pass, ctx)
        reevaluation_root = ast
        if handler_status.is_result_atomic:
            # Replace the reference to a subtree in the parent node with
            # the atomic result
            parent_node, i = parent_backlink
            parent_node[i] = ast[0]
            reevaluation_root = parent_node[i]

        # Re-walk the current node.
        if handler_status.should_reevaluate_result:
            transform_ast(reevaluation_root,
                          ctx,
                          node_encountered_handlers,
                          parent_backlink=parent_backlink,
                          is_tree_reevaluation_pass=True)
            # We don't want to continue with the evaluation - the tree underneath
            # has been changed and will be solved in the recursive call.
            ctx['history'].pop(-1)
            return

    for subtree, backlink in ast_iter_subtrees(ast):
        transform_ast(subtree, ctx, node_encountered_handlers, parent_backlink=backlink)

    ctx['history'].pop(-1)


def fold_in_let_bindings(ast: AST_Node,
                         bindings_stack: List[Dict[str, AST_Node]],
                         path: List[Tuple[AST_Node, int]]) -> int:
    """
    Fold in the expressions (ASTs) bound to variables inside previous let blocks (ala macro expansion).

    The given AST is modified in place.
    """
    if type(ast) != list:
        # We've encountered a string leaf, check if it is bound to something, if yes, expand it.
        for bindings in reversed(bindings_stack):
            if ast in bindings:
                parent, position_in_parent = path[-1]
                parent[position_in_parent] = bindings[ast]
                return 1
        return 0

    node_name = ast[0]
    folds_performed: int = 0
    if node_name == 'let':
        # First try to fold in variables from previous let expressions.
        binding_list = ast[1]
        for i, binding in enumerate(binding_list):
            _, binding_ast = binding
            path.append((ast, i))
            folds_performed += fold_in_let_bindings(binding_ast, bindings_stack, path)
            path.pop(-1)

        # Identify bindings that stand for a literal, or an arithmetic
        # expression - those must be folded in
        bindings_list_without_folded: List[List[AST_Leaf, AST_NaryNode]] = []
        bindings_stack.append({})
        for let_var_name, binding_ast in ast[1]:
            is_arithmetic_expr = type(binding_ast) == list and binding_ast[0] in ['-', '+', '*', 'mod']
            is_literal = type(binding_ast) == str
            if is_arithmetic_expr or is_literal:
                # The current binding must be folded in oder to be able to
                # evaluate the tree
                bindings_stack[-1][let_var_name] = binding_ast
            else:
                bindings_list_without_folded.append([let_var_name, binding_ast])

        # Continue folding down the line.
        path.append((ast, 2))
        folds_performed += fold_in_let_bindings(ast[2], bindings_stack, path)
        path.pop(-1)

        # Check whether some binding in the `let` was left
        if not bindings_list_without_folded:
            # No bingings were left, remove the `let` node alltogether.
            assert path
            parent, position_in_parent = path[-1]
            parent[position_in_parent] = ast[2]

        bindings_stack.pop(-1)
        return folds_performed
    else:
        for subtree, parent_backlink in ast_iter_subtrees(ast):
            path.append(parent_backlink)
            folds_performed += fold_in_let_bindings(subtree, bindings_stack, path)
            path.pop(-1)
        return folds_performed


def expand_implications_handler(ast: AST_NaryNode, is_reeval: bool, ctx: Dict) -> NodeEncounteredHandlerStatus:
    # Expand with: A => B  <<-->> ~A or B
    A = ast[1]
    B = ast[2]

    ast[0] = 'or'
    ast[1] = ['not', A]
    ast[2] = B

    ctx['implications_expanded_cnt'] += 1

    return NodeEncounteredHandlerStatus(True, False)


def remove_double_negations_handler(ast: AST_NaryNode, is_reeval: bool, ctx: Dict) -> NodeEncounteredHandlerStatus:
    subtree = ast[1]
    if type(subtree) == list and subtree[0] == 'not':
        expr_under_double_negation = subtree[1]

        # Empty the current AST root node
        ast.pop(-1)
        ast.pop(-1)

        if type(expr_under_double_negation) == list:
            # Under the double nagation lies a tree, copy the contents of its
            # root node to the current one, effectively replacing the current
            # root with the root of the tree under double negation.
            is_result_atomic = False
            for node_under_double_negation_elem in expr_under_double_negation:
                ast.append(node_under_double_negation_elem)
        else:
            # There is a literal under the double negation, just copy it.
            is_result_atomic = True
            ast.append(expr_under_double_negation)

        ctx['negation_pairs_removed_cnt'] += 1

        return NodeEncounteredHandlerStatus(True, is_result_atomic)

    return NodeEncounteredHandlerStatus(False, False)


def replace_forall_with_exists_handler(ast: AST_NaryNode, is_reeval: bool, ctx: Dict) -> NodeEncounteredHandlerStatus:
    _, binders, stmt = ast

    ast[0] = 'not'
    ast[1] = ['exists', binders, ['not', stmt]]
    ast.pop(-1)  # Remove the original stmt from [forall, binders, stmt] -> [not, [exists, [not, stmt]]]

    ctx['forall_replaced_cnt'] += 1

    return NodeEncounteredHandlerStatus(True, False)


def preprocess_ast(ast):
    '''Peforms preprocessing on the given AST. The following proprocessing operations are performed:
        - universal quantifiers are replaced with existential quantifiers,
        - implications are expanded: `A => B` <<-->> `~A or B`,
        - consequent negation pairs are removed,

    Params:
        ast - The SMT tree to be preprocessed. The preprocessing is performed in place.
    '''

    logger.info('Entering the first preprocessing pass: Folding in arithmetic expressions.')
    folds_performed = fold_in_let_bindings(ast, [], [])
    logger.info(f'Performed {folds_performed} folds.')

    logger.info('Entering the second preprocessing pass: `ite` expansion, `forall` removal, modulo operator expansion.')

    second_pass_transformations = {
        'forall': replace_forall_with_exists_handler,
        'ite': ite_expansion_handler,
        '>=': expand_ite_expressions_inside_presburger_relation,
        '<=': expand_ite_expressions_inside_presburger_relation,
        '=': expand_ite_expressions_inside_presburger_relation,
        '>': expand_ite_expressions_inside_presburger_relation,
        '<': expand_ite_expressions_inside_presburger_relation,
        '=>': expand_implications_handler,
    }

    second_pass_context = {
        'forall_replaced_cnt': 0,
        'modulos_replaced_cnt': 0,
        'ite_expansions_cnt': 0,
        'implications_expanded_cnt': 0
    }
    transform_ast(ast, second_pass_context, second_pass_transformations)

    logger.info('First pass stats: ')
    logger.info(f'Replaced {second_pass_context["forall_replaced_cnt"]} forall quantifiers with exists.')
    logger.info(f'Transformed {second_pass_context["modulos_replaced_cnt"]} modulo expressions into \\exists formulas.')
    logger.info(f'Expanded {second_pass_context["ite_expansions_cnt"]} ite expressions outside of atomic Presburfer formulas.')
    logger.info(f'Expanded {second_pass_context["implications_expanded_cnt"]} implications.')

    logger.info('Entering the third preprocessing pass: double negation removal.')
    third_pass_transformations = {
        'not': remove_double_negations_handler
    }
    third_pass_context = {
        'negation_pairs_removed_cnt': 0,
    }
    transform_ast(ast, third_pass_context, third_pass_transformations)
    logger.info(f'Removed {third_pass_context["negation_pairs_removed_cnt"]} negation pairs.')
