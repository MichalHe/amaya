from dataclasses import dataclass
import collections
import itertools
from typing import (
    Any,
    Callable,
    Dict,
    Generator,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
    TypeVar,
    Union,
)
from amaya.preprocessing.eval import VarInfo, convert_ast_into_evaluable_form

from amaya.relations_structures import (
    AST_NaryNode,
    AST_Node,
    AST_Node_Names,
    BoolLiteral,
    Congruence,
    FunctionSymbol,
    NodeEncounteredHandler,
    NodeEncounteredHandlerStatus,
    Raw_AST,
    Relation,
    Var,
    make_and_node,
    make_exists_node,
    make_not_node,
    make_or_node,
)
from amaya.preprocessing.ite_preprocessing import (
    rewrite_ite_expressions,
)
from amaya import (
    logger,
    utils,
)
from amaya.config import (
    SolverConfig,
    solver_config,
)


def is_presburger_term(ast: AST_Node, bool_vars: Set[str]) -> bool:
    """
    Returns true if the given ast represents a Presburger arithmetics term.
    """
    if not isinstance(ast, list):
        return ast not in bool_vars
    root = ast[0]
    return root in {'+', '-', '*', 'mod', 'div'}


def is_ast_bool_equavalence(ast: AST_Node, bool_fn_symbols: Set[str]):
    """
    Check whether the given ast encodes the equivalence of two Booleans.
    :returns: True if the AST represents a Boolean equivalence instead of Presburger equality.
    """
    if not isinstance(ast, list) or ast[0] != '=':
        return False

    left_subtree, right_subtree = ast[1], ast[2]

    return not (
        is_presburger_term(left_subtree, bool_fn_symbols) and is_presburger_term(right_subtree, bool_fn_symbols)
    )


BindingList = List[List[str]]


def ast_iter_subtrees(root_node: AST_Node) -> Generator[Tuple[AST_Node, Tuple[AST_NaryNode, int]], None, None]:
    """
    Iterate over AST subtrees present in the given root_node.

    Some subtress such as bindings in (forall) and (exists) are not iterated.
    :param root_node: Root node which subtrees will be yielded.
    :returns: Function is generating tuples containing the subtree node and
              a tuple containing a parent and index which points to the subtree.
    """
    if not isinstance(root_node, list):
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


def transform_ast(ast: Raw_AST,  # NOQA
                  ctx: Dict,
                  node_encountered_handlers: Dict[str, NodeEncounteredHandler],
                  parent_backlink: Optional[Tuple[AST_NaryNode, int]] = None,
                  is_tree_reevaluation_pass: bool = False):

    if 'history' not in ctx:
        ctx['history'] = list()

    if type(ast) != list:
        return

    node_name = ast[0]
    assert isinstance(node_name, str)

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


Arbitrary_AST = Union[List["Arbitrary_AST"], str, int]


def copy_ast(ast: Arbitrary_AST) -> Arbitrary_AST:
    if isinstance(ast, str) or isinstance(ast, int):
        return ast

    assert isinstance(ast, list)

    return [copy_ast(item) for item in ast]


def expand_let_macros(ast: Raw_AST, macro_def_scopes: List[Dict[str, Raw_AST]]) -> Raw_AST:
    """Perform let macro expansion."""
    if not isinstance(ast, list):
        # We've encountered a string leaf, check if it is bound to something, if yes, expand it.
        for macro_def_scope in reversed(macro_def_scopes):
            if ast in macro_def_scope:
                return copy_ast(macro_def_scope[ast])
        return ast

    node_name = ast[0]

    if node_name == 'let':
        # The new S-expressions in the let binding might contain variables pointing to previously bound S-expressions.
        # We have to first fold in the macros carried to this node into the new S-expressions - only we can use them.
        macro_defs = ast[1]
        macro_defs_with_prev_macros_folded_in = [
            (macro_name, expand_let_macros(macro_body, macro_def_scopes)) for macro_name, macro_body in macro_defs
        ]

        # Make a new macro definition scope, and populate it with the current macro definitions
        macro_def_scopes.append(dict(macro_defs_with_prev_macros_folded_in))

        # Continue down the tree, however, return only the AST subtree from the current let expr with the macros folded in - remove the let node
        folded_subtree = expand_let_macros(ast[2], macro_def_scopes)

        macro_def_scopes.pop(-1)
        return folded_subtree
    elif node_name in ('exists', 'forall'):
        ast_with_folded_macros = [node_name, ast[1]]
        for subtree in ast[2:]:
            subtree_with_folded_macro = expand_let_macros(subtree, macro_def_scopes)
            ast_with_folded_macros.append(subtree_with_folded_macro)
        return ast_with_folded_macros
    elif node_name in ('and', 'or', 'not', '=', '<=', '<', '>=', '>', '+', '-', '*', 'mod', 'div', 'ite', '=>'):
        ast_with_folded_macros: Raw_AST = [node_name]
        for subtree in ast[1:]:
            subtree_with_folded_macro = expand_let_macros(subtree, macro_def_scopes)
            ast_with_folded_macros.append(subtree_with_folded_macro)
        return ast_with_folded_macros
    else:
        raise ValueError(f'Cannot fold in macros into the AST: {ast=}')


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


TreeType = TypeVar('TreeType', Raw_AST, AST_Node)


def assign_fresh_names_to_all_vars(var_table: Dict[Var, VarInfo]) -> Dict[Var, VarInfo]:
    """
    Assign new variable names X<var_id> to every variable in the tree.
    """
    new_var_table: Dict[Var, VarInfo] = {}

    i = 0
    for var, var_info in var_table.items():
        new_var_table[var] = VarInfo(name=f'X{i}', type=var_info.type)
    return new_var_table


def preprocess_ast(ast: Raw_AST,
                   global_fn_symbols: Iterable[FunctionSymbol],
                   solver_config: SolverConfig = solver_config) -> Tuple[AST_Node, Dict[Var, VarInfo]]:
    """
    Peforms preprocessing on the given AST. The following proprocessing operations are performed:
        - universal quantifiers are replaced with existential quantifiers,
        - implications are expanded: `A => B` <<-->> `~A or B`,
        - consequent negation pairs are removed,
        - relations are reduced to directly evaluable forms (Relation, Congruence)
        - all string variables are disabiguated and their occurrences are replaced by corresponding Var(ID)
          The variable names and types can be resolved from the returned variable table.
    Params:
        - ast - The SMT tree to be preprocessed. The preprocessing is performed in place.
        - global_fn_symbols - Global (constant) function symbols with with 0args (global vars)
    Returns:
        - A tuple (modified_ast, var_table).
     """

    logger.debug('[Preprocessing] original AST: %s', ast)
    ast = expand_let_macros(ast, [])
    logger.debug('[Preprocessing] AST after let macro expansion: %s', ast)

    logger.info('[Preprocessing] Rewriting if-then-else expressions.')
    ast = rewrite_ite_expressions(ast)

    third_pass_transformations = {
        'forall': replace_forall_with_exists_handler,
        '=>': expand_implications_handler,
    }

    third_pass_context = {
        'forall_replaced_cnt': 0,
        'implications_expanded_cnt': 0
    }
    transform_ast(ast, third_pass_context, third_pass_transformations)

    logger.debug('[Preprocessing] AST after ite expansion, implications rewriting, and forall rewriting: %s', ast)

    logger.info('First pass stats: ')
    logger.info('Replaced %d forall quantifiers with exists.', third_pass_context["forall_replaced_cnt"])
    logger.info('Expanded %d implications.', third_pass_context["implications_expanded_cnt"])

    logger.info('Entering the third preprocessing pass: double negation removal.')
    third_pass_transformations = {
        'not': remove_double_negations_handler
    }
    third_pass_context = {
        'negation_pairs_removed_cnt': 0,
    }
    transform_ast(ast, third_pass_context, third_pass_transformations)
    logger.info('Removed %d negation pairs.', third_pass_context["negation_pairs_removed_cnt"])

    logger.info('Condensing atomic relation ASTs into AST leaves.')
    evaluable_ast, var_table = convert_ast_into_evaluable_form(ast, global_fn_symbols)

    if solver_config.preprocessing.assign_new_variable_names:
        var_table = assign_fresh_names_to_all_vars(var_table)

    return evaluable_ast, var_table


def _flatten_bool_nary_connectives(ast: AST_Node) -> AST_Node:
    if not isinstance(ast, list):
        return ast

    parent_type: str = ast[0]  # type: ignore

    connectives_to_flatten = (AST_Node_Names.AND.value, AST_Node_Names.OR.value)
    if parent_type in connectives_to_flatten:

        new_node: AST_Node = [parent_type]

        for child in ast[1:]:
            flattened_child = _flatten_bool_nary_connectives(child)
            is_nary_node = isinstance(flattened_child , list)
            if is_nary_node and flattened_child[0] == parent_type:
                new_node.extend(flattened_child[1:])
            else:
                new_node.append(flattened_child)

        return new_node

    if parent_type == AST_Node_Names.EXISTS.value:
        new_child = _flatten_bool_nary_connectives(ast[2])
        return [parent_type, ast[1], new_child]

    if parent_type == AST_Node_Names.NOT.value:
        new_child = _flatten_bool_nary_connectives(ast[1])
        return [parent_type, new_child]

    logger.warning(f'Node {parent_type} is not explicitly handled when flattening bool connectives.')
    return [parent_type, *(_flatten_bool_nary_connectives(child) for child in ast[1:])]


def flatten_bool_nary_connectives(ast: AST_Node) -> AST_Node:
    return _flatten_bool_nary_connectives(ast)
