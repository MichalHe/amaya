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
from amaya.preprocessing.eval import convert_ast_into_evaluable_form

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


@dataclass
class Var_Scope_Info:
    scope_id: int
    """The number (ID) of the variable scope the currently examined variable belongs to."""

    def put_scope_id_into_name(self, var_name: str) -> str:
        return f'{var_name}{solver_config.disambiguation_scope_separator}{self.scope_id}'


TreeType = TypeVar('TreeType', Raw_AST, AST_Node)


def _disambiguate_vars(ast: TreeType, var_scope_info: Dict[str, Var_Scope_Info], var_scope_cnts: Dict[str, int]) -> TreeType:
    """
    Give every number a unique suffix so that every variable in the formula has an unique name.

    Param:
        - var_scope_info: Maps a variable to the actual scope it is in so that an unique suffix with scope id can be generated.
        - var_scope_cnts: Counts the number of different scopes the variable has been seen so far so that a different suffix
                          would be generated for a variable in a newly encountered context.
    """

    undeclared_var_err = ('Trying to disambiguate variable {var} of with unknown scope. Although '
                          'it can be deduced that the scope should be global, the decision '
                          'procedure has to know variable sorts to construct correct automata '
                          '- all vars have to be pre-declared.')

    def atom_renamer(var: str) -> str:
        if not var in var_scope_info:
            raise ValueError(undeclared_var_err.format(var=var))
        return var_scope_info[var].put_scope_id_into_name(var)

    if isinstance(ast, str):
        if ast in var_scope_info:
            disambiguated_var: TreeType = var_scope_info[ast].put_scope_id_into_name(ast)   # type: ignore
            return disambiguated_var
        return ast
    elif isinstance(ast, int):
        return ast
    elif isinstance(ast, Relation):
        # This branch might not be hit if the relations were not yet condensed into relations.
        relation: Relation = ast
        relation.rename_variables(atom_renamer)
        return relation
    elif isinstance(ast, Congruence):
        congruence: Congruence = ast
        congruence.rename_vars(atom_renamer)
        return congruence

    assert isinstance(ast, list)
    node_type = ast[0]

    if node_type in ('exists', 'forall'):
        new_scope_info: Dict[str, Var_Scope_Info] = dict(var_scope_info)
        quantified_vars = tuple(var_name for var_name, dummy_var_type in ast[1])

        disambiguated_quantified_vars = []
        for i, var_name in enumerate(quantified_vars):
            this_scope_id = var_scope_cnts.get(var_name, 0)
            var_scope_cnts[var_name] = this_scope_id + 1
            scope_info = Var_Scope_Info(scope_id=this_scope_id)
            new_scope_info[var_name] = scope_info

            var_type: str = ast[1][i][1]
            disambiguated_quantified_vars.append([scope_info.put_scope_id_into_name(var_name), var_type])

        disambiguated_subast = _disambiguate_vars(ast[2], new_scope_info, var_scope_cnts)

        return [node_type, disambiguated_quantified_vars, disambiguated_subast]

    elif node_type in ('and', 'or', 'not', '<=', '<', '>', '>=', '=', '+', '-', 'mod', 'div', '*'):
        disambiguated_subasts = (_disambiguate_vars(subtree, var_scope_info, var_scope_cnts) for subtree in ast[1:])
        return [node_type, *disambiguated_subasts]

    raise NotImplementedError(f'[Variable name disambiguation] Unhandled {node_type=} while traversing ast.')


def disambiguate_variables(ast: TreeType, constant_function_symbols: Iterable[FunctionSymbol]) -> Tuple[Iterable[Tuple[FunctionSymbol, FunctionSymbol]], TreeType]:
    """Modifies the AST so that all variables have unique names."""
    global_scope_info: Dict[str, Var_Scope_Info] = {}
    var_scope_cnt: Dict[str, int] = {}
    for constatnt_symbol in constant_function_symbols:
        global_scope_info[constatnt_symbol.name] = Var_Scope_Info(scope_id=0)
        var_scope_cnt[constatnt_symbol.name] = 1

    disambiguated_tree = _disambiguate_vars(ast, global_scope_info, var_scope_cnt)

    # We have likely changed also how are the global symbols named, therefore, we have to disambiguate them
    # as well so thay can be injected into the evaluation context
    disambiguated_global_symbols = []
    for symbol in constant_function_symbols:
        new_symbol = FunctionSymbol(name=global_scope_info[symbol.name].put_scope_id_into_name(symbol.name),
                                    arity=symbol.arity, args=symbol.args, return_type=symbol.return_type)
        disambiguated_global_symbols.append((symbol, new_symbol))

    return (disambiguated_global_symbols, disambiguated_tree)



class VariableNamer(object):
    def __init__(self):
        self.next_variable_id = 0
        self.name_table: Dict[str, str] = {}

    def __call__(self, var_name: str) -> str:
        if var_name in self.name_table:
            return self.name_table[var_name]

        new_name = f'X{self.next_variable_id}'
        self.name_table[var_name] = new_name
        self.next_variable_id += 1
        return new_name



def _assign_fresh_names_to_all_vars_weak(ast: AST_Node,
                                         namer: Callable[[str], str]) -> AST_Node:
    if isinstance(ast, str):  # Boolean variable
        new_name = namer(ast)
        return new_name

    if isinstance(ast, Congruence):
        congruence = ast.rename_vars(namer)
        return congruence

    if isinstance(ast, Relation):
        ast.rename_variables(namer)  # The modification is done in-place
        return ast

    if isinstance(ast, BoolLiteral):
        return ast

    assert isinstance(ast, list), 'Unhandled node type while assigninig fresh variable names'

    node_type: str = ast[0]  # type: ignore
    if node_type == AST_Node_Names.EXISTS.value:
        bindings: List[List[str]] = ast[1]  # type:ignore
        new_bindings = [(namer(var), sort) for var, sort in bindings]
        new_subformula = _assign_fresh_names_to_all_vars_weak(ast[2], namer)
        return make_exists_node(new_bindings, new_subformula)

    if node_type == AST_Node_Names.AND.value:
        new_subformulae = [_assign_fresh_names_to_all_vars_weak(subformula, namer) for subformula in ast[1:]]
        return make_and_node(new_subformulae)

    if node_type == AST_Node_Names.OR.value:
        new_subformulae = [_assign_fresh_names_to_all_vars_weak(subformula, namer) for subformula in ast[1:]]
        return make_or_node(new_subformulae)

    if node_type == AST_Node_Names.NOT.value:
        new_subformula = _assign_fresh_names_to_all_vars_weak(ast[1], namer)
        return make_not_node(new_subformula)

    assert False, f'Unhandled node: {ast}'


def assign_fresh_names_to_all_vars_weak(ast: AST_Node, fn_symbols: Iterable[FunctionSymbol]) -> Tuple[AST_Node, Iterable[FunctionSymbol], Dict[str, str]]:
    """
    Assign new variable names X<var_id> to every variable in the tree.

    The function is weak - expects the tree to be disabiguated first.
    """
    namer = VariableNamer()

    def rename_function_symbol(fn_symbol: FunctionSymbol) -> FunctionSymbol:
        return FunctionSymbol(name=namer(fn_symbol.name), arity=fn_symbol.arity,
                              args=list(fn_symbol.args), return_type=fn_symbol.return_type)

    new_fn_symbols = [rename_function_symbol(sym) for sym in fn_symbols]
    new_ast = _assign_fresh_names_to_all_vars_weak(ast, namer)
    return (new_ast, new_fn_symbols, namer.name_table)


def preprocess_ast(ast: Raw_AST,
                   constant_function_symbols: Iterable[FunctionSymbol],
                   bool_vars: Set[str],
                   solver_config: SolverConfig = solver_config) -> Tuple[Iterable[Tuple[FunctionSymbol, FunctionSymbol]], AST_Node]:
    """
    Peforms preprocessing on the given AST. The following proprocessing operations are performed:
        - universal quantifiers are replaced with existential quantifiers,
        - implications are expanded: `A => B` <<-->> `~A or B`,
        - consequent negation pairs are removed,

    Params:
        - ast - The SMT tree to be preprocessed. The preprocessing is performed in place.
        - constant_function_symbols - Global function symbols with with 0args (global vars)
    Returns:
        - A tuple (modified_constant_function_symbols, modified_ast). The constant function symbols might
          be modified due to, e.g., variable disambiguation.
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

    fn_symbols = constant_function_symbols
    disambiguated_vars = False
    if solver_config.preprocessing.disambiguate_variables:
        logger.info('Disambiguating variables.')
        fn_symbol_changes, ast = disambiguate_variables(ast, constant_function_symbols)
        fn_symbols = [new_sym for old_sym, new_sym in fn_symbol_changes]

        new_bool_vars = set()
        for old_sym, new_sym in fn_symbol_changes:
            if old_sym.name in bool_vars:
                new_bool_vars.add(new_sym.name)

        bool_vars = new_bool_vars
        disambiguated_vars = True
    else:
        fn_symbol_changes = [(sym, sym) for sym in fn_symbols]

    logger.info('Condensing atomic relation ASTs into AST leaves.')
    evaluable_ast, _ = convert_ast_into_evaluable_form(ast, bool_vars)

    if disambiguated_vars and solver_config.preprocessing.assign_new_variable_names:
        evaluable_ast, fn_symbols, name_table = assign_fresh_names_to_all_vars_weak(evaluable_ast, fn_symbols)
    else:
        fn_symbols = constant_function_symbols

    return fn_symbol_changes, evaluable_ast
