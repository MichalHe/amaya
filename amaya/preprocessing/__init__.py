from dataclasses import dataclass
import collections
import itertools
from typing import (
    Any,
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

from amaya.ast_definitions import (
    AST_Leaf,
    AST_NaryNode,
    AST_Node,
    FunctionSymbol,
    NodeEncounteredHandler,
    NodeEncounteredHandlerStatus,
)
import amaya.ast_relations as relations
from amaya.relations_structures import (
    DivTerm,
    ModuloTerm,
    Relation,
    RewritableTerm,
    TermRewrites,
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


def generate_atomic_constraints_for_replaced_terms(rewrites: Dict[RewritableTerm, str]) -> List[Relation]:
    """
    Generate the atomic constraints to semantically bind the introduced variable with the original term.

    The returned constraints are sorted according to the predicted size of their automata in an ascending order.

    :param rewrites: Information about what term was replaced by what variable.
    """
    constraints: List[Relation] = []
    for term, variable in rewrites.items():
        if isinstance(term, ModuloTerm):
            reminder_lower_bound = Relation.new_lin_relation(variable_names=[variable],
                                                             variable_coefficients=[-1], absolute_part=0, predicate_symbol='<=')

            reminder_upper_bound = Relation.new_lin_relation(variable_names=[variable],
                                                             variable_coefficients=[1], predicate_symbol='<=',
                                                             absolute_part=term.modulo - 1)

            # The difference of the original variables and the rewrite variable should be congruent to 0
            modulo_term = ModuloTerm(variables=term.variables + (variable,),
                                     variable_coefficients=term.variable_coefficients + (-1,),
                                     constant=term.constant, modulo=term.modulo)

            modulo_term = modulo_term.into_sorted()
            congruence = Relation.new_congruence_relation(modulo_terms=[modulo_term], modulo_term_coefficients=[1])

            constraints.extend((reminder_lower_bound, reminder_upper_bound, congruence))
        else:
            _vars = term.variables + (variable,)
            _var_coefs = term.variable_coefficients + (-term.divisor,)

            # Sort the variables and their coefficients according to their names
            _vars, _var_coefs = zip(*sorted(zip(_vars, _var_coefs), key=lambda pair: pair[0]))

            # Create bounds limiting the divisor so that the original_expr - divisor*var gives a reminder as
            # when performing integer division
            reminder_lower_bound = Relation.new_lin_relation(variable_names=list(_vars),
                                                             variable_coefficients=[-coef for coef in _var_coefs],
                                                             absolute_part=0, predicate_symbol='<=')

            reminder_upper_bound = Relation.new_lin_relation(variable_names=list(_vars),
                                                             variable_coefficients=list(_var_coefs),
                                                             absolute_part=term.divisor - 1,
                                                             predicate_symbol='<=')
            constraints.extend((reminder_lower_bound, reminder_upper_bound))

    return sorted(constraints, key=lambda constraint: constraint.calc_approximate_automaton_size())


def condense_relation_asts_to_relations(ast: AST_NaryNode, bool_fn_symbols: Set[str]) -> AST_Node:
    """Walks the AST and replaces subtrees representing atoms with Relation instances."""
    if not isinstance(ast, list):
        return ast

    node_type = ast[0]

    if node_type in ['<', '>', '<=', '>=', '=']:
        # The = symbol can stand for either equivalence of two formulae, or Presbuger equality
        if not (node_type == '=' and is_ast_bool_equavalence(ast, bool_fn_symbols)):
            relation = relations.extract_relation(ast)
            relation.ensure_canoical_form_if_equation()
            return relation

    reduced_subtrees = (
        condense_relation_asts_to_relations(subtree, bool_fn_symbols) for subtree in ast[1:]
    )
    return [node_type, *reduced_subtrees]


BindingList = List[List[str]]


def _rewrite_terms_in_relations(relations: List[Relation],
                                rewrite_info: TermRewrites,
                                vars_in_rewritten_terms: Optional[Set[str]] = None) -> Tuple[List[Relation], BindingList, List[Relation]]:
    # We don't want to rewrite modulo terms if they occur only once and that is in the form of congruence
    mod_term_uses: Dict[RewritableTerm, List[Relation]] = collections.defaultdict(list)
    for relation in relations:
        for term in relation.modulo_terms:
            mod_term_uses[term].append(relation)

    def is_only_in_congruence(term_relations: List[Relation]) -> bool:
        return len(term_relations) == 1 and term_relations[0].is_congruence_equality()

    congruence_relations = [
        term_relations[0] for term, term_relations in mod_term_uses.items() if is_only_in_congruence(term_relations)
    ]

    vars_rewriting_terms: Dict[RewritableTerm, str] = {}
    relations_to_propagate: List[Relation] = []
    for relation in relations:

        # @Optimize: This performs a linear search in the list of relations, but there should not be many of them
        if relation in congruence_relations:
            continue

        relation.replace_chosen_nonlinear_terms_with_variables(vars_in_rewritten_terms, vars_rewriting_terms, rewrite_info)
        if relation.modulo_terms or relation.div_terms:
            relations_to_propagate.append(relation)
    binding_list = [[var, 'Int'] for var in vars_rewriting_terms.values()]

    atoms = generate_atomic_constraints_for_replaced_terms(vars_rewriting_terms)
    return relations_to_propagate, binding_list, atoms


def _rewrite_nonlinear_terms(ast: AST_NaryNode, rewrite_info: TermRewrites) -> Tuple[List[Relation], AST_NaryNode]:
    if isinstance(ast, Relation):
        relation: Relation = ast

        rewrite_candidate = [relation] if relation.modulo_terms or relation.div_terms else []
        return (rewrite_candidate, relation)

    if isinstance(ast, str):
        return ([], ast)

    node_type = ast[0]

    if node_type in ('or', 'and', 'not', '='):
        rewrite_results = (_rewrite_nonlinear_terms(subtree, rewrite_info) for subtree in ast[1:])

        subtree_relations, subtrees = zip(*rewrite_results)
        subtree_relations = itertools.chain(*subtree_relations)

        return (list(subtree_relations), [node_type, *subtrees])
    elif node_type == 'exists':
        subtree = ast[2]
        quantified_vars = set(var for var, _type in ast[1])

        relations, rewritten_subtree = _rewrite_nonlinear_terms(subtree, rewrite_info)

        relations_to_propagate, binding_list, new_atoms = _rewrite_terms_in_relations(relations, rewrite_info, quantified_vars)

        if new_atoms:
            term_vars_limits = ['and', *new_atoms]
            if isinstance(rewritten_subtree, list) and rewritten_subtree[0] == 'and':
                term_vars_limits += rewritten_subtree[1:]
            else:
                term_vars_limits.append(rewritten_subtree)
            rewritten_subtree = term_vars_limits

        extended_binding_list = ast[1] + binding_list
        return (relations_to_propagate, ['exists', extended_binding_list, rewritten_subtree])

    raise ValueError(f'Unknown node: {node_type=} {ast=}')


def rewrite_nonlinear_terms(ast: AST_NaryNode) -> AST_NaryNode:
    rewrite_info = TermRewrites(count=0)
    relations_with_nonlinear_terms, rewritten_formula = _rewrite_nonlinear_terms(ast, rewrite_info)

    # Some relations might contain terms consisting entirely of free variables
    if relations_with_nonlinear_terms:
        reminding_relations, binding_list, new_atoms = _rewrite_terms_in_relations(relations_with_nonlinear_terms, rewrite_info, vars_in_rewritten_terms=None)  # Rewrite all
        return ['exists', binding_list, ['and', *new_atoms, rewritten_formula]]

    return rewritten_formula


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


Arbitrary_AST = Union[List["Arbitrary_AST"], str, int]


def copy_ast(ast: Arbitrary_AST) -> Arbitrary_AST:
    if isinstance(ast, str) or isinstance(ast, int):
        return ast
    elif isinstance(ast, Relation):
        return Relation.copy_of(ast)

    assert isinstance(ast, list)

    return [copy_ast(item) for item in ast]


def expand_let_macros(ast: AST_Node,
                         macro_def_scopes: List[Dict[str, AST_Node]]):
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
        ast_with_folded_macros = [node_name]
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
        return f'{var_name}#{self.scope_id}'


def _disambiguate_vars(ast: AST_Node, var_scope_info: Dict[str, Var_Scope_Info], var_scope_cnts: Dict[str, int]) -> AST_Node:
    """
    Give every number a unique suffix so that every variable in the formula has an unique name.

    Param:
        - var_scope_info: Maps a variable to the actual scope it is in so that an unique suffix with scope id can be generated.
        - var_scope_cnts: Counts the number of different scopes the variable has been seen so far so that a different suffix
                          would be generated for a variable in a newly encountered context.
    """
    if isinstance(ast, str):
        if ast in var_scope_info:
            return var_scope_info[ast].put_scope_id_into_name(ast)
        return ast
    elif isinstance(ast, int):
        return ast
    elif isinstance(ast, Relation):
        # This branch might not be hit if the relations were not yet condensed into relations.
        relation: Relation = ast
        relation.rename_variables(lambda var: var_scope_info[var].put_scope_id_into_name(var))
        return ast

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


def disambiguate_variables(ast: AST_Node, constant_function_symbols: Iterable[FunctionSymbol]) -> Tuple[Iterable[FunctionSymbol], AST_Node]:
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
        disambiguated_global_symbols.append(new_symbol)

    return (disambiguated_global_symbols, disambiguated_tree)


def preprocess_ast(ast: AST_Node,
                   constant_function_symbols: Iterable[FunctionSymbol],
                   solver_config: SolverConfig = solver_config) -> Tuple[Iterable[FunctionSymbol], AST_Node]:
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

    if solver_config.preprocessing.disambiguate_variables:
        disambiguated_global_symbols, ast = disambiguate_variables(ast, constant_function_symbols)
    else:
        disambiguated_global_symbols = constant_function_symbols

    return disambiguated_global_symbols, ast
