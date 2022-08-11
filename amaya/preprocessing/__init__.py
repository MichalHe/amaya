from dataclasses import dataclass
from itertools import chain
from typing import (
    Dict,
    Generator,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
)

import amaya.ast_relations as relations
from amaya.ast_definitions import (
    AST_Leaf,
    AST_NaryNode,
    AST_Node,
    FunctionSymbol,
    NodeEncounteredHandler,
    NodeEncounteredHandlerStatus,
)
from amaya.relations_structures import (
    DivTerm,
    ModuloTerm,
    NonlinearTermReplacementInfo,
    Relation,
)
from amaya.preprocessing.ite_preprocessing import (
    expand_ite_expressions_inside_presburger_relation,
    ite_expansion_handler,
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


def generate_atomic_constraints_for_replaced_mod_terms(
        replacement_infos: List[NonlinearTermReplacementInfo[ModuloTerm]]) -> List[Relation]:
    """
    Generate the atomic constraints limiting the range of the variables replacing modulo terms, as well as
    the congruence constraints.

    The returned constraints are sorted according to the predicted size of their automata in an ascending order.

    :param replacement_info: Information about what mod term was replaced by what variable.
    """
    constraints: List[Relation] = []
    for replacement_info in replacement_infos:
        reminder_lower_bound = Relation.new_lin_relation(variable_names=[replacement_info.variable],
                                                         variable_coeficients=[-1], absolute_part=0, operation='<=')

        reminder_upper_bound = Relation.new_lin_relation(variable_names=[replacement_info.variable],
                                                         variable_coeficients=[1], operation='<=',
                                                         absolute_part=replacement_info.term.modulo - 1)

        # Modify the original modulo term by subtracting the replacement variable, and use it to form the congruence
        modulo_term = ModuloTerm(variables=replacement_info.term.variables + (replacement_info.variable,),
                                 variable_coeficients=replacement_info.term.variable_coeficients + (-1,),
                                 constant=replacement_info.term.constant, modulo=replacement_info.term.modulo)
        modulo_term = modulo_term.into_sorted()
        congruence = Relation.new_congruence_relation(modulo_terms=[modulo_term],  modulo_term_coeficients=[1])

        constraints.extend((reminder_lower_bound, reminder_upper_bound, congruence))

    return sorted(constraints, key=lambda constraint: constraint.calc_approximate_automaton_size())


def generate_atomic_constraints_for_replaced_div_terms(
        replacement_infos: List[NonlinearTermReplacementInfo[DivTerm]]) -> List[Relation]:
    """
    Generate the atomic constraints limiting the value of the variables that replaced div terms.

    :param replacement_info: Information about what div term was replaced by what variable.
    """
    constraints: List[Relation] = []
    for replacement_info in replacement_infos:
        _vars = replacement_info.term.variables + (replacement_info.variable,)
        _var_coefs = replacement_info.term.variable_coeficients + (-replacement_info.term.divisor,)

        # Sort the variables and their coefficients according to their names
        _vars, _var_coefs = zip(*sorted(zip(_vars, _var_coefs), key=lambda pair: pair[0]))

        reminder_lower_bound = Relation.new_lin_relation(variable_names=list(_vars),
                                                         variable_coeficients=[-coef for coef in _var_coefs],
                                                         absolute_part=0, operation='<=')
        reminder_upper_bound = Relation.new_lin_relation(variable_names=list(_vars),
                                                         variable_coeficients=list(_var_coefs),
                                                         absolute_part=replacement_info.term.divisor - 1,
                                                         operation='<=')

        constraints.extend((reminder_lower_bound, reminder_upper_bound))

    return constraints


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


def rewrite_relations_with_mod_and_div_terms_to_evaluable_atoms(ast: AST_NaryNode):
    if isinstance(ast, Relation):
        relation: Relation = ast
        if relation.direct_construction_exists():
            return relation

        relation_without_modulos, mod_replacements, div_replacements = relation.replace_nonlinear_terms_with_variables()

        # Make sure we are not expanding something that should have a direct construction
        failure_desc = 'Relation did not have a direct construction, yet there were no modulos inside(?)'
        assert mod_replacements or div_replacements, failure_desc

        # We need to add relations expressing modulo/reminder domains etc.
        resulting_relations: List[Relation] = [relation_without_modulos]
        resulting_relations += generate_atomic_constraints_for_replaced_div_terms(div_replacements)
        resulting_relations += generate_atomic_constraints_for_replaced_mod_terms(mod_replacements)

        variable_binding_list = [
            [var, 'Int'] for var in sorted(info.variable for info in chain(div_replacements, mod_replacements))
        ]
        return ['exists', variable_binding_list, ['and', *resulting_relations]]

    if isinstance(ast, str):
        return ast

    node_type = ast[0]

    if node_type in ('or', 'and', 'not', '='):
        rewritten_subtrees = (
            rewrite_relations_with_mod_and_div_terms_to_evaluable_atoms(subtree) for subtree in ast[1:]
        )
        return [node_type, *rewritten_subtrees]
    elif node_type == 'exists':
        rewritten_subtrees = (
            rewrite_relations_with_mod_and_div_terms_to_evaluable_atoms(subtree) for subtree in ast[2:]
        )
        return [node_type, ast[1], *rewritten_subtrees]

    raise ValueError(f'Unknown node: {node_type=} {ast=}')


def ast_iter_subtrees(root_node: AST_Node) -> Generator[Tuple[AST_Node, Tuple[AST_NaryNode, int]], None, None]:
    """
    Iterate over AST subtrees present in the given root_node.

    Some subtress such as bindings in (forall) and (exists) are not iterated.
    :param root_node: Root node which subtrees will be yielded.
    :returns: Funcion is generating tuples containing the subtree node and
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


def expand_let_macros(ast: AST_Node,
                         macro_def_scopes: List[Dict[str, AST_Node]]):
    """Perform let macro expansion."""
    if not isinstance(ast, list):
        # We've encountered a string leaf, check if it is bound to something, if yes, expand it.
        for macro_def_scope in reversed(macro_def_scopes):
            if ast in macro_def_scope:
                return macro_def_scope[ast]
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
class VarDisambiguationInfo:
    new_name: str
    conflict_count: int


def _disambiguate_variables_rec(ast: AST_Node,
                                variable_rename_map: Dict[str, VarDisambiguationInfo]) -> AST_Node:
    if isinstance(ast, str):
        if ast in variable_rename_map:
            return variable_rename_map[ast].new_name
        return ast
    elif isinstance(ast, int):
        return ast
    elif isinstance(ast, Relation):
        # This branch is kept for robustness of this functionality, it might not be hit - depends on the amount of
        # preprocessing work already done.
        relation: Relation = ast
        relation.variable_names = list(variable_rename_map[var_name] for var_name in relation.variable_names)
        for mod_term in relation.modulo_terms:
            mod_term.variables = tuple(variable_rename_map[var_name] for var_name in mod_term.variables)
        for div_term in relation.div_terms:
            div_term.variables = tuple(variable_rename_map[var_name] for var_name in div_term.variables)
        return ast

    assert isinstance(ast, list)
    node_type = ast[0]

    if node_type in ('exists', 'forall'):
        new_variables = tuple(var_name for var_name, dummy_var_type in ast[1])

        # Update variable_rename_map so that the variables can be renamed further down the AST
        disambiguated_quantifier_binding_list = []
        for i, var_name in enumerate(new_variables):
            var_type: str = ast[1][i][1]
            conflicting_disambiguation_entries: Dict[str, VarDisambiguationInfo] = {}
            if var_name in variable_rename_map:
                old_disambiguation_info = variable_rename_map[var_name]
                conflicting_disambiguation_entries[var_name] = old_disambiguation_info
                new_var_name = f'{var_name}#{old_disambiguation_info.conflict_count + 1}'
                new_disambiguation_info = VarDisambiguationInfo(new_name=new_var_name, conflict_count=old_disambiguation_info.conflict_count + 1)
                variable_rename_map[var_name] = new_disambiguation_info
                disambiguated_quantifier_binding_list.append([new_var_name, var_type])
            else:
                new_disambiguation_info = VarDisambiguationInfo(new_name=f'{var_name}', conflict_count=0)
                variable_rename_map[var_name] = new_disambiguation_info
                disambiguated_quantifier_binding_list.append([var_name, var_type])

        disambiguated_subast = _disambiguate_variables_rec(ast[2], variable_rename_map)

        # Restore the names to which should the conflicting variables in the surrounding scope be renamed, however,
        # keep the new conflict count, in order to be able to generate unique variable names when new conflict is seen.
        for var_name, old_disambiguation_info in conflicting_disambiguation_entries.items():
            new_conflict_count = variable_rename_map[var_name].conflict_count
            variable_rename_map[var_name] = VarDisambiguationInfo(new_name=old_disambiguation_info.new_name, conflict_count=new_conflict_count)
        return [node_type, disambiguated_quantifier_binding_list, disambiguated_subast]

    elif node_type in ('and', 'or', 'not', '<=', '<', '>', '>=', '=', '+', '-', 'mod', 'div', '*'):
        disambiguated_subasts = (_disambiguate_variables_rec(subtree, variable_rename_map) for subtree in ast[1:])
        return [node_type, *disambiguated_subasts]

    raise NotImplementedError(f'[Variable name disambiguation] Unhandled {node_type=} while traversing ast.')


def disambiguate_variables(ast: AST_Node, constant_function_symbols: Iterable[FunctionSymbol]) -> AST_Node:
    """Modifies the AST so that all variables have unique names."""
    variable_rename_map = {
        fn_symbol.name: VarDisambiguationInfo(new_name=fn_symbol.name, conflict_count=0) for fn_symbol in constant_function_symbols
    }
    return _disambiguate_variables_rec(ast, variable_rename_map)


def preprocess_ast(ast: AST_Node,
                   constant_function_symbols: Iterable[FunctionSymbol],
                   solver_config: SolverConfig = solver_config) -> AST_Node:
    """
    Peforms preprocessing on the given AST. The following proprocessing operations are performed:
        - universal quantifiers are replaced with existential quantifiers,
        - implications are expanded: `A => B` <<-->> `~A or B`,
        - consequent negation pairs are removed,

    Params:
        ast - The SMT tree to be preprocessed. The preprocessing is performed in place.
    """

    logger.debug('[Preprocessing] original AST: %s', ast)
    ast = expand_let_macros(ast, [])
    logger.debug('[Preprocessing] AST after let macro expansion: %s', ast)

    logger.info('Entering the second preprocessing pass: `ite` expansion, `forall` removal.')

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
        'ite_expansions_cnt': 0,
        'implications_expanded_cnt': 0
    }
    transform_ast(ast, second_pass_context, second_pass_transformations)

    logger.debug('[Preprocessing] AST after ite expansion, implications rewriting, and forall rewriting: %s', ast)

    logger.info('First pass stats: ')
    logger.info('Replaced %d forall quantifiers with exists.', second_pass_context["forall_replaced_cnt"])
    logger.info('Expanded %d ite expressions outside of atomic Presburfer formulas.', second_pass_context["ite_expansions_cnt"])
    logger.info('Expanded %d implications.', second_pass_context["implications_expanded_cnt"])

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
        ast = disambiguate_variables(ast, constant_function_symbols)

    return ast
