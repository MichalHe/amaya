from __future__ import annotations
from dataclasses import dataclass

from typing import (
    Dict,
    Set,
    Optional,
    Any
)
from amaya import logger
from amaya.relations_structures import (
    DivTerm,
    ModuloTerm,
    PresburgerExpr,
    Relation,
)
from amaya.utils import number_to_bit_tuple


def evaluate_expression_ast(expr) -> PresburgerExpr:
    """
    Evaluates the given expression AST and returns the (normalized) result.

    Example:
        expr=[+ [* 10 x] y] ----> 10x + y
    """
    if not isinstance(expr, list):
        # It is an atom, which is either int, or variable
        try:
            atom_int_value = int(expr)
            return PresburgerExpr(
                absolute_part=atom_int_value,
                variables=dict(),
                modulo_terms=dict()
            )
        except ValueError:
            variable_name = expr
            return PresburgerExpr(
                absolute_part=0,
                variables={variable_name: 1},
                modulo_terms=dict()
            )

    operation = expr[0]
    if operation == '-':
        if len(expr) == 2:
            return -evaluate_expression_ast(expr[1])  # Negate expr
        else:
            operand1 = evaluate_expression_ast(expr[1])
            operand2 = evaluate_expression_ast(expr[2])
            return operand1 - operand2
    elif operation == '+':
        acc = evaluate_expression_ast(expr[1])
        for operand in expr[2:]:
            acc += evaluate_expression_ast(operand)
        return acc
    elif operation == '*':
        operand1 = evaluate_expression_ast(expr[1])
        operand2 = evaluate_expression_ast(expr[2])

        # (* (+ 10 x) (- 20 y)) --> PrA disallows variable multiplication - would violate Godel's first incompleteness
        try:
            return operand1 * operand2
        except ValueError:
            err = (f'Error while evaluating {expr} -- attempting to multiply'
                   'variables by variables, which is forbidden in PA.')
            raise ValueError(err)
    elif operation == 'mod':
        # (mod (+ x y) 10)
        variables_expr = evaluate_expression_ast(expr[1])
        modul = evaluate_expression_ast(expr[2])  # The modulo might be a a constexpr not just a literal

        if not modul.is_constexpr():
            raise(f'The modulo term does not have a constant as a right operand: {modul}')

        modulo_term = ModuloTerm.from_expression(variables_expr, modul.absolute_part)
        return PresburgerExpr.from_single_modulo_term(modulo_term)
    elif operation == 'div':
        expr_to_divide = evaluate_expression_ast(expr[1])
        divisor = evaluate_expression_ast(expr[2])

        if not divisor.is_constexpr():
            raise ValueError(f'The divisor inside a div term must be a constant expression: {expr}')

        div_term = DivTerm.from_expression(expr_to_divide, divisor.absolute_part)
        return PresburgerExpr(div_terms={div_term: 1})

    else:
        raise ValueError(f'Unsupported operation type: {operation} in expr: {expr}')


def normalize_atomic_presburger_formula(rel_type: str, lhs_expr: PresburgerExpr, rhs_expr: PresburgerExpr) -> Relation:
    """
    Takes an automic formula of form: <expr> <op> <expr>, and produces output in the <VARIABLES> ~ <ABS> form
    where ~ is `<=` or `>=`.

    :param rel_type: Relation type, one of {<=, <, =, >, >=}
    :param lhs_expr: The expression that is present on the left-hand side
    :param rhs_expr: The expression that is present on the right-hand side
    :returns: Relation that has variables on left side and absolute part on the right side.
              Relation type is one of {<=, <, =}, so they can be used in the Presburger constructions right away.
    """

    # Craft an unified expr according to the used relation type that will have all variables and constants on one side
    if rel_type in ('<=', '<'):
        unified_expr = lhs_expr - rhs_expr
    elif rel_type in ('>=', '>'):
        unified_expr = rhs_expr - lhs_expr
    elif rel_type == '=':
        # It does not matter, equation can be rotated around = without problems
        unified_expr = rhs_expr - lhs_expr
    else:
        raise ValueError(f'Attempting to normalize a relation of unknown type: {rel_type}.')

    # Now the unified expr has form of <everything> <= 0 or <everything> < 0
    logger.debug(f'(unified expr): {unified_expr}{rel_type}0')

    # Deduce resulting relation type after rearangements - the expression might have to be rotated
    # in order to have the constant on the right side
    if rel_type in ('<', '>'):
        rel_op = '<'
    elif rel_type in ('<=', '>='):
        rel_op = '<='
    elif rel_type == '=':
        rel_op = '='

    relation_variable_names = []
    relation_variable_coeficients = []

    relation_abs = -unified_expr.absolute_part  # Move the absolute part the right side

    # Keep variables in the alphabetical order (required to as it is used to speed up projections)
    sorted_vars = sorted(unified_expr.variables.keys())
    for var_name in sorted_vars:
        var_coef = unified_expr.variables[var_name]
        relation_variable_names.append(var_name)
        relation_variable_coeficients.append(var_coef)

    modulo_terms, modulo_term_coeficients = [], []
    for modulo_term, modulo_term_coeficient in unified_expr.modulo_terms.items():
        modulo_terms.append(modulo_term)
        modulo_term_coeficients.append(modulo_term_coeficient)

    div_terms, div_term_coeficients = (
        tuple(map(list, zip(*unified_expr.div_terms.items()))) if unified_expr.div_terms else ([], [])
    )

    return Relation(
        variable_names=relation_variable_names,
        variable_coeficients=relation_variable_coeficients,
        modulo_terms=modulo_terms,
        modulo_term_coeficients=modulo_term_coeficients,
        div_terms=div_terms,
        div_term_coeficients=div_term_coeficients,
        absolute_part=relation_abs,
        operation=rel_op
    )


def extract_relation(ast, remove_variables_with_zero_ceofs: bool = False) -> Relation:
    """
    Construct a Relation from the given relation AST.

    The returned relation is normalized.
    """
    # (<= 2 ?X)  <=> [<=, 2, ?X]
    logger.debug(f'Extracting relation from: {ast}')
    assert(len(ast) == 3)
    op, lhs, rhs = ast
    logger.debug(f'Operation: \'{op}\', Left side: \'{lhs}\', Right side: \'{rhs}\'')

    lhs_expr = evaluate_expression_ast(lhs)
    rhs_expr = evaluate_expression_ast(rhs)

    normalized_expr = normalize_atomic_presburger_formula(op, lhs_expr, rhs_expr)

    # Filter out the variables with zero coeficients.
    if remove_variables_with_zero_ceofs:
        coefs = []
        var_names = []
        for var_name, coef in zip(normalized_expr.variable_names,
                                  normalized_expr.variable_coeficients):
            if coef != 0:
                coefs.append(coef)
                var_names.append(var_name)
            else:
                info = f'Removing the variable "{var_name}" from the atomic formula - the variable has a coeficient 0.'
                logger.info(info)
                logger.debug(f'Ast: {ast}')
        normalized_expr.variable_coeficients = coefs
        normalized_expr.variable_names = var_names

    if normalized_expr.operation == '<':
        conversion_message = 'Converting the sharp inequality into a non-sharp one (from={0},'.format(normalized_expr)
        normalized_expr.operation = '<='
        normalized_expr.absolute_part -= 1
        conversion_message += ' to={0})'.format(normalized_expr)
        logger.debug(conversion_message)

    logger.debug(f'Extraced relation: {normalized_expr}')
    return normalized_expr


def collect_ite_control_variables(ast) -> Set[str]:
    '''Returns the set of boolean variables found in the ITE expressions in the given AST.
    DEPRECATED'''

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


def evaluate_ite_for_var_assignment(ast, assignment: Dict[str, bool]):
    if type(ast) != list:
        # We have found a leaf, no processing is to be done
        return ast

    root = ast[0]
    if root == 'ite':
        ite_variable = ast[1]
        ite_val = assignment[ite_variable]

        if ite_val is True:
            true_subtree = ast[2]
            return evaluate_ite_for_var_assignment(true_subtree, assignment)
        else:
            false_subtree = ast[3]
            return evaluate_ite_for_var_assignment(false_subtree, assignment)
    elif root in ['+', '*', '<=', '>=', '>', '<', '=']:
        return [
            root,
            evaluate_ite_for_var_assignment(ast[1], assignment),
            evaluate_ite_for_var_assignment(ast[2], assignment),
        ]
    elif root in ['-']:
        # - needs separate handling, because it might be binary or unary
        if len(root) == 3:
            # Binary
            return [
                root,
                evaluate_ite_for_var_assignment(ast[1], assignment),
                evaluate_ite_for_var_assignment(ast[2], assignment),
            ]
        else:
            # Unary
            return [
                root,
                evaluate_ite_for_var_assignment(ast[1], assignment)
            ]


def gen_conjunction_expr_from_bool_vars(bool_assignment: Dict[str, bool]):
    expr = ['and']
    for name, value in bool_assignment.items():
        if value is True:
            expr.append(name)
        else:
            expr.append(['not', name])
    return expr


def expand_relation_on_ite(ast):
    '''Converts the AST containing ITE expressions into an equivalent disjunction.
    DEPRECATED
    '''
    # (>= sub sub)
    ite_ctl_variables = collect_ite_control_variables(ast)
    ctl_var_count = len(ite_ctl_variables)

    logger.info(
        'Found {0} ITE control variables when evaluating {1}'.format(
            ctl_var_count,
            ast
        )
    )

    if ctl_var_count == 0:
        return ast  # No expansions need to be performed

    relation_expr = ['or']
    for i in range(2**ctl_var_count):
        var_raw_values = number_to_bit_tuple(i, ctl_var_count)
        # Convert bit values to their Bool form
        var_values = [True if x == 1 else False for x in var_raw_values]
        var_assignment: Dict[str, bool] = dict(zip(ite_ctl_variables, var_values))

        ite_ctl_eval_expr = gen_conjunction_expr_from_bool_vars(var_assignment)
        ite_eval_tree = evaluate_ite_for_var_assignment(ast, var_assignment)

        ite_ctl_eval_expr.append(ite_eval_tree)
        relation_expr.append(ite_ctl_eval_expr)

        logger.debug(
            'ITE expanded for assigment: {0} into: {1}'.format(
                var_assignment,
                ite_ctl_eval_expr
            )
        )

    logger.info('AST was ITE expanded into {0}'.format(relation_expr))
    return relation_expr


def try_retrieve_variable_if_literal(ast) -> Optional[str]:
    '''Walks the given AST checking for the required structure of a literal -
    a variable that is prepended by some number of negations.

    Returns:
        - The literal variable (without negations) if the tree encodes a literal,
        - None otherwise.'''
    if type(ast) == list:
        if ast[0] == 'not':
            return try_retrieve_variable_if_literal(ast[1])
        else:
            # We have some node that is not a negation - that means we do not have a literal,
            # which is only bare variable with some negation prefix
            return None
    else:
        return ast
