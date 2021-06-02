from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Set, Optional
from log import logger
from relations_structures import Relation
from utils import number_to_bit_tuple


@dataclass
class PresburgerExpr:
    absolute_part: int
    variables: Dict[str, int]

    def __neg__(self) -> PresburgerExpr:
        new_variables = {}
        for variable_name in self.variables:
            new_variables[variable_name] = -self.variables[variable_name]

        return PresburgerExpr(-self.absolute_part, new_variables)

    def __sub__(self, other_expr: PresburgerExpr) -> PresburgerExpr:
        abs_val = self.absolute_part - other_expr.absolute_part
        variables = self.variables

        for var_name in other_expr.variables:
            if var_name in variables:
                variables[var_name] -= other_expr.variables[var_name]
            else:
                variables[var_name] = -other_expr.variables[var_name]

        return PresburgerExpr(abs_val, variables)

    def __add__(self, other: PresburgerExpr) -> PresburgerExpr:
        abs_val = self.absolute_part + other.absolute_part
        variables = self.variables

        for var_name in other.variables:
            if var_name in variables:
                variables[var_name] += other.variables[var_name]
            else:
                variables[var_name] = other.variables[var_name]
        return PresburgerExpr(abs_val, variables)

    def __mul__(self, other: PresburgerExpr):
        # In PA one must be constant
        const_expr: PresburgerExpr = self
        non_const_expr: PresburgerExpr = other

        if self.variables:
            if other.variables:
                raise ValueError(f'Atempting to multiply variables by variables, which is forbidden in PA: {self} * {other}')
            else:
                const_expr = other
                non_const_expr = self

        new_variables: Dict[str, int] = dict()
        for var_name, var_value in non_const_expr.variables.items():
            new_variables[var_name] = const_expr.absolute_part * var_value
        return PresburgerExpr(
            absolute_part=const_expr.absolute_part * non_const_expr.absolute_part,
            variables=new_variables
        )


def evaluate_expression(expr) -> PresburgerExpr:
    if not type(expr) == list:
        # It is an atom, which is either int, or variable
        try:
            atom_int_value = int(expr)
            return PresburgerExpr(
                absolute_part=atom_int_value,
                variables=dict()
            )
        except ValueError:
            variable_name = expr
            return PresburgerExpr(
                absolute_part=0,
                variables={variable_name: 1}
            )

    operation = expr[0]
    if operation == '-':
        if len(expr) == 2:
            return -evaluate_expression(expr[1])  # Negate expr
        else:
            operand1 = evaluate_expression(expr[1])
            operand2 = evaluate_expression(expr[2])
            return operand1 - operand2
    elif operation == '+':
        operand1 = evaluate_expression(expr[1])
        operand2 = evaluate_expression(expr[2])
        return operand1 + operand2
    elif operation == '*':
        operand1 = evaluate_expression(expr[1])
        operand2 = evaluate_expression(expr[2])

        # (* (+ 10 x) (- 20 y)) --> forbidden in presburger arithmetics
        try:
            return operand1 * operand2
        except ValueError:
            raise ValueError(f'Error while evaluating {expr} -- attempting to multiply variables by variables, which is forbidden in PA.')

    else:
        raise ValueError(f'Unsupported operation type: {operation} in expr: {expr}')


def normalize_atomic_presburger_formula(op: str, lhs_expr: PresburgerExpr, rhs_expr: PresburgerExpr) -> Relation:
    '''Takes an automic formula of form:
            <variables_and_constants2> <op> <variables_and_constants2>,
        and produces output in form of:
            <VARIABLES> <= <ABS>, when op is `<=` or `>=`
            <VARIABLES> < <ABS>, when op is `<` or `>`
    '''

    if op == '<=' or op == '<':
        unified_expr = lhs_expr - rhs_expr
    elif op == '>=' or op == '>':
        unified_expr = rhs_expr - lhs_expr
    elif op == '=':
        # It does not matter, equation can be rotated around = without problems
        unified_expr = rhs_expr - lhs_expr

    # Now the unified expr has form of <everything> <= 0 or <everything> < 0
    logger.debug(f'(unified expr): {unified_expr}{op}0')

    # Deduce resulting ineqation relation op after rearangement
    if op in ['<', '>']:
        rel_op = '<'
    elif op in ['<=', '>=']:
        rel_op = '<='
    elif op == '=':
        rel_op = '='

    relation_variable_names = []
    relation_variable_coeficients = []

    relation_abs = -unified_expr.absolute_part  # move it to the right side

    # Keep variables in alphabetical order - required for fast projections
    sorted_vars = sorted(unified_expr.variables.keys())
    for var_name in sorted_vars:
        var_coef = unified_expr.variables[var_name]
        relation_variable_names.append(var_name)
        relation_variable_coeficients.append(var_coef)

    return Relation(
        relation_variable_names,
        relation_variable_coeficients,
        relation_abs,
        rel_op
    )


def extract_relation(ast, remove_variables_with_zero_ceofs: bool = False) -> Relation:
    # (<= 2 ?X)  <=> [<=, 2, ?X]
    logger.debug(f'Extracting inequality from: {ast}')
    assert(len(ast) == 3)
    op, lhs, rhs = ast
    logger.debug(f'Operation: \'{op}\', Left side: \'{lhs}\', Right side: \'{rhs}\'')

    lhs_expr = evaluate_expression(lhs)
    rhs_expr = evaluate_expression(rhs)

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
                logger.info(f'Removing the variable variable_name="{var_name}" from atomic fromula - the variable has a coeficient 0.')
                logger.debug(f'Ast: {ast}')
        normalized_expr.variable_coeficients = coefs
        normalized_expr.variable_names = var_names

    return normalized_expr


def get_ite_info(ast) -> Set[str]:
    '''Returns the set of boolean variables found in the ITE expressions in the given AST.'''
    if type(ast) != list:
        return set()

    root = ast[0]
    if root == 'ite':
        assert len(ast) == 4
        ite_variable = ast[1]
        ite_true_tree = ast[2]
        ite_false_tree = ast[3]

        ite_true_info = get_ite_info(ite_true_tree)
        ite_false_info = get_ite_info(ite_false_tree)

        return set([ite_variable]).union(ite_true_info).union(ite_false_info)
    elif root in ['+',  '*', '<=', '>=', '>', '<', '=']:
        return get_ite_info(ast[1]).union(get_ite_info(ast[2]))
    elif root in ['-']:
        if len(root) == 3:
            return get_ite_info(ast[1]).union(get_ite_info(ast[2]))
        else:
            return get_ite_info(ast[1])


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
    '''Converts the AST containing ITE expressions into an equivalent disjunction.'''
    # (>= sub sub)
    ite_ctl_variables = get_ite_info(ast)
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
        return ast
