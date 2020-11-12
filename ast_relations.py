from __future__ import annotations
from dataclasses import dataclass
from typing import Dict
from log import logger
from relations_structures import Relation


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


def normalize_inequation(op: str, lhs_expr: PresburgerExpr, rhs_expr: PresburgerExpr) -> Relation:
    '''Takes inequation, and produces output in form of:
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
    for var_name, var_coef in unified_expr.variables.items():
        relation_variable_names.append(var_name)
        relation_variable_coeficients.append(var_coef)

    return Relation(
        relation_variable_names,
        relation_variable_coeficients,
        relation_abs,
        rel_op
    )


def extract_relation(ast) -> Relation:
    # (<= 2 ?X)  <=> [<=, 2, ?X]
    logger.debug(f'Extracting inequality from: {ast}')
    assert(len(ast) == 3)
    op, lhs, rhs = ast
    logger.debug(f'Operation: \'{op}\', Left side: \'{lhs}\', Right side: \'{rhs}\'')

    lhs_expr = evaluate_expression(lhs)
    rhs_expr = evaluate_expression(rhs)

    return normalize_inequation(op, lhs_expr, rhs_expr)
