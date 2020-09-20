from __future__ import annotations
from log import logger
from dataclasses import dataclass
from typing import List, Dict, Sequence
from collections import defaultdict
from automatons import DFA, AlphabetLetter
from utils import vector_dot, number_to_bit_tuple
import math


INEQUALITY_COMPARISON_COMPLEMENTS = {
    '>': '<',
    '<': '>',
    '<=': '>=',
    '>=': '<=',
}


@dataclass
class Inequality:
    variable_names: List[str]
    variable_coeficients: List[int]
    absolute_part: int
    operation: str


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
    else:
        raise ValueError(f'Unsupported operation type: {operation}')


def normalize_inequation(op: str, lhs_expr: PresburgerExpr, rhs_expr: PresburgerExpr) -> Inequality:
    '''Takes inequation, and produces output in form of:
        <VARIABLES> <= <ABS>, when op is `<=` or `>=`
        <VARIABLES> < <ABS>, when op is `<` or `>`
    '''

    if op == '<=' or op == '<':
        unified_expr: PresburgerExpr = lhs_expr - rhs_expr
    elif op == '>=' or op == '>':
        unified_expr: PresburgerExpr = rhs_expr - lhs_expr
    # Now the unified expr has form of <everything> <= 0 or <everything> < 0
    logger.debug(f'{op}0 (unified expr): {unified_expr}')

    # Deduce resulting ineqation relation op
    if op == '<' or op == '>':
        ineq_op = '<'
    else:
        ineq_op = '<='

    ineq_variable_names = []
    ineq_variable_coeficients = []

    ineq_abs = -unified_expr.absolute_part  # move it to the right side
    for var_name, var_coef in unified_expr.variables.items():
        ineq_variable_names.append(var_name)
        ineq_variable_coeficients.append(var_coef)

        # @Debug: See whether the system can process variables with coeficients
        # bigger than 1
        if abs(var_coef) > 1:
            logger.info(f'Found variable coeficient which is bigger than expected- {var_name}:{var_coef}')

    return Inequality(
        ineq_variable_names,
        ineq_variable_coeficients,
        ineq_abs,
        ineq_op
    )


def extract_inquality(ast) -> Inequality:
    # (<= 2 ?X)  <=> [<=, 2, ?X]
    logger.debug(f'Extracting inequality from: {ast}')
    assert(len(ast) == 3)
    op, lhs, rhs = ast
    logger.debug(f'Operation: \'{op}\', Left side: \'{lhs}\', Right side: \'{rhs}\'')

    lhs_expr = evaluate_expression(lhs)
    rhs_expr = evaluate_expression(rhs)

    return normalize_inequation(op, lhs_expr, rhs_expr)


def get_automaton_alphabet_from_inequality(ineq: Inequality) -> Sequence[AlphabetLetter]:
    '''Generator'''
    letter_size = len(ineq.variable_names)
    for i in range(2**letter_size):
        yield number_to_bit_tuple(i)


def build_dfa_from_inequality(ineq: Inequality) -> DFA:
    '''Builds DFA with Lang same as solutions to the inequation over N'''
    logger.debug(f'Building DFA (over N) to inequation: {ineq}')

    # Build DFA, assume len(bound_variables) == 1
    initial_state = ineq.absolute_part
    final_states = set()
    states = set()
    transitions = dict()

    work_queue = [initial_state]

    alphabet = list(get_automaton_alphabet_from_inequality(ineq))
    logger.info(f'Generated alphabet for automaton: {alphabet}')

    while work_queue:
        currently_processed_state = work_queue.pop(0)
        states.add(currently_processed_state)
        transitions[currently_processed_state] = {}

        # Check whether current state satisfies property that it accepts an
        # empty word
        if currently_processed_state >= 0:
            final_states.add(currently_processed_state)

        for alphabet_symbol in alphabet:
            # @Optimize: Precompute dot before graph traversal
            dot = vector_dot(alphabet_symbol, ineq.variable_coeficients)
            next_state = math.floor(0.5 * (currently_processed_state - dot))

            # Was the alphabet symbol already seen?
            if alphabet_symbol not in transitions[currently_processed_state]:
                transitions[currently_processed_state][alphabet_symbol] = set()

            # Add newly discovered transition
            transitions[currently_processed_state][alphabet_symbol].add(next_state)

            if next_state not in states:
                if next_state not in work_queue:  # @Optimize: Use hashtable-like object to quickly check for `in`
                    work_queue.append(next_state)

    dfa = DFA(
        initial_state=initial_state,
        states=states,
        final_states=final_states,
        transitions=transitions,
        alphabet=alphabet
    )

    logger.debug(f'Extracted dfa: {dfa}')

    return dfa
