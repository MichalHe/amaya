from __future__ import annotations
from log import logger
from dataclasses import dataclass
from typing import (
    List,
    Dict,
    Tuple,
    Union
)
from utils import vector_dot
from automatons import (
    DFA,
    NFA,
    LSBF_Alphabet,
    AutomatonType
)
from inequations_data import (
    Inequality
)

import math


INEQUALITY_COMPARISON_COMPLEMENTS = {
    '>': '<',
    '<': '>',
    '<=': '>=',
    '>=': '<=',
}


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
        unified_expr = lhs_expr - rhs_expr
    elif op == '>=' or op == '>':
        unified_expr = rhs_expr - lhs_expr
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


DFA_AlphabetSymbolType = Tuple[int, ...]
DFA_AutomatonStateType = int
NFA_AutomatonStateType = Union[int, str]
NFA_AlphabetSymbolType = Tuple[int, ...]


def build_dfa_from_inequality(ineq: Inequality) -> DFA:
    '''Builds DFA with Lang same as solutions to the inequation over N'''
    logger.debug(f'Building DFA (over N) to inequation: {ineq}')

    alphabet = LSBF_Alphabet.from_inequation(ineq)
    dfa: DFA[DFA_AutomatonStateType] = DFA(
        alphabet=alphabet,
        automaton_type=AutomatonType.DFA
    )
    dfa.add_initial_state(ineq.absolute_part)

    work_queue: List[DFA_AutomatonStateType] = [ineq.absolute_part]

    logger.info(f'Generated alphabet for automaton: {alphabet}')

    while work_queue:
        currently_processed_state = work_queue.pop(0)
        print(dfa.states)
        dfa.add_state(currently_processed_state)

        # Check whether current state satisfies property that it accepts an
        # empty word
        if currently_processed_state >= 0:
            dfa.add_final_state(currently_processed_state)

        for alphabet_symbol in alphabet.symbols:
            # @Optimize: Precompute dot before graph traversal
            dot = vector_dot(alphabet_symbol, ineq.variable_coeficients)
            next_state = math.floor(0.5 * (currently_processed_state - dot))

            # Add newly discovered transition
            dfa.update_transition_fn(currently_processed_state, alphabet_symbol, next_state)

            if not dfa.has_state_with_value(next_state):
                if next_state not in work_queue:
                    work_queue.append(next_state)

    logger.debug(f'Extracted dfa: {dfa}')

    return dfa


def build_nfa_from_inequality(ineq: Inequality) -> NFA[NFA_AutomatonStateType]:
    # Initialize nfa structures
    alphabet = LSBF_Alphabet.from_inequation(ineq)
    nfa: NFA[NFA_AutomatonStateType] = NFA(
        alphabet=alphabet,
        automaton_type=AutomatonType.NFA,
    )
    nfa.add_initial_state(ineq.absolute_part)

    work_queue: List[int] = [ineq.absolute_part]

    import pdb
    pdb.set_trace()
    while work_queue:
        current_state = work_queue.pop(0)
        nfa.add_state(current_state)

        for alphabet_symbol in alphabet.symbols:
            dot = vector_dot(alphabet_symbol, ineq.variable_coeficients)
            destination_state = math.floor(0.5 * (current_state - dot))

            if not nfa.has_state_with_value(destination_state):
                work_queue.append(destination_state)

            nfa.update_transition_fn(current_state, alphabet_symbol, destination_state)

            # Check whether state is final
            if current_state + dot >= 0:
                final_state = 'FINAL'
                nfa.add_state(final_state)
                nfa.add_final_state(final_state)
                nfa.update_transition_fn(current_state, alphabet_symbol, final_state)

    return nfa
