from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Set, Optional, Tuple, Any
from log import logger
from relations_structures import Relation
from utils import number_to_bit_tuple


ModuloTerm = Tuple[str, int]  # (x mod 10) --> Variable name: x, modulo: 10


@dataclass
class PresburgerExpr:
    absolute_part: int
    variables: Dict[str, int]
    modulo_terms: Dict[ModuloTerm, int]

    def _invert_signs_immutable(self, coeficient_mapping: Dict[Any, int]) -> Dict[Any, int]:
        """Invert/negate signs in given coeficient_mapping."""
        new_coef_mapping: Dict[Any, int] = {}
        for item in coeficient_mapping:
            new_coef_mapping[item] = -coeficient_mapping[item]
        return new_coef_mapping

    def _subtract_coeficients_immutable(self,
                                        coef_mapping_left: Dict[Any, int],
                                        coef_mapping_right: Dict[Any, int]) -> Dict[Any, int]:
        subtraction_result = dict(coef_mapping_left)
        for item in coef_mapping_right:
            if item in subtraction_result:
                subtraction_result[item] -= coef_mapping_right[item]
            else:
                subtraction_result[item] = -coef_mapping_right[item]
        return subtraction_result

    def _add_coeficients_immutable(self,
                                   coef_mapping_left: Dict[Any, int],
                                   coef_mapping_right: Dict[Any, int]) -> Dict[Any, int]:
        subtraction_result = dict(coef_mapping_left)
        for item in coef_mapping_right:
            if item in subtraction_result:
                subtraction_result[item] += coef_mapping_right[item]
            else:
                subtraction_result[item] = coef_mapping_right[item]
        return subtraction_result

    def __neg__(self) -> PresburgerExpr:
        new_variables = self._invert_signs_immutable(self.variables)
        modulo_terms = self._invert_signs_immutable(self.modulo_terms)

        return PresburgerExpr(
            absolute_part=-self.absolute_part,
            variables=new_variables,
            modulo_terms=modulo_terms
        )

    def __sub__(self, other_expr: PresburgerExpr) -> PresburgerExpr:
        abs_val = self.absolute_part - other_expr.absolute_part
        variables = self._subtract_coeficients_immutable(self.variables, other_expr.variables)
        modulo_terms = self._subtract_coeficients_immutable(self.modulo_terms, other_expr.modulo_terms)

        return PresburgerExpr(
            absolute_part=abs_val,
            variables=variables,
            modulo_terms=modulo_terms
        )

    def __add__(self, other_expr: PresburgerExpr) -> PresburgerExpr:
        abs_val = self.absolute_part + other_expr.absolute_part
        variables = self._add_coeficients_immutable(self.variables, other_expr.variables)
        modulo_terms = self._add_coeficients_immutable(self.modulo_terms, other_expr.modulo_terms)

        return PresburgerExpr(
            absolute_part=abs_val,
            variables=variables,
            modulo_terms=modulo_terms
        )

    def __mul__(self, other: PresburgerExpr):
        # In PA one must be constant
        const_expr: PresburgerExpr = self
        non_const_expr: PresburgerExpr = other

        if self.variables:
            if other.variables or other.modulo_terms:
                raise ValueError(f'Atempting to multiply variables by variables, which is forbidden in PA: {self} * {other}')
            else:
                const_expr = other
                non_const_expr = self

        new_variables: Dict[str, int] = dict()
        for var_name, var_value in non_const_expr.variables.items():
            new_variables[var_name] = const_expr.absolute_part * var_value

        new_mod_terms: Dict[ModuloTerm, int] = dict()
        for mod_term, coef in non_const_expr.modulo_terms.items():
            new_mod_terms[mod_term] = const_expr.absolute_part * coef

        return PresburgerExpr(
            absolute_part=const_expr.absolute_part * non_const_expr.absolute_part,
            variables=new_variables,
            modulo_terms=new_mod_terms
        )

    @staticmethod
    def from_modulo_term(modulo_term: ModuloTerm) -> PresburgerExpr:
        """Wraps the given modulo term into PresburgerExpr."""
        return PresburgerExpr(absolute_part=0, variables={}, modulo_terms={modulo_term: 1})

    def is_constexpr(self) -> bool:
        """Checks whether the expression contains no variables."""
        return not (self.variables or self.modulo_terms)


def evaluate_expression(expr) -> PresburgerExpr:
    """
    Evaluates the given expression AST and returns the (normalized) result.

    Example: [+ [* 10 x] y] --> 10x + y
    """
    if not type(expr) == list:
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
            return -evaluate_expression(expr[1])  # Negate expr
        else:
            operand1 = evaluate_expression(expr[1])
            operand2 = evaluate_expression(expr[2])
            return operand1 - operand2
    elif operation == '+':
        acc = evaluate_expression(expr[1])
        for operand in expr[2:]:
            acc += evaluate_expression(operand)
        return acc
    elif operation == '*':
        operand1 = evaluate_expression(expr[1])
        operand2 = evaluate_expression(expr[2])

        # (* (+ 10 x) (- 20 y)) --> forbidden in presburger arithmetics
        try:
            return operand1 * operand2
        except ValueError:
            raise ValueError(f'Error while evaluating {expr} -- attempting to multiply variables by variables, which is forbidden in PA.')
    elif operation == 'mod':
        # We only expect modulo operators in the form of: [mod x constant]
        variable_name = expr[1]
        modulo = evaluate_expression(expr[2])  # The modulo might be entire AST

        assert modulo.is_constexpr(), 'The modulo term does not have a constant as a right operand: {0}'.format(
            modulo
        )

        return PresburgerExpr.from_modulo_term((variable_name, modulo.absolute_part))

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
