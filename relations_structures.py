from __future__ import annotations
from dataclasses import dataclass
from typing import (
    Callable,
    List,
    Dict,
    Tuple
)


@dataclass(frozen=True)
class ModuloTerm:
    '''Represents modulo term of form: `a.x + b.y ... + C ~=~ 0` (where ~=~ is the symbol for congruent)'''
    variables: Tuple[str, ...]
    variable_coeficients: Tuple[int, ...]
    constant: int
    modulo: int

    def __str__(self) -> str:
        variable_with_coefs = zip(self.variable_coeficients, self.variables)
        _variables = ['{0}.{1}'.format(*var_with_coef) for var_with_coef in variable_with_coefs]

        return '({0} mod {1})'.format(' '.join(_variables), self.modulo)

    def __repr__(self) -> str:
        return str(self)

    @staticmethod
    def from_expression(expr, modulo) -> ModuloTerm:
        '''
        Create ModuloTerm from PresburgerExpr - the result of evaluation subtrees in modulo term SMT form.

        :param PresburgerExpr expr: Result of evaluating the first AST in [mod AST AST]
        :param int modulo: Result of evaluating the second AST in [mod AST AST]
        '''
        variables = tuple(sorted(expr.variables.keys()))
        coeficients = tuple(expr.variables[variable] for variable in variables)
        constant = expr.absolute_part

        return ModuloTerm(
            variables=variables,
            variable_coeficients=coeficients,
            constant=constant,
            modulo=modulo
        )


@dataclass
class Relation:
    variable_names: List[str]
    variable_coeficients: List[int]
    modulo_terms: List[ModuloTerm]
    modulo_term_coeficients: List[int]
    absolute_part: int
    operation: str

    def are_all_coeficients_zero(self) -> bool:
        '''Returns true if all relation variable coeficients are zero.'''
        are_all_coefs_zero = True
        for coef in self.variable_coeficients:
            if coef != 0:
                are_all_coefs_zero = False
                break
        return are_all_coefs_zero

    def is_always_satisfied(self) -> bool:
        '''Returns true if all the variable cooeficients are zero and
        the relation is satisfied.'''
        are_all_coefs_zero = self.are_all_coeficients_zero()

        if are_all_coefs_zero:
            # \\vec{coefs} \cdot \\vec{variables}   (left hand side) is always zero
            absolute_part_conditions: Dict[str, Callable[[int], bool]] = {
                '<': lambda absolute_part: absolute_part > 0,
                '<=': lambda absolute_part: absolute_part >= 0,
                '=': lambda absolute_part: absolute_part == 0,
                '>': lambda absolute_part: absolute_part < 0,
                '>=': lambda absolute_part: absolute_part <= 0,
            }

            absolute_part_condition = absolute_part_conditions[self.operation]
            return absolute_part_condition(self.absolute_part)
        else:
            return False

    def __str__(self):
        linear_component = []
        for coef, variable in zip(self.variable_coeficients, self.variable_names):
            sign = '+' if coef >= 0 else ''
            linear_component.append('{0}{1}.{2}'.format(sign, coef, variable))

        modulo_components = []
        for mod_term, coef in zip(self.modulo_terms, self.modulo_term_coeficients):
            sign = '+' if coef >= 0 else ''
            modulo_components.append('{0}{1}.{2}'.format(sign, coef, mod_term))

        return 'Relation({0} {1} {2} {3})'.format(
            ' '.join(linear_component),
            ' '.join(modulo_components),
            self.operation,
            self.absolute_part
        )

    def __repr__(self):
        return str(self)

    def get_used_variables(self) -> List[str]:
        '''Retrieve a collection of all the variables used in this relation.'''
        used_variables = set(self.variable_names)
        for modulo_term in self.modulo_terms:
            used_variables.update(modulo_term.variables)
        return sorted(used_variables)

    def is_in_canoical_form(self) -> bool:
        sign_count = len(self.variable_coeficients) + len(self.modulo_term_coeficients)

        positive_sign_count = 0
        for coef in self.variable_coeficients:
            if coef >= 0:
                positive_sign_count += 1
        for coef in self.modulo_term_coeficients:
            if coef >= 0:
                positive_sign_count += 1

        if positive_sign_count == sign_count / 2:
            return self.absolute_part >= 0

        return (positive_sign_count > sign_count / 2)

    def ensure_canoical_form_if_equation(self):
        """Ensures that the majority of variables/moduloterms in the relation have positive sign if the operation is =."""

        if not self.is_in_canoical_form():
            self.variable_coeficients = [-1 * coef for coef in self.variable_coeficients]
            self.modulo_term_coeficients = [-1 * coef for coef in self.modulo_term_coeficients]
            self.absolute_part *= -1
