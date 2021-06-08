from __future__ import annotations
from dataclasses import dataclass
from typing import (
    Callable,
    List,
    Dict
)


@dataclass
class Relation:
    variable_names: List[str]
    variable_coeficients: List[int]
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
