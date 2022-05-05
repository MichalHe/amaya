from __future__ import annotations
from dataclasses import (
    dataclass,
    field,
)
from typing import (
    Callable,
    List,
    Dict,
    Tuple
)


@dataclass
class PresburgerExpr:
    absolute_part: int = 0
    variables: Dict[str, int] = field(default_factory=dict)
    modulo_terms: Dict[ModuloTerm, int] = field(default_factory=dict)
    div_terms: Dict[DivTerm, int] = field(default_factory=dict)

    def _invert_signs_immutable(self, coeficient_mapping: Dict[Any, int]) -> Dict[Any, int]:
        """Invert/negate signs in given coeficient_mapping."""
        new_coef_mapping: Dict[Any, int] = {term: -coef for term, coef in coeficient_mapping.items()}
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
        div_terms = self._invert_signs_immutable(self.div_terms)

        return PresburgerExpr(
            absolute_part=-self.absolute_part,
            variables=new_variables,
            modulo_terms=modulo_terms,
            div_terms=div_terms,
        )

    def __sub__(self, other_expr: PresburgerExpr) -> PresburgerExpr:
        abs_val = self.absolute_part - other_expr.absolute_part
        variables = self._subtract_coeficients_immutable(self.variables, other_expr.variables)
        modulo_terms = self._subtract_coeficients_immutable(self.modulo_terms, other_expr.modulo_terms)
        div_terms = self._subtract_coeficients_immutable(self.div_terms, other_expr.div_terms)

        return PresburgerExpr(
            absolute_part=abs_val,
            variables=variables,
            modulo_terms=modulo_terms,
            div_terms=div_terms,
        )

    def __add__(self, other_expr: PresburgerExpr) -> PresburgerExpr:
        abs_val = self.absolute_part + other_expr.absolute_part
        variables = self._add_coeficients_immutable(self.variables, other_expr.variables)
        modulo_terms = self._add_coeficients_immutable(self.modulo_terms, other_expr.modulo_terms)
        div_terms = self._add_coeficients_immutable(self.div_terms, other_expr.div_terms)

        return PresburgerExpr(
            absolute_part=abs_val,
            variables=variables,
            modulo_terms=modulo_terms,
            div_terms=div_terms,
        )

    def __mul__(self, other: PresburgerExpr):
        # In Presburger arithmetic, only multiplication by a constant is allowed

        # Determine which operand is constant
        if self.is_constexpr():
            const_expr: PresburgerExpr = self
            non_const_expr: PresburgerExpr = other
        elif other.is_constexpr():
            const_expr: PresburgerExpr = other
            non_const_expr: PresburgerExpr = self
        else:
            raise ValueError(
                f'Atempting to multiply variables by variables, which is forbidden in PA: {self} * {other}'
            )

        new_variables: Dict[str, int] = dict()
        multiplier = const_expr.absolute_part

        new_variables = {var_name: multiplier * var_coef for var_name, multiplier in non_const_expr.variables.items()}
        new_mod_terms = {
            var_name: multiplier * var_coef for var_name, var_coef in non_const_expr.modulo_terms.items()
        }
        new_div_terms = {
            var_name: multiplier * var_coef for var_name, var_coef in non_const_expr.div_terms.items()
        }

        return PresburgerExpr(
            absolute_part=const_expr.absolute_part * non_const_expr.absolute_part,
            variables=new_variables,
            modulo_terms=new_mod_terms,
            div_terms=new_div_terms,
        )

    @staticmethod
    def from_single_modulo_term(modulo_term: ModuloTerm) -> PresburgerExpr:
        """Wraps the given modulo term in PresburgerExpr."""
        return PresburgerExpr(absolute_part=0, variables={}, modulo_terms={modulo_term: 1})

    def is_constexpr(self) -> bool:
        """Checks whether the expression contains no variables."""
        return not (self.variables or self.modulo_terms or self.div_terms)


@dataclass(frozen=True)
class ModuloTerm:
    """Represents modulo term of form: `a.x + b.y ... + C ~=~ 0` (where ~=~ is the symbol for congruent)."""
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
    def from_expression(expr: PresburgerExpr, modulo: int) -> ModuloTerm:
        """
        Create ModuloTerm from PresburgerExpr - the result of evaluation subtrees in modulo term SMT form.

        :param PresburgerExpr expr: Result of evaluating the first AST in [mod AST AST]
        :param int modulo: Result of evaluating the second AST in [mod AST AST]
        """
        variables = tuple(sorted(expr.variables.keys()))
        coeficients = tuple(expr.variables[variable] for variable in variables)
        constant = expr.absolute_part

        return ModuloTerm(
            variables=variables,
            variable_coeficients=coeficients,
            constant=constant,
            modulo=modulo
        )

    def into_sorted(self) -> ModuloTerm:
        """Sorts the variables and corresponding coeficients alphabetically."""
        var_coef_pairs = zip(self.variables, self.variable_coeficients)
        sorted_var_coef_pairs = sorted(var_coef_pairs, key=lambda pair: pair[1])

        sorted_vars, sorted_coefs = zip(*sorted_var_coef_pairs)
        return ModuloTerm(variables=sorted_vars, variable_coeficients=sorted_coefs,
                          constant=self.constant, modulo=self.modulo)


@dataclass(frozen=True)
class DivTerm(object):
    """Represents single SMT-LIB div term."""
    variables: Tuple[str, ...]
    variable_coeficients: Tuple[str, ...]
    constant: int
    divisor: int

    def __str__(self) -> str:
        sign = '+' if self.constant >= 0 else '-'
        var_terms = (f'{var_coef}{var}' for var_coef, var in zip(self.variable_coeficients, self.variables))
        var_term_str = ' '.join(var_terms)
        return f'({var_term_str} {sign} {self.constant}) div {self.divisor})'

    @staticmethod
    def from_expression(expr: PresburgerExpr, divisor: int) -> DivTerm:
        variable_coef_pairs = sorted(expr.variables.items(), key=lambda pair: pair[0])
        variables, var_coefficients = zip(*variable_coef_pairs)
        return DivTerm(
            constant=expr.absolute_part,
            variables=variables,
            variable_coeficients=var_coefficients,
            divisor=divisor
        )

@dataclass
class ModuloReplacementInfo:
    term: ModuloTerm
    variable: str


@dataclass
class Relation(object):
    """
    Represents one atomic PrA constraint.
    
    Might contain modulo terms or div terms that are not evaluable directly and must be expressed in terms 
    of existential quantifier.
    """
    variable_names: List[str]
    variable_coeficients: List[int]

    modulo_terms: List[ModuloTerm]
    modulo_term_coeficients: List[int]

    div_terms: List[DivTerm]
    div_term_coeficients: List[int]

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
        """
        Returns true if all the variable cooeficients are zero and the relation is satisfied."""
        # TODO(codeboy): This needs fixing
        if self.modulo_terms:
            return False

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
        linear_terms = (
            '{0}{1}.{2}'.format(('+' if coef >= 0 else ''), coef, var_name) for coef, var_name in zip(
                self.variable_coeficients, self.variable_names
            )
        )

        modulo_terms = (
            '{0}{1}.{2}'.format(('+' if coef >= 0 else ''), coef, mod_term) for coef, mod_term in zip(
                self.modulo_terms, self.modulo_term_coeficients
            )
        )

        div_terms = (
            '{0}{1}.{2}'.format(('+' if coef >= 0 else ''), coef, div_term) for coef, div_term in zip(
                self.div_term_coeficients, self.div_terms
            )
        )
        
        relation_lhs_parts = (' '.join(linear_terms), ' '.join(modulo_terms), ' '.join(div_terms))
        return 'Relation({0} {1} {2})'.format(
            ' '.join(lhs_part for lhs_part in relation_lhs_parts if lhs_part),
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
        if self.operation != '=':
            return
        if not self.is_in_canoical_form():
            self.variable_coeficients = [-1 * coef for coef in self.variable_coeficients]
            self.modulo_term_coeficients = [-1 * coef for coef in self.modulo_term_coeficients]
            self.absolute_part *= -1

    def is_conguence_equality(self) -> bool:
        """Returns true if the relation is equation of form (a.x mod c0) = c1."""
        return len(self.modulo_terms) == 1 and self.operation == '=' and not self.variable_names

    def direct_construction_exists(self) -> bool:
        """Returns true if there exists a direct construction for the stored relation."""
        is_congruence_eq = self.is_conguence_equality()
        is_linear_relation = bool(self.variable_names) and not bool(self.modulo_terms)

        return is_congruence_eq or is_linear_relation

    def replace_modulo_terms_with_variables(self) -> Tuple[Relation, List[ModuloReplacementInfo]]:
        """Returns relation where every modulo term is replaced with a variable."""
        mod_vars = ['Mod_{0}_Var'.format(i) for i in range(len(self.modulo_terms))]

        modulo_replacement_info: List[ModuloReplacementInfo] = []

        relation_with_modulos_replaced = Relation(variable_names=self.variable_names[:],
                                                  variable_coeficients=self.variable_coeficients[:],
                                                  modulo_terms=[],
                                                  modulo_term_coeficients=[],
                                                  absolute_part=self.absolute_part,
                                                  operation=self.operation)

        for i, mod_term_data in enumerate(zip(mod_vars, self.modulo_term_coeficients, self.modulo_terms)):
            mod_var, term_coef, term = mod_term_data

            assert mod_var not in self.variable_names, 'Name collision when trying to replace modulo with a Mod_Var'

            relation_with_modulos_replaced.variable_names.append(mod_var)
            relation_with_modulos_replaced.variable_coeficients.append(term_coef)

            modulo_replacement_info.append(ModuloReplacementInfo(term=term, variable=mod_var))

        # Sort the relation variables alphabetically, so we have a canoical form in the future
        relation_with_modulos_replaced.sort_variables_alphabetically()

        return (relation_with_modulos_replaced, modulo_replacement_info)

    def sort_variables_alphabetically(self):
        """Sorts the variables and corresponding coeficients alphabetically."""
        var_coef_pairs = zip(self.variable_names, self.variable_coeficients)
        sorted_var_coef_pairs = sorted(var_coef_pairs, key=lambda pair: pair[1])

        sorted_vars, sorted_coefs = zip(*sorted_var_coef_pairs)
        self.variable_names = list(sorted_vars)
        self.variable_coeficients = list(sorted_coefs)
