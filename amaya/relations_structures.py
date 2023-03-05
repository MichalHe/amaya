from __future__ import annotations
from dataclasses import (
    dataclass,
    field,
)
import functools
from typing import (
    Callable,
    List,
    Dict,
    Generic,
    Tuple,
    TypeVar,
    Union,
)


@dataclass
class PresburgerExpr:
    absolute_part: int = 0
    variables: Dict[str, int] = field(default_factory=dict)
    modulo_terms: Dict[ModuloTerm, int] = field(default_factory=dict)
    div_terms: Dict[DivTerm, int] = field(default_factory=dict)

    def _invert_signs_immutable(self, coefficient_mapping: Dict[Any, int]) -> Dict[Any, int]:
        """Invert/negate signs in given coefficient_mapping."""
        new_coef_mapping: Dict[Any, int] = {term: -coef for term, coef in coefficient_mapping.items()}
        return new_coef_mapping

    def _subtract_coefficients_immutable(self,
                                        coef_mapping_left: Dict[Any, int],
                                        coef_mapping_right: Dict[Any, int]) -> Dict[Any, int]:
        subtraction_result = dict(coef_mapping_left)
        for item in coef_mapping_right:
            if item in subtraction_result:
                subtraction_result[item] -= coef_mapping_right[item]
            else:
                subtraction_result[item] = -coef_mapping_right[item]
        return subtraction_result

    def _add_coefficients_immutable(self,
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
        variables = self._subtract_coefficients_immutable(self.variables, other_expr.variables)
        modulo_terms = self._subtract_coefficients_immutable(self.modulo_terms, other_expr.modulo_terms)
        div_terms = self._subtract_coefficients_immutable(self.div_terms, other_expr.div_terms)

        return PresburgerExpr(
            absolute_part=abs_val,
            variables=variables,
            modulo_terms=modulo_terms,
            div_terms=div_terms,
        )

    def __add__(self, other_expr: PresburgerExpr) -> PresburgerExpr:
        abs_val = self.absolute_part + other_expr.absolute_part
        variables = self._add_coefficients_immutable(self.variables, other_expr.variables)
        modulo_terms = self._add_coefficients_immutable(self.modulo_terms, other_expr.modulo_terms)
        div_terms = self._add_coefficients_immutable(self.div_terms, other_expr.div_terms)

        return PresburgerExpr(
            absolute_part=abs_val,
            variables=variables,
            modulo_terms=modulo_terms,
            div_terms=div_terms,
        )

    def __mul__(self, other: PresburgerExpr):
        # Only multiplication by a constant is allowed - determine which operand is constant
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

        new_variables = {var_name: multiplier * var_coef for var_name, var_coef in non_const_expr.variables.items()}
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
    variable_coefficients: Tuple[int, ...]
    constant: int
    modulo: int

    def __str__(self) -> str:
        variable_with_coefs = zip(self.variable_coefficients, self.variables)
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
        coefficients = tuple(expr.variables[variable] for variable in variables)
        constant = expr.absolute_part

        return ModuloTerm(
            variables=variables,
            variable_coefficients=coefficients,
            constant=constant,
            modulo=modulo
        )

    def into_sorted(self) -> ModuloTerm:
        """Sorts the variables and corresponding coefficients alphabetically."""
        var_coef_pairs = zip(self.variables, self.variable_coefficients)
        sorted_var_coef_pairs = sorted(var_coef_pairs, key=lambda pair: pair[0])

        sorted_vars, sorted_coefs = zip(*sorted_var_coef_pairs)
        return ModuloTerm(variables=sorted_vars, variable_coefficients=sorted_coefs,
                          constant=self.constant, modulo=self.modulo)


@dataclass(frozen=True)
class DivTerm(object):
    """Represents single SMT-LIB div term."""
    variables: Tuple[str, ...]
    variable_coefficients: Tuple[str, ...]
    constant: int
    divisor: int

    def __str__(self) -> str:
        sign = '+' if self.constant >= 0 else '-'
        var_terms = (f'{var_coef}{var}' for var_coef, var in zip(self.variable_coefficients, self.variables))
        var_term_str = ' '.join(var_terms)
        return f'({var_term_str} {sign} {self.constant}) div {self.divisor})'

    @staticmethod
    def from_expression(expr: PresburgerExpr, divisor: int) -> DivTerm:
        variable_coef_pairs = sorted(expr.variables.items(), key=lambda pair: pair[0])
        variables, var_coefficients = zip(*variable_coef_pairs) if variable_coef_pairs else ((), ())
        return DivTerm(
            constant=expr.absolute_part,
            variables=variables,
            variable_coefficients=var_coefficients,
            divisor=divisor
        )


RewritableTerm = Union[ModuloTerm, DivTerm]


@dataclass
class TermRewrites:
    count: int = 0
    """The number of rewritten terms so far."""


@dataclass
class Relation(object):
    """
    Represents one atomic PrA constraint.

    Might contain modulo terms or div terms that are not evaluable directly and must be expressed in terms
    of existential quantifier.
    """
    variable_names: List[str]
    variable_coefficients: List[int]

    modulo_terms: List[ModuloTerm]
    modulo_term_coefficients: List[int]

    div_terms: List[DivTerm]
    div_term_coefficients: List[int]

    absolute_part: int
    predicate_symbol: str

    def are_all_coefficients_zero(self) -> bool:
        '''Returns true if all relation variable coefficients are zero.'''
        are_all_coefs_zero = True
        for coef in self.variable_coefficients:
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

        are_all_coefs_zero = self.are_all_coefficients_zero()

        if are_all_coefs_zero:
            # \\vec{coefs} \cdot \\vec{variables}   (left hand side) is always zero
            absolute_part_conditions: Dict[str, Callable[[int], bool]] = {
                '<': lambda absolute_part: absolute_part > 0,
                '<=': lambda absolute_part: absolute_part >= 0,
                '=': lambda absolute_part: absolute_part == 0,
                '>': lambda absolute_part: absolute_part < 0,
                '>=': lambda absolute_part: absolute_part <= 0,
            }

            absolute_part_condition = absolute_part_conditions[self.predicate_symbol]
            return absolute_part_condition(self.absolute_part)
        else:
            return False

    def _format_term_type_into_string(self,
                                      term_coefs: Iterable[int],
                                      terms: Union[List[str], List[DivTerm], List[ModuloTerm]],
                                      use_latex_notation: bool = False) -> Generator[str, None, None]:
        if use_latex_notation:
            var_coef_iterator = iter(zip(term_coefs, terms))
            first_var_coef_name_pair = next(var_coef_iterator, None)
            if not first_var_coef_name_pair:
                return
            first_var_coef, first_var_name = first_var_coef_name_pair
            yield '{0}{1}'.format(first_var_coef if first_var_coef != 1 else '', first_var_name)
            for coef, var_name in var_coef_iterator:
                yield '{sign} {coef_abs}{var_name}'.format(
                    sign='+' if coef >= 0 else '-', coef_abs=abs(coef) if abs(coef) != 1 else '', var_name=var_name
                )
        else:
            for coef, var_name in zip(term_coefs, terms):
                yield '{0}{1}.{2}'.format(('+' if coef >= 0 else ''), coef, var_name)

    def into_string(self, use_latex_notation: bool = False) -> str:
        linear_terms = self._format_term_type_into_string(self.variable_coefficients, self.variable_names,
                                                          use_latex_notation=use_latex_notation)

        modulo_terms = self._format_term_type_into_string(self.modulo_term_coefficients, self.modulo_terms,
                                                          use_latex_notation=use_latex_notation)

        div_terms = self._format_term_type_into_string(self.div_term_coefficients, self.div_terms,
                                                          use_latex_notation=use_latex_notation)

        relation_lhs_parts = (' '.join(linear_terms), ' '.join(modulo_terms), ' '.join(div_terms))

        predicate_symbol = self.predicate_symbol
        if use_latex_notation:
            predicate_symbol = {'<=': '\\le', '>=': '\\ge'}.get(predicate_symbol, predicate_symbol)

        return '{0} {1} {2}'.format(
            ' '.join(lhs_part for lhs_part in relation_lhs_parts if lhs_part),
            predicate_symbol,
            self.absolute_part
        )

    def __str__(self):
        return self.into_string(use_latex_notation=False)

    def __repr__(self):
        return 'Relation(' + self.into_string(use_latex_notation=False) + ')'

    def get_used_variables(self) -> Set[str]:
        '''Retrieve a collection of all the variables used in this relation.'''
        used_variables = set(self.variable_names)
        for modulo_term in self.modulo_terms:
            used_variables.update(modulo_term.variables)
        return sorted(used_variables)

    def is_in_canoical_form(self) -> bool:
        sign_count = len(self.variable_coefficients) + len(self.modulo_term_coefficients)

        positive_sign_count = 0
        for coef in self.variable_coefficients:
            if coef >= 0:
                positive_sign_count += 1
        for coef in self.modulo_term_coefficients:
            if coef >= 0:
                positive_sign_count += 1

        positive_sign_count += sum(coef >= 0 for coef in self.div_term_coefficients)

        if positive_sign_count == sign_count / 2:
            return self.absolute_part >= 0

        return (positive_sign_count > sign_count / 2)

    def ensure_canoical_form_if_equation(self):
        """Ensures that the majority of variables/moduloterms in the relation have the positive sign if the predicate_symbol is =."""
        if self.predicate_symbol != '=':
            return
        if not self.is_in_canoical_form():
            self.variable_coefficients = [-1 * coef for coef in self.variable_coefficients]
            self.modulo_term_coefficients = [-1 * coef for coef in self.modulo_term_coefficients]
            self.div_term_coefficients = [-1 * coef for coef in self.div_term_coefficients]
            self.absolute_part *= -1

    def is_congruence_equality(self) -> bool:
        """Returns true if the relation is equation of form (a.x mod c0) = c1."""
        return len(self.modulo_terms) == 1 and self.predicate_symbol == '=' and not self.variable_names and not self.div_terms

    def direct_construction_exists(self) -> bool:
        """Returns true if there exists a direct construction for the stored relation."""
        is_congruence_eq = self.is_congruence_equality()
        is_linear_relation = bool(self.variable_names) and not bool(self.modulo_terms) and not bool(self.div_terms)

        return is_congruence_eq or is_linear_relation

    def _add_vars_replacing_terms(self,
                                  terms: Union[Iterable[ModuloTerm], Iterable[DivTerm]],
                                  coefs: Iterable[int],
                                  vars_to_reference: Optional[Set[str]],
                                  var_prefix: str,
                                  rewrite_info: TermRewrites,
                                  vars_rewriting_terms: Dict[RewritableTerm, str]) -> int:
        introduced_names_cnt = 0
        for i, term_pair in enumerate(zip(coefs, terms)):
            coef, term = term_pair

            if vars_to_reference and all(var not in vars_to_reference for var in vars_to_reference):
                continue

            if term not in vars_rewriting_terms:
                term_id = rewrite_info.count
                rewrite_info.count += 1

                assigned_var = f'{var_prefix}#{term_id}'
                vars_rewriting_terms[term] = assigned_var
            else:
                assigned_var = vars_rewriting_terms[term]

            assert assigned_var not in self.variable_names, ('Name collision when trying to replace div term '
                                                             'with an existentially bound variable: {div_var}')

            self.variable_names.append(assigned_var)
            self.variable_coefficients.append(coef)
        return introduced_names_cnt

    def replace_chosen_nonlinear_terms_with_variables(self, vars_to_reference: Set[str], vars_rewriting_terms: Optional[Dict[RewritableTerm, str]], rewrite_info: TermRewrites) -> int:
        """Replace modulo and div terms that reference a variable from `vars_to_reference` with variables in a fashion consistent with `vars_rewriting_terms`."""
        introduced_names_cnt = 0
        introduced_names_cnt += self._add_vars_replacing_terms(self.div_terms, self.div_term_coefficients, vars_to_reference,
                                                               'DivTerm', rewrite_info, vars_rewriting_terms)

        introduced_names_cnt += self._add_vars_replacing_terms(self.modulo_terms, self.modulo_term_coefficients, vars_to_reference,
                                                               'ModTerm', rewrite_info, vars_rewriting_terms)

        self.modulo_term_coefficients = []
        self.modulo_terms = []
        self.div_term_coefficients = []
        self.div_terms = []

        self.sort_variables_alphabetically()
        return introduced_names_cnt

    def sort_variables_alphabetically(self):
        """Sorts the variables and corresponding coefficients alphabetically."""
        var_coef_pairs = zip(self.variable_names, self.variable_coefficients)
        sorted_var_coef_pairs = sorted(var_coef_pairs, key=lambda pair: pair[0])

        sorted_vars, sorted_coefs = zip(*sorted_var_coef_pairs) if sorted_var_coef_pairs else (tuple(), tuple())
        self.variable_names = list(sorted_vars)
        self.variable_coefficients = list(sorted_coefs)

    def calc_approximate_automaton_size(self) -> int:
        """
        Calculate the approximate size for the automaton encoding this constraint.

        Requires the represented relation to be a directly evaluable atomic constraint (linear relation without mod/div
        terms or congruence).
        """
        if self.variable_names:
            return sum(map(abs, self.variable_coefficients))
        if self.modulo_terms:
            return abs(self.modulo_terms[0].modulo)
        return 0

    def rename_frozen_terms(self,
                            terms: List[T],
                            renaming: Dict[str, VariableRenamingInfo],
                            term_constr: Callable[[Tuple[str], T], T]) -> Optional[Tuple[bool, List[T]]]:
        """
        Rename the variables in the given terms according to supplied renaming.

        Returns a tuple containing:
            - a boolean indicating whether was any variable renamed
            - a list of the renamed terms
        """
        renamed_terms = []
        was_any_variable_renamed = False
        for term in terms:
            renamed_variables = tuple(renaming[var].new_name if var in renaming else var for var in term.variables)
            if renamed_variables != term.variables:
                was_any_variable_renamed = True
                renamed_term = term_constr(renamed_variables, term)
                renamed_terms.append(renamed_term)
            else:
                renamed_terms.append(term)
        return was_any_variable_renamed, renamed_terms

    def rename_variables(self, renaming: Dict[str, VariableRenamingInfo]) -> bool:
        """Rename the variables used in this relation. Returns True if any variable was renamed."""
        was_any_variable_renamed = False
        new_var_names = [renaming[var].new_name if var in renaming else var for var in self.variable_names]

        if new_var_names != self.variable_names:
            self.variable_names = new_var_names
            was_any_variable_renamed = True

        # Modulo and Div terms are frozen - they have to be recreated with correct variables
        was_any_variable_inside_modulo_renamed, self.modulo_terms = self.rename_frozen_terms(
            self.modulo_terms, renaming,
            lambda renamed_vars, mod_term: ModuloTerm(variables=renamed_vars,
                                                      variable_coefficients=mod_term.variable_coefficients,
                                                      modulo=mod_term.modulo, constant=mod_term.constant)
        )
        was_any_variable_renamed |= was_any_variable_inside_modulo_renamed

        was_any_variable_inside_div_renamed, self.div_terms = self.rename_frozen_terms(
            self.div_terms, renaming,
            lambda renamed_vars, div_term: DivTerm(variables=renamed_vars,
                                                   variable_coefficients=div_term.variable_coefficients,
                                                   divisor=div_term.divisor, constant=div_term.constant)
        )
        was_any_variable_renamed |= was_any_variable_inside_div_renamed

        self.sort_variables_alphabetically()

        return was_any_variable_renamed

    @staticmethod
    def new_lin_relation(variable_names: List[str] = [], variable_coefficients: List[int] = [],
                         absolute_part: int = 0, predicate_symbol: str = '=') -> Relation:
        return Relation(variable_names=variable_names, variable_coefficients=variable_coefficients,
                        absolute_part=absolute_part, predicate_symbol=predicate_symbol,
                        div_term_coefficients=[], div_terms=[], modulo_terms=[], modulo_term_coefficients=[])

    @staticmethod
    def new_congruence_relation(modulo_terms: List[ModuloTerm] = [], modulo_term_coefficients: List[int] = [],
                                absolute_part: int = 0) -> Relation:
        return Relation(variable_names=[], variable_coefficients=[],
                        absolute_part=absolute_part, predicate_symbol='=',
                        div_term_coefficients=[], div_terms=[], modulo_terms=modulo_terms,
                        modulo_term_coefficients=modulo_term_coefficients)

    @staticmethod
    def copy_of(relation: Relation) -> Relation:
        # Both ModuloTerm and DivTerm have frozen=True, meaning they are immutable, so no need to do a deep copy
        return Relation(variable_names=list(relation.variable_names),
                        variable_coefficients=list(relation.variable_coefficients),
                        modulo_terms=list(relation.modulo_terms),
                        modulo_term_coefficients=list(relation.modulo_term_coefficients),
                        div_terms=list(relation.div_terms),
                        div_term_coefficients=list(relation.div_term_coefficients),
                        absolute_part=relation.absolute_part, predicate_symbol=relation.predicate_symbol)
