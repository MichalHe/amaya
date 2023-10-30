from __future__ import annotations
from dataclasses import (
    dataclass,
    field,
)
from enum import Enum, IntEnum
import functools
from typing import (
    Any,
    Callable,
    Generator,
    Iterable,
    List,
    Dict,
    Generic,
    Tuple,
    TypeVar,
    Set,
    Union,
)


@dataclass(frozen=True)
class Var:
    id: int

    def __lt__(self, other: Var) -> bool:
        return self.id < other.id

    def __gt__(self, other: Var) -> bool:
        return self.id > other.id


@dataclass
class Relation(object):
    """
    Represents one atomic PrA constraint.

    Might contain modulo terms or div terms that are not evaluable directly and must be expressed in terms
    of existential quantifier.
    """
    vars: List[Var]
    coefs: List[int]
    rhs: int
    predicate_symbol: str

    def are_all_coefficients_zero(self) -> bool:
        """Returns true if all relation variable coefficients are zero."""
        return all(coef == 0 for coef in self.coefs)

    def is_always_satisfied(self) -> bool:
        """
        Returns true if all the variable cooeficients are zero and the relation is satisfied."""

        are_all_coefs_zero = self.are_all_coefficients_zero()

        if are_all_coefs_zero:
            absolute_part_conditions: Dict[str, Callable[[int], bool]] = {
                '<': lambda absolute_part: absolute_part > 0,
                '<=': lambda absolute_part: absolute_part >= 0,
                '=': lambda absolute_part: absolute_part == 0,
            }

            absolute_part_condition = absolute_part_conditions[self.predicate_symbol]
            return absolute_part_condition(self.rhs)
        return False

    def _format_term_type_into_string(self,
                                      coefs: Iterable[int],
                                      vars: List[Var],
                                      use_latex_notation: bool = False) -> Generator[str, None, None]:
        if use_latex_notation:
            var_coef_iterator = iter(zip(coefs, vars))
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
            for coef, var_name in zip(coefs, vars):
                yield '{0}{1}.{2}'.format(('+' if coef >= 0 else ''), coef, var_name)

    def into_string(self, use_latex_notation: bool = False) -> str:
        linear_terms = self._format_term_type_into_string(self.coefs, self.vars,
                                                          use_latex_notation=use_latex_notation)

        lhs = ' '.join(linear_terms)

        predicate_symbol = self.predicate_symbol
        if use_latex_notation:
            predicate_symbol = {'<=': '\\le', '>=': '\\ge'}.get(predicate_symbol, predicate_symbol)

        return f'{lhs} {predicate_symbol} {self.rhs}'

    def __str__(self):
        return self.into_string(use_latex_notation=False)

    def __repr__(self):
        return 'Relation(' + self.into_string(use_latex_notation=False) + ')'

    def is_in_canoical_form(self) -> bool:
        positive_sign_count = sum(coef >= 0 for coef in self.coefs)
        if positive_sign_count == len(self.coefs) / 2:
            return self.rhs >= 0
        return (positive_sign_count > len(self.coefs) / 2)

    def ensure_canoical_form_if_equation(self):
        """Ensures that the majority of variables/moduloterms in the relation have the positive sign if the predicate_symbol is =."""
        if self.predicate_symbol != '=':
            return
        if not self.is_in_canoical_form():
            self.variable_coefficients = [-1 * coef for coef in self.variable_coefficients]
            self.rhs *= -1

    def sort_variables(self):
        """Sorts the variables and corresponding coefficients alphabetically."""
        var_coef_pairs = zip(self.vars, self.coefs)
        sorted_var_coef_pairs = sorted(var_coef_pairs, key=lambda pair: pair[0])

        sorted_vars, sorted_coefs = zip(*sorted_var_coef_pairs) if sorted_var_coef_pairs else (tuple(), tuple())
        self.vars = list(sorted_vars)  # type: ignore
        self.coefs = list(sorted_coefs)  # type: ignore

    @staticmethod
    def new_lin_relation(variable_names: List[Var] = [], variable_coefficients: List[int] = [],
                         absolute_part: int = 0, predicate_symbol: str = '=') -> Relation:
        return Relation(vars=variable_names, coefs=variable_coefficients, rhs=absolute_part, predicate_symbol=predicate_symbol)

    def __eq__(self, other: Relation) -> bool:
        if not isinstance(other, Relation):
            return False
        if self.predicate_symbol != other.predicate_symbol:
            return False
        if self.rhs != other.rhs:
            return False
        if len(self.vars) != len(other.vars):
            return False

        # Convert to dictionaries as want comparison regardless of variable order
        self_lin_term = {var: coef for var, coef in zip(self.vars, self.coefs)}
        other_lin_term = {var: coef for var, coef in zip(other.vars, other.coefs)}

        return self_lin_term == other_lin_term


@dataclass
class Congruence:
    """A congruence a_1 * c_1 ... = rhs (mod modulus)"""
    vars: List[Var]
    coefs: List[int]
    rhs: int
    modulus: int


@dataclass
class BoolLiteral:
    """True or False formula"""
    value: bool

Frozen_AST = Union[int, str, Tuple['Raw_AST', ...]]
Raw_AST = Union[int, str, List['Raw_AST']]
AST_Atom = Union[str, Var, Congruence, Relation, BoolLiteral]
AST_NaryNode = List[Union[AST_Atom, 'AST_NaryNode']]
AST_Node = Union[AST_Atom, AST_NaryNode]


class AST_Node_Names(Enum):
    DECLARE_FUN = 'declare-fun'
    ASSERT = 'assert'
    CHECK_SAT = 'check-sat'
    EXISTS = 'exists'
    BOOL_EQUIV = '='
    AND = 'and'
    OR = 'or'
    NOT = 'not'


def ast_get_node_type(node: AST_NaryNode) -> str:
    node_type: str = node[0]  # type: ignore
    return node_type


def ast_get_binding_list(exists_node: AST_NaryNode) -> List[Var]:
    binding_list: List[Var] = exists_node[1]  # type: ignore
    return binding_list


def make_exists_node(binding_list: List[Tuple[str, str]], subformula: AST_Node) -> AST_Node:
    # @Note: We convert the tuples into lists because the rest of the solver might expect so
    # #      however we should have a more proper types for the entire AST
    _binding_list = [list(binding) for binding in binding_list]
    return [AST_Node_Names.EXISTS.value, _binding_list, subformula]  # type: ignore


def make_and_node(subformulae: List[AST_Node]) -> AST_Node:
    return [AST_Node_Names.AND.value, *subformulae]


def make_or_node(subformulae: List[AST_Node]) -> AST_Node:
    return [AST_Node_Names.OR.value, *subformulae]


def make_not_node(subformula: AST_Node) -> AST_Node:
    return [AST_Node_Names.NOT.value, subformula]


@dataclass
class NodeEncounteredHandlerStatus:
    should_reevaluate_result: bool
    is_result_atomic: bool
    do_not_descend_further: bool = False


NodeEncounteredHandler = Callable[[AST_NaryNode, bool, Dict], NodeEncounteredHandlerStatus]


class VariableType(IntEnum):
    INT = 1
    BOOL = 2
    UNSET = 3

    @staticmethod
    def from_smt_type_string(type_str: str) -> VariableType:
        m = {
            'Bool': VariableType.BOOL,
            'Int': VariableType.INT,
        }
        return m[type_str]


@dataclass
class FunctionSymbol:
    name: str
    arity: int
    args: List[Tuple[str, VariableType]]
    return_type: VariableType
