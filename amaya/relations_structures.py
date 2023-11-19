from __future__ import annotations
from dataclasses import (
    dataclass,
    field,
)
from enum import Enum, IntEnum
import functools
import math
from typing import (
    Any,
    Callable,
    Generator,
    Iterable,
    List,
    Dict,
    Generic,
    Optional,
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

    def linear_terms(self) -> Generator[Tuple[int, Var], None, None]:
        for coef, var in zip(self.coefs, self.vars):
            yield (coef, var)

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

    def is_hard_bound(self) -> bool:
        return len(self.vars) == 1 and self.predicate_symbol == '<='


@dataclass
class Congruence:
    """A congruence a_1 * c_1 ... = rhs (mod modulus)"""
    vars: List[Var]
    coefs: List[int]
    rhs: int
    modulus: int

    def linear_terms(self) -> Generator[Tuple[int, Var], None, None]:
        for term in zip(self.coefs, self.vars):
            yield term

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


def make_exists_node(bound_vars: List[Var], subformula: AST_Node) -> AST_NaryNode:
    return [AST_Node_Names.EXISTS.value, list(bound_vars), subformula]  # type: ignore


def make_and_node(subformulae: List[AST_Node]) -> AST_NaryNode:
    return [AST_Node_Names.AND.value, *subformulae]


def make_or_node(subformulae: List[AST_Node]) -> AST_NaryNode:
    return [AST_Node_Names.OR.value, *subformulae]


def make_not_node(subformula: AST_Node) -> AST_NaryNode:
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
class Value_Interval:
    lower_limit: Optional[int] = None
    upper_limit: Optional[int] = None

    def __repr__(self) -> str:
        lower = self.lower_limit if self.lower_limit is not None else '-inf'
        upper = self.upper_limit if self.upper_limit is not None else '+inf'
        return f'<{lower}, {upper}>'

    def try_strengthen_lower(self, new_lower: int):
        if self.lower_limit is None:
            self.lower_limit = new_lower
        else:
            self.lower_limit = max(self.lower_limit, new_lower)

    def try_strengthen_upper(self, new_upper: int):
        if self.upper_limit is None:
            self.upper_limit = new_upper
        else:
            self.upper_limit = min(self.upper_limit, new_upper)

    def synthetize_atoms(self, var: Var) -> Tuple[Relation, ...]:
        atoms = []
        if self.lower_limit is not None:
            lower_limit = Relation(vars=[var], coefs=[-1], rhs=-self.lower_limit, predicate_symbol='<=')
            atoms.append(lower_limit)
        if self.upper_limit is not None:
            upper_limit = Relation(vars=[var], coefs=[1], rhs=self.upper_limit, predicate_symbol='<=')
            atoms.append(upper_limit)
        return tuple(atoms)


@dataclass
class FunctionSymbol:
    name: str
    arity: int
    args: List[Tuple[str, VariableType]]
    return_type: VariableType


@dataclass
class ASTp_Node_Base:
    referenced_vars: Tuple[Var,...] = field(repr=False)


@dataclass
class AST_Negation(ASTp_Node_Base):
    child: ASTp_Node


@dataclass
class AST_Quantifier(ASTp_Node_Base):
    bound_vars: Tuple[Var, ...]
    child: ASTp_Node


class Connective_Type(IntEnum):
    AND   = 0x01
    OR    = 0x02
    EQUIV = 0x03


@dataclass
class AST_Connective(ASTp_Node_Base):
    type: Connective_Type
    children: Tuple[ASTp_Node, ...]
    variable_bounds: Optional[Dict[Var, Value_Interval]] = field(default=None, repr=False)

    def replace_children(self, new_children: Tuple[ASTp_Node, ...]) -> AST_Connective:
        return AST_Connective(referenced_vars=self.referenced_vars,
                              type=self.type,
                              children=new_children,
                              variable_bounds=self.variable_bounds)

ASTp_Leaf_Type_List = (Relation, Congruence, BoolLiteral, Var)
ASTp_Node = Union[AST_Connective, AST_Negation, AST_Quantifier, Relation, Congruence, BoolLiteral, Var]


def _collect_referenced_vars(children: Iterable[ASTp_Node]) -> Tuple[Var, ...]:
    refd_vars: Set[Var] = set()

    for child in children:
        if isinstance(child, (Relation, Congruence)):
            refd_vars.update(child.vars)
            continue
        if isinstance(child, Var):
            refd_vars.add(child)
            continue
        if isinstance(child, BoolLiteral):
            continue

        refd_vars.update(child.referenced_vars)

    return tuple(sorted(refd_vars))


def _collect_referenced_vars_unary(child: ASTp_Node):
    if isinstance(child, (Relation, Congruence)):
        return tuple(child.vars)
    if isinstance(child, Var):
        return (child,)
    if isinstance(child, BoolLiteral):
        return tuple()
    return child.referenced_vars


def convert_ast_into_astp(ast: AST_Node) -> ASTp_Node:
    if isinstance(ast, (Relation, Congruence, BoolLiteral, Var)):
        return ast

    assert isinstance(ast, list)
    node_type = ast_get_node_type(ast)

    match node_type:
        case 'and':
            children = tuple(convert_ast_into_astp(child) for child in ast[1:])
            referenced_vars = _collect_referenced_vars(children)
            return AST_Connective(type=Connective_Type.AND, referenced_vars=referenced_vars, children=children)
        case 'or':
            children = tuple(convert_ast_into_astp(child) for child in ast[1:])
            referenced_vars = _collect_referenced_vars(children)
            return AST_Connective(type=Connective_Type.OR, referenced_vars=referenced_vars, children=children)
        case '=':
            children = tuple(convert_ast_into_astp(child) for child in ast[1:])
            referenced_vars = _collect_referenced_vars(children)
            return AST_Connective(type=Connective_Type.EQUIV, referenced_vars=referenced_vars, children=children)
        case 'not':
            child = convert_ast_into_astp(ast[1])
            return AST_Negation(child=child, referenced_vars=_collect_referenced_vars_unary(child))
        case 'exists':
            bound_vars: Tuple[Var,...] = tuple(ast_get_binding_list(ast))
            child = convert_ast_into_astp(ast[2])
            return AST_Quantifier(referenced_vars=_collect_referenced_vars_unary(child), bound_vars=bound_vars, child=child)
        case _:
            raise NotImplementedError(f'Unhandled branch when converting AST into ASTp: {ast}')


def pprint_formula(ast: ASTp_Node, indent: int = 0):
    indent_str = '   ' * indent
    match ast:
        case BoolLiteral() | Relation() | Congruence() | Var():
            print(f'{indent_str}{ast}')
        case AST_Connective():
            connective_symbol_table = {
                Connective_Type.AND:   'and',
                Connective_Type.OR:    'or',
                Connective_Type.EQUIV: '<=>'
            }
            symbol = connective_symbol_table[ast.type]
            print(f'{indent_str}{symbol}')
            for child in ast.children:
                pprint_formula(child,  indent=indent+1)
        case AST_Negation():
            print(f'{indent_str}NOT')
            pprint_formula(ast.child,  indent=indent+1)
        case AST_Quantifier():
            _var_list = [f'x{var.id}' for var in ast.bound_vars]
            var_list = ','.join(_var_list)
            print(f'{indent_str}exists ({var_list})')
            pprint_formula(ast.child,  indent=indent+1)
        case _:
            raise NotImplementedError(f'Unhandled node while pprinting formula: {ast=}')


class Bound_Type(IntEnum):
    LOWER = 0x01
    UPPER = 0x02


def get_hard_bound_semantics(rel: Relation) -> Tuple[Bound_Type, Var, int]:
    var, coef = rel.vars[0], rel.coefs[0]
    if coef < 0:
        implied_val = math.ceil(rel.rhs / coef)
        bound_type = Bound_Type.LOWER
    else:
        implied_val = math.floor(rel.rhs / coef)
        bound_type = Bound_Type.UPPER

    return (bound_type, var, implied_val)


def compute_implied_bound(var: Var, coef: int, bound_rhs: int) -> int:
    if coef < 0:
        return math.ceil(bound_rhs  / coef)
    return math.floor(bound_rhs / coef)

