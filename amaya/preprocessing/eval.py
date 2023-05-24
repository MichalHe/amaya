from __future__ import annotations
from collections import defaultdict
from collections.abc import Iterable
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple, Union

from amaya import logger
from amaya.ast_definitions import AST_NaryNode
from amaya.relations_structures import BoolLiteral, Congruence, DivTerm, ModuloTerm, Relation


class NonlinTermType(Enum):
    DIV = 'div'
    MOD = 'mod'


@dataclass(frozen=True)
class NonlinTerm:
    lin_terms: Tuple[Tuple[str, int]]
    nonlin_constant: int
    """Divisor in when the term is DIV, modulus when the term is MOD"""
    type: NonlinTermType
    lin_term_constant: int = 0


@dataclass(unsafe_hash=True)
class NonlinTermNode:
    """A node in the term dependency graph"""
    var: str = field(hash=True)
    body: NonlinTerm = field(hash=True)
    was_dropped: bool = field(hash=False, default=False)
    dependent_terms: Set[NonlinTermNode] = field(default_factory=set, hash=False)


@dataclass
class NonlinTermGraph:
    index: Dict[str, List[NonlinTermNode]] = field(default_factory=lambda: defaultdict(list))
    term_nodes: Dict[NonlinTerm, NonlinTermNode] = field(default_factory=dict)
    graph_roots: Set[NonlinTermNode] = field(default_factory=set)

    def make_term_known(self, term: NonlinTerm) -> NonlinTermNode:
        if term in self.term_nodes:
            return self.term_nodes[term]

        var_prefix = 'M' if term.type == NonlinTermType.MOD else 'D'
        var = f'{var_prefix}{len(self.term_nodes)}'
        node = NonlinTermNode(var=var, body=term)
        self.term_nodes[term] = node
        return node

    def make_node_root(self, node: NonlinTermNode):
        self.graph_roots.add(node)
        for var, _ in node.body.lin_terms:
            self.index[var].append(node)

    def drop_nodes_for_var(self, var: str) -> List[NonlinTermNode]:
        work_list = list(self.index[var])

        dropped_nodes = []
        while work_list:
            node = work_list.pop(-1)
            dropped_nodes.append(node)

            node.was_dropped = True
            for dependent_node in node.dependent_terms:
                if not dependent_node.was_dropped:
                    dependent_node.was_dropped = True
                    work_list.append(dependent_node)
        return dropped_nodes


@dataclass
class Expr:
    """A linear arithmetical expression of the form c_1*a_1 + c_2*a_2 + K"""
    constant_term: int = 0
    linear_terms: Dict[str, int] = field(default_factory=dict)

    def __neg__(self) -> Expr:
        negated_lin_terms = {var: -coef for var, coef in self.linear_terms.items()}
        return Expr(constant_term=-self.constant_term, linear_terms=negated_lin_terms)

    def __sub__(self, other: Expr) -> Expr:
        lin_terms = dict(self.linear_terms)
        for var, coef in other.linear_terms.items():
            lin_terms[var] = lin_terms.get(var, 0) - coef
            if lin_terms[var] == 0:
                del lin_terms[var]
        const_term = self.constant_term - other.constant_term
        return Expr(constant_term=const_term, linear_terms=lin_terms)

    def __add__(self, other: Expr) -> Expr:
        lin_terms = dict(self.linear_terms)
        for var, coef in other.linear_terms.items():
            lin_terms[var] = lin_terms.get(var, 0) + coef
            if lin_terms[var] == 0:
                del lin_terms[var]
        const_term = self.constant_term + other.constant_term
        return Expr(constant_term=const_term, linear_terms=lin_terms)

    def __mul__(self, other: Expr) -> Expr:
        lin_expr, const_expr = (self, other) if not other.linear_terms else (other, self)
        if const_expr.linear_terms:
            raise ValueError(f'Attempting to multiply two Expressions containing variables {lin_expr} * {const_expr}')

        multiplier = const_expr.constant_term
        lin_terms = {var: multiplier*coef for var, coef in lin_expr.linear_terms.items()}
        return Expr(constant_term=multiplier*lin_expr.constant_term, linear_terms=lin_terms)


@dataclass
class ASTInfo:
    used_vars: Set[str] = field(default_factory=set)


Atom = Union[Relation, Congruence, BoolLiteral]
Raw_AST = Union[str, List['Raw_AST']]
Evaluable_AST = Union[str, Atom, List['Evaluable_AST']]


def normalize_expr(ast: Raw_AST, nonlinear_term_graph: NonlinTermGraph) -> Tuple[Expr, Set[NonlinTermNode], Set[str]]:
    if isinstance(ast, str):
        try:
            int_val = int(ast)
            return Expr(constant_term=int_val), set(), set()
        except ValueError:
            return Expr(linear_terms={ast: 1}), set(), {ast}

    node_type = ast[0]

    expr_reductions = {'*': Expr.__mul__, '-': Expr.__sub__, '+': Expr.__add__}  # all are left-associative

    if len(ast) > 2 and node_type in expr_reductions:
        reduction = expr_reductions[node_type]
        left, dependent_terms, support = normalize_expr(ast[1], nonlinear_term_graph)
        for operand_ast in ast[2:]:
            operand, dependent_term, other_support = normalize_expr(operand_ast, nonlinear_term_graph)
            dependent_terms.update(dependent_term)
            support.update(other_support)
            left = reduction(left, operand)
        return left, dependent_terms, support
    elif len(ast) == 2 and node_type == '-':
        operand, dependent_terms, support = normalize_expr(ast[1], nonlinear_term_graph)
        return -operand, dependent_terms, support
    elif node_type in {'mod', 'div'}:
        lin_term, dependent_terms, support = normalize_expr(ast[1], nonlinear_term_graph)
        nonlin_constant, _, _ = normalize_expr(ast[2], nonlinear_term_graph)
        lin_terms = tuple(sorted(lin_term.linear_terms.items(), key=lambda var_coef_pair: var_coef_pair[0]))
        term_body = NonlinTerm(lin_terms=lin_terms, lin_term_constant=lin_term.constant_term,
                               type=NonlinTermType(node_type), nonlin_constant=nonlin_constant.constant_term)

        term_node = nonlinear_term_graph.make_term_known(term_body)

        for dep_term in dependent_terms:
            dep_term.dependent_terms.add(term_node)

        expr = Expr(linear_terms={term_node.var: 1})

        if not dependent_terms:
            nonlinear_term_graph.make_node_root(term_node)

        support.add(term_node.var)
        return expr, {term_node}, support

    raise ValueError(f'Cannot reduce unknown expression to evaluable form. {ast=}')


def convert_relation_to_evaluable_form(ast: Raw_AST, dep_graph: NonlinTermGraph) -> Tuple[Union[Relation, BoolLiteral], ASTInfo]:
    predicate_symbol = ast[0]
    if not isinstance(predicate_symbol, str):
        raise ValueError(f'Cannot construct equation for predicate symbol that is not a string: {predicate_symbol=}')

    lhs, _, lhs_support = normalize_expr(ast[1], dep_graph)
    rhs, _, rhs_support = normalize_expr(ast[2], dep_graph)
    support = lhs_support.union(rhs_support)
    top_level_support = set(lhs.linear_terms.keys()) | set(rhs.linear_terms.keys())

    if predicate_symbol in ('>=', '>'):
        lhs, rhs = rhs, lhs
        predicate_symbol = '<=' if predicate_symbol == '>=' else '<'

    norm = lhs - rhs
    new_top_level_support = set(norm.linear_terms.keys())

    if not new_top_level_support:
        return BoolLiteral(value=True), ASTInfo()

    # Remove variables that are not part of the support after norm has been calculated - diff might have result in some coef=0
    support = support - (top_level_support - new_top_level_support)

    vars, coefs = [], []
    for var, coef in sorted(norm.linear_terms.items(), key=lambda var_coef_pair: var_coef_pair[0]):
        vars.append(var)
        coefs.append(coef)

    abs_part = -norm.constant_term
    if predicate_symbol == '<':
        predicate_symbol = '<='
        abs_part -= 1

    relation = Relation.new_lin_relation(variable_names=vars, variable_coefficients=coefs,
                                         absolute_part=abs_part, predicate_symbol=predicate_symbol)

    # The relation might use some variables transiently trough the use of mod/div terms, include them
    # for var in vars:

    ast_info = ASTInfo(used_vars=support)

    return relation, ast_info


def generate_atoms_for_term(node: NonlinTermNode) -> List[Atom]:
    term = node.body

    def split_lin_terms_into_vars_and_coefs(terms: Iterable[Tuple[str, int]]) -> Tuple[List[str], List[int]]:
        vars, coefs = [], []
        for var, coef in terms:
            vars.append(var)
            coefs.append(coef)
        return vars, coefs

    if term.type == NonlinTermType.MOD:
        lower_bound = Relation.new_lin_relation(variable_names=[node.var], variable_coefficients=[-1],
                                                absolute_part=0, predicate_symbol='<=')
        upper_bound = Relation.new_lin_relation(variable_names=[node.var], variable_coefficients=[1],
                                                absolute_part=term.nonlin_constant-1, predicate_symbol='<=')

        rhs = (-term.lin_term_constant) % term.nonlin_constant
        if rhs < 0:
            rhs += term.nonlin_constant

        # Make a congruence as <original_term> - reminder = <-original_term_abs> (mod modulus)
        lin_terms = list(term.lin_terms) + [(node.var, -1)]
        lin_terms = sorted(lin_terms, key=lambda item: item[0])
        vars, coefs = split_lin_terms_into_vars_and_coefs(lin_terms)
        congruence = Congruence(vars=vars, coefs=coefs, rhs=rhs, modulus=term.nonlin_constant)

        return [lower_bound, upper_bound, congruence]

    # The new variable is used to express the properties of difference: <original_term> - existential_var * divisor
    var_coefs = list(term.lin_terms) + [(node.var, -term.nonlin_constant)]
    var_ceofs = sorted(var_coefs, key=lambda item: item[0])
    vars, coefs = split_lin_terms_into_vars_and_coefs(var_coefs)

    neg_coefs = [-coef for coef in coefs]
    lower_bound = Relation.new_lin_relation(variable_names=vars, variable_coefficients=neg_coefs,
                                            absolute_part=0, predicate_symbol='<=')
    upper_bound = Relation.new_lin_relation(variable_names=vars, variable_coefficients=coefs,
                                            absolute_part=term.nonlin_constant - 1, predicate_symbol='<=')
    return [lower_bound, upper_bound]


def is_any_member_if_str(container, elem1, elem2):
    return (isinstance(elem1, str) and elem1 in container) or (isinstance(elem2, str) and elem2 in container)

def is_any_node_of_type(types: Iterable[str], node1, node2):
    is_node1 = isinstance(node1, list) and node1[0] in types
    is_node2 = isinstance(node2, list) and node2[0] in types
    return is_node1 or is_node2


def _convert_ast_into_evaluable_form(ast: Raw_AST, dep_graph: NonlinTermGraph, bool_vars: Set[str]) -> Tuple[Evaluable_AST, ASTInfo]:
    if isinstance(ast, str):
        return ast, ASTInfo(used_vars={ast})

    node_type = ast[0]
    assert isinstance(node_type, str)

    if node_type in {'and', 'or'}:
        new_node: Evaluable_AST = [node_type]
        tree_info = ASTInfo()
        for child in ast[1:]:
            new_child, child_tree_info = _convert_ast_into_evaluable_form(child, dep_graph, bool_vars)
            new_node.append(new_child)
            tree_info.used_vars.update(child_tree_info.used_vars)
        return new_node, tree_info

    if node_type == 'not':
        child, child_ast_info = _convert_ast_into_evaluable_form(ast[1], dep_graph, bool_vars)
        if isinstance(child, BoolLiteral):
            return BoolLiteral(value=not child.value), child_ast_info
        return ['not', child], child_ast_info

    if node_type == 'exists':
        new_node: Evaluable_AST = [node_type]
        bound_vars: List[str] = [var for var, dummy_type in ast[1]]  # type: ignore

        child, child_ast_info = _convert_ast_into_evaluable_form(ast[2], dep_graph, bool_vars)

        binding_list = [[var, type] for var, type in ast[1] if var in child_ast_info.used_vars]
        if not binding_list:
            # The underlying AST could be x = x, which would be reduced to BoolLiteral(True). Remove the quantifier
            # all together
            return child, child_ast_info

        new_node.append(binding_list)  # type: ignore

        # Child's AST Info will represent this node - remove all currently bound variables
        for var in bound_vars:
            if var in child_ast_info.used_vars:  # A variable might be not be used e.g when x + y = x
                child_ast_info.used_vars.remove(var)

        # Try dropping any of the bound vars - collect nonlinear terms (graph nodes) that have to be instantiated
        dropped_nodes = []
        for var in bound_vars:
            dropped_nodes += dep_graph.drop_nodes_for_var(var)

        new_atoms = []
        for dropped_node in dropped_nodes:
            new_atoms += generate_atoms_for_term(dropped_node)

        if dropped_nodes:
            if isinstance(child, list) and child[0] == 'and':
                child += new_atoms
            else:
                child = ['and', child] + new_atoms
            new_node[1] += [[term_node.var, 'Int'] for term_node in dropped_nodes]  # type: ignore

        new_node.append(child)

        return new_node, child_ast_info

    if node_type == '=':
        connectives = {'and', 'or', 'not', 'exists', 'forall'}
        if is_any_member_if_str(bool_vars, ast[1], ast[2]) or is_any_node_of_type(connectives, ast[1], ast[2]):
            lhs, lhs_info = _convert_ast_into_evaluable_form(ast[1], dep_graph, bool_vars)
            rhs, rhs_info = _convert_ast_into_evaluable_form(ast[2], dep_graph, bool_vars)
            lhs_info.used_vars.update(rhs_info.used_vars)
            return ['=', lhs, rhs], lhs_info
        lia_symbols = {'+', '-', '*', 'mod', 'div'}
        if is_any_node_of_type(lia_symbols, ast[1], ast[2]):
            return convert_relation_to_evaluable_form(ast, dep_graph)

        logger.info('Not sure whether %s is a Boolean equivalence or an atom, reducing to atom.', ast)
        return convert_relation_to_evaluable_form(ast, dep_graph)

    if node_type in ['<=', '<', '>', '>=']:
        return convert_relation_to_evaluable_form(ast, dep_graph)

    raise ValueError(f'Cannot traverse trough {node_type=} while converting AST into evaluable form. {ast=}')


def convert_ast_into_evaluable_form(ast: Raw_AST, bool_vars: Set[str]) -> Tuple[Evaluable_AST, ASTInfo]:
    dep_graph = NonlinTermGraph()
    new_ast, new_ast_info = _convert_ast_into_evaluable_form(ast, dep_graph, bool_vars)

    # There might be non-linear terms still not rewritten, e.g., if the lin. term inside the modulo term
    # depends on global symbols
    vars_with_undropped_nodes = [
        var for var, root_nodes in dep_graph.index.items() if any(not node.was_dropped for node in root_nodes)
    ]

    if not vars_with_undropped_nodes:
        return new_ast, ASTInfo()

    dropped_nodes = []
    for var in vars_with_undropped_nodes:
        dropped_nodes += dep_graph.drop_nodes_for_var(var)

    assert dropped_nodes

    binding_list = [[node.var, 'Int'] for node in dropped_nodes]
    new_atoms = []
    for dropped_node in dropped_nodes:
        new_atoms += generate_atoms_for_term(dropped_node)

    new_ast = ['exists', binding_list, ['and', new_ast, new_atoms]]  # type: ignore
    return new_ast, ASTInfo()
