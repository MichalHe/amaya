from __future__ import annotations
from collections import defaultdict
from collections.abc import Iterable
from dataclasses import dataclass, field
from enum import Enum
import itertools
from typing import Dict, List, Optional, Set, Tuple, Union

from amaya import logger
from amaya.config import solver_config
from amaya.relations_structures import (
    AST_Atom,
    AST_NaryNode,
    AST_Node,
    BoolLiteral,
    Congruence,
    Raw_AST,
    Relation,
)


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


@dataclass(frozen=True)
class LinTerm:
    coef: int
    var: str


class RelationType(Enum):
    EQ = '='
    INEQ = '<='
    CONGRUENCE = '~'


@dataclass(frozen=True)
class FrozenRelation:
    lhs: Tuple[LinTerm, ...]
    rhs: int
    type: RelationType
    modulus: int = 0  # Only when type = congruence


@dataclass(unsafe_hash=True)
class NonlinTermNode:
    """A node in the term dependency graph"""

    introduced_vars: Tuple[str, ...] = field(hash=True)
    """ Variables used to express the term that need to be quantified. """

    equivalent_lin_expression: Tuple[LinTerm, ...] = field(hash=True)

    atoms_relating_introduced_vars: Tuple[FrozenRelation, ...] = field(hash=True)
    """ If multiple variables are introduced, they need to be related via extra atoms. """

    body: NonlinTerm = field(hash=True)

    was_dropped: bool = field(hash=False, default=False)

    dependent_terms: Set[NonlinTermNode] = field(default_factory=set, hash=False)


def make_node_for_two_variable_rewrite(term: NonlinTerm, rewrite_id: int) -> NonlinTermNode:
    """
    Create a node describing rewrite of the given term using two new variables (quotient and reminder).

    Div term is rewritten as:
        x - (y div D) = 0   --->   x - <QUOTIENT> && 0 <= <REMINDER> && <REMINDER> <= M-1 && y - D*<QUOTIENT> = <REMINDER>
    Mod term is rewritten as:
        x - (y mod D) = 0   --->   x - <REMINDER> && 0 <= <REMINDER> && <REMINDER> <= M-1 && y - D*<QUOTIENT> = <REMINDER>
    """
    quotient = f'D{rewrite_id}'
    reminder = f'M{rewrite_id}'
    introduced_vars = (quotient, reminder)
    if term.type == NonlinTermType.MOD:
        equiv_expr = (LinTerm(coef=1, var=reminder),)
    else:
        equiv_expr = (LinTerm(coef=1, var=quotient),)

    larger_than_zero = FrozenRelation(lhs=(LinTerm(coef=-1, var=reminder),), rhs=0, type=RelationType.INEQ)
    smaller_than_modulus = FrozenRelation(lhs=(LinTerm(coef=1, var=reminder),), rhs=term.nonlin_constant-1, type=RelationType.INEQ)

    divisor_reminder_terms = [LinTerm(var=var, coef=coef) for var, coef in term.lin_terms]
    divisor_reminder_terms.extend([LinTerm(coef=-term.nonlin_constant, var=quotient), LinTerm(coef=-1, var=reminder)])
    divisor_reminder_terms = sorted(divisor_reminder_terms, key=lambda term: term.var)

    divisor_reminder_atom = FrozenRelation(lhs=tuple(divisor_reminder_terms), rhs=0, type=RelationType.EQ)

    relating_atoms = (larger_than_zero, smaller_than_modulus, divisor_reminder_atom)
    node = NonlinTermNode(introduced_vars=introduced_vars, equivalent_lin_expression=equiv_expr,
                          atoms_relating_introduced_vars=relating_atoms, body=term)
    return node


def make_node_for_single_variable_rewrite(term: NonlinTerm, rewrite_id: int) -> NonlinTermNode:
    """
    Create a node describing rewrite of the given term using a single new variable (quotient).

    Div term is rewritten as:
        x - (y div M) = 0   --->   x - <QUOTIENT> && 0 <= (y - M*<QUOTIENT>) && (y - M*<QUOTIENT>) <= M-1
    Mod term is rewritten as:
        x - (y mod M) = 0   --->   x - (y - M*<QUOTIENT>) && 0 <= (y - M*<QUOTIENT>) && (y - M*<QUOTIENT>) <= M-1
    """
    quotient = f'D{rewrite_id}'
    introduced_vars = (quotient, )

    # (y - M*<QUOTIENT>)
    _reminder_expr = [LinTerm(coef=coef, var=var) for var, coef in term.lin_terms] + [LinTerm(coef=-term.nonlin_constant, var=quotient)]
    _reminder_expr = sorted(_reminder_expr, key=lambda lin_term: lin_term.var)
    reminder_expr = tuple(_reminder_expr)

    negated_equiv_expr = tuple(LinTerm(coef=-term.coef, var=term.var) for term in reminder_expr)
    larger_than_zero = FrozenRelation(lhs=negated_equiv_expr, rhs=0, type=RelationType.INEQ)

    smaller_than_modulus = FrozenRelation(lhs=reminder_expr, rhs=term.nonlin_constant-1, type=RelationType.INEQ)

    equiv_expr = reminder_expr if term.type == NonlinTermType.MOD else (LinTerm(coef=1, var=quotient),)

    relating_atoms = (larger_than_zero, smaller_than_modulus)
    node = NonlinTermNode(introduced_vars=introduced_vars, equivalent_lin_expression=equiv_expr,
                          atoms_relating_introduced_vars=relating_atoms, body=term)
    return node


@dataclass
class NonlinTermGraph:
    index: Dict[str, List[NonlinTermNode]] = field(default_factory=lambda: defaultdict(list))
    term_nodes: Dict[NonlinTerm, NonlinTermNode] = field(default_factory=dict)
    graph_roots: Set[NonlinTermNode] = field(default_factory=set)

    def make_term_known(self, term: NonlinTerm) -> NonlinTermNode:
        if term in self.term_nodes:
            return self.term_nodes[term]

        var_id = len(self.term_nodes)

        if term.type == NonlinTermType.MOD and solver_config.preprocessing.use_congruences_when_rewriting_modulo:
            reminder = f'M{var_id}'
            introduced_vars = (reminder,)

            equiv_expr = (LinTerm(coef=1, var=reminder),)

            larger_than_zero = FrozenRelation(lhs=(LinTerm(coef=-1, var=reminder),), rhs=0, type=RelationType.INEQ)
            smaller_than_modulus = FrozenRelation(lhs=(LinTerm(coef=1, var=reminder),), rhs=term.nonlin_constant-1, type=RelationType.INEQ)

            congruence_terms = [LinTerm(var=var, coef=coef) for var, coef in term.lin_terms]
            congruence_terms.append(LinTerm(coef=-1, var=reminder))
            congruence_terms = sorted(congruence_terms, key=lambda term: term.var)  # sort to have a canonical representation

            congruence = FrozenRelation(lhs=tuple(congruence_terms), rhs=term.nonlin_constant-1, modulus=term.nonlin_constant, type=RelationType.CONGRUENCE)

            relating_atoms = (larger_than_zero, smaller_than_modulus, congruence)
            node = NonlinTermNode(introduced_vars=introduced_vars, equivalent_lin_expression=equiv_expr,
                                  atoms_relating_introduced_vars=relating_atoms, body=term)
        else:
            if solver_config.preprocessing.use_two_vars_when_rewriting_nonlin_terms:
                node = make_node_for_two_variable_rewrite(term, rewrite_id=len(self.term_nodes))
            else:
                node = make_node_for_single_variable_rewrite(term, rewrite_id=len(self.term_nodes))

        self.term_nodes[term] = node
        return node

    def make_node_root(self, node: NonlinTermNode):
        if node in self.graph_roots:
            return

        self.graph_roots.add(node)
        for var, _ in node.body.lin_terms:
            self.index[var].append(node)

    def drop_nodes_for_var(self, var: str) -> List[NonlinTermNode]:
        work_list = list(self.index[var])

        dropped_nodes = []
        while work_list:
            node = work_list.pop(-1)

            if node.was_dropped:
                # In case the root node is dependent on multiple variables quantified on the same level
                # the node might already be dropped
                continue

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



def normalize_expr(ast: Raw_AST, nonlinear_term_graph: NonlinTermGraph) -> Tuple[Expr, Set[NonlinTermNode], Set[str]]:
    if isinstance(ast, str):
        try:
            int_val = int(ast)
            return Expr(constant_term=int_val), set(), set()
        except ValueError:
            return Expr(linear_terms={ast: 1}), set(), {ast}

    assert isinstance(ast, list)
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

        expr = Expr(linear_terms={term.var: term.coef for term in term_node.equivalent_lin_expression})

        if not dependent_terms:
            nonlinear_term_graph.make_node_root(term_node)

        support.update(term_node.introduced_vars)
        return expr, {term_node}, support

    raise ValueError(f'Cannot reduce unknown expression to evaluable form. {ast=}')


def convert_relation_to_evaluable_form(ast: Raw_AST, dep_graph: NonlinTermGraph) -> Tuple[Union[Relation, BoolLiteral], ASTInfo]:
    assert isinstance(ast, list)
    predicate_symbol = ast[0]
    if not isinstance(predicate_symbol, str):
        raise ValueError(f'Cannot construct equation for predicate symbol that is not a string: {predicate_symbol=}')

    lhs, _, lhs_support = normalize_expr(ast[1], dep_graph)  # Will remove nonlinear terms and replace them with new variables
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


def split_lin_terms_into_vars_and_coefs(terms: Iterable[LinTerm]) -> Tuple[List[str], List[int]]:
    vars, coefs = [], []
    for term in terms:
        coefs.append(term.coef)
        vars.append(term.var)
    return vars, coefs


def generate_atoms_for_term(node: NonlinTermNode) -> List[AST_Atom]:
    atoms = []
    for frozen_atom in node.atoms_relating_introduced_vars:
        vars, coefs = split_lin_terms_into_vars_and_coefs(frozen_atom.lhs)
        if frozen_atom.type == RelationType.EQ or frozen_atom.type == RelationType.INEQ:
            atom = Relation.new_lin_relation(variable_names=vars, variable_coefficients=coefs,
                                             absolute_part=frozen_atom.rhs, predicate_symbol=frozen_atom.type.value)
        else:
            atom = Congruence(vars=vars, coefs=coefs, rhs=frozen_atom.rhs, modulus=frozen_atom.modulus)
        atoms.append(atom)
    return atoms


def is_any_member_if_str(container, elem1, elem2):
    return (isinstance(elem1, str) and elem1 in container) or (isinstance(elem2, str) and elem2 in container)


def is_any_node_of_type(types: Iterable[str], node1, node2):
    is_node1 = isinstance(node1, list) and node1[0] in types
    is_node2 = isinstance(node2, list) and node2[0] in types
    return is_node1 or is_node2


def _convert_ast_into_evaluable_form(ast: Raw_AST, dep_graph: NonlinTermGraph, bool_vars: Set[str]) -> Tuple[AST_Node, ASTInfo]:
    if isinstance(ast, str):
        return ast, ASTInfo(used_vars={ast})

    assert isinstance(ast, list), f'Freestanding integer found - not a part of any atom: {ast}'
    node_type = ast[0]
    assert isinstance(node_type, str)

    if node_type in {'and', 'or'}:
        new_node: AST_Node = [node_type]
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
        new_node: AST_Node = [node_type]
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
        dropped_nodes: List[NonlinTermNode] = []
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

            new_binders_in_node = [[introduced_var, 'Int'] for term_node in dropped_nodes for introduced_var in term_node.introduced_vars]
            new_node[1] += new_binders_in_node  # type: ignore
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


def convert_ast_into_evaluable_form(ast: Raw_AST, bool_vars: Set[str]) -> Tuple[AST_Node, ASTInfo]:
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

    introduced_vars = itertools.chain(*(node.introduced_vars for node in dropped_nodes))
    binding_list = [[var, 'Int'] for var in introduced_vars]
    new_atoms = []
    for dropped_node in dropped_nodes:
        new_atoms += generate_atoms_for_term(dropped_node)

    new_ast = ['exists', binding_list, ['and', new_ast, *new_atoms]]  # type: ignore
    return new_ast, ASTInfo()
