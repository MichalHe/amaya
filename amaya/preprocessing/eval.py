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
    AST_Node_Names,
    BoolLiteral,
    Congruence,
    FunctionSymbol,
    Raw_AST,
    Relation,
    Var,
    VariableType,
)


class NonlinTermType(Enum):
    DIV = 'div'
    MOD = 'mod'


@dataclass(frozen=True)
class NonlinTerm:
    lin_terms: Tuple[Tuple[Var, int]]
    nonlin_constant: int
    type: NonlinTermType = field(hash=False, compare=False)
    """Divisor in when the term is DIV, modulus when the term is MOD"""
    lin_term_constant: int = 0


@dataclass(frozen=True)
class LinTerm:
    coef: int
    var: Var


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


@dataclass
class VarInfo:
    name: str
    type: VariableType


class Scoper:
    def __init__(self, global_symbols: Iterable[Tuple[str, VariableType]]):
        self.scopes: List[Dict[str, Var]] = []
        self.var_table: Dict[Var, VarInfo] = {}
        self.next_var_id: int = 1

        global_scope: Dict[str, Var] = {}
        self.scopes.append(global_scope)

        for var_name, var_type in global_symbols:
            var = Var(id=self.next_var_id)
            self.next_var_id += 1
            global_scope[var_name] = var
            self.var_table[var] = VarInfo(name=var_name, type=var_type)

    def enter_quantifier(self, quantified_vars: List[Tuple[str, str]]) -> List[Var]:
        new_scope: Dict[str, Var] = {}
        self.scopes.append(new_scope)

        vars: List[Var] = []

        for var_name, raw_var_type in quantified_vars:
            var_type = VariableType.from_smt_type_string(raw_var_type)
            var = Var(id=self.next_var_id)
            new_scope[var_name] = var
            self.var_table[var] = VarInfo(name=var_name, type=var_type)
            self.next_var_id += 1

            vars.append(var)

        return vars

    def unwind_quantifier(self):
        """ None of the quantified variables was used in the subformula. """
        scope = self.scopes.pop(-1)
        self.next_var_id = min(scope.values()).id


    def exit_quantifier(self):
        self.scopes.pop(-1)


    def lookup_var_name(self, var_name: str) -> Var:
        for scope in reversed(self.scopes):
            if var_name in scope:
                return scope[var_name]

        raise ValueError(f'Variable has not been declared previously: {var_name}')


    def put_var_into_current_scope(self, var_name: str, raw_var_type: str = 'Int') -> Var:
        current_scope = self.scopes[-1]
        if var_name in current_scope:
            raise ValueError(f'Naming conflict - trying to insert a variable {var_name} into a scope that already contains that name')
        var_type = VariableType.from_smt_type_string(raw_var_type)
        var = Var(id=self.next_var_id)
        self.next_var_id += 1
        current_scope[var_name] = var
        self.var_table[var] = VarInfo(name=var_name, type=var_type)
        return var


@dataclass(unsafe_hash=True)
class NonlinTermNode:
    """
    A node in the term dependency graph.

    @Design: Currently we are replacing the placeholders whenever we see a variable being quantified.
             It might save some time to replace all placeholder variables at once when
             the tree is constructed.
    """

    body: NonlinTerm = field(hash=True)
    """ The body of the nonlinear term that is being replaced, e.g., (MOD <BODY>)"""

    was_dropped: bool = field(hash=False, default=False)
    """ Was an existential quantifier with the introduced variables added into the tree? """

    div_rewrite_var: Optional[Var] = field(default=None, hash=False)
    """ Placeholder variable to replace (div x D) with. """

    mod_rewrite_var: Optional[Var] = field(default=None, hash=False)
    """ Placeholder variable to replace (mod x M) with. """

    dependent_terms: Set[NonlinTermNode] = field(default_factory=set, hash=False)
    """ Nonlinear terms in the graph that contain a linear expression replacing a non-linear term represented by this node. """


def make_node_for_two_variable_rewrite(term: NonlinTerm, rewrite_id: int, scoper: Scoper) -> NonlinTermNode:
    """
    Create a node describing rewrite of the given term using two new variables (quotient and reminder).

    Div term is rewritten as:
        x - (y div D) = 0   --->   x - <QUOTIENT> && 0 <= <REMINDER> && <REMINDER> <= M-1 && y - D*<QUOTIENT> = <REMINDER>
    Mod term is rewritten as:
        x - (y mod D) = 0   --->   x - <REMINDER> && 0 <= <REMINDER> && <REMINDER> <= M-1 && y - D*<QUOTIENT> = <REMINDER>
    """
    quotient = scoper.put_var_into_current_scope(f'D{rewrite_id}')
    reminder = scoper.put_var_into_current_scope(f'M{rewrite_id}')
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


def make_node_for_single_variable_rewrite(term: NonlinTerm, rewrite_id: int, scoper: Scoper) -> NonlinTermNode:
    """
    Create a node describing rewrite of the given term using a single new variable (quotient).

    Div term is rewritten as:
        x - (y div M) = 0   --->   x - <QUOTIENT> && 0 <= (y - M*<QUOTIENT>) && (y - M*<QUOTIENT>) <= M-1
    Mod term is rewritten as:
        x - (y mod M) = 0   --->   x - (y - M*<QUOTIENT>) && 0 <= (y - M*<QUOTIENT>) && (y - M*<QUOTIENT>) <= M-1
    """
    quotient = scoper.put_var_into_current_scope(f'D{rewrite_id}')
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
    index: Dict[Var, List[NonlinTermNode]] = field(default_factory=lambda: defaultdict(list))
    term_nodes: Dict[NonlinTerm, NonlinTermNode] = field(default_factory=dict)
    graph_roots: Set[NonlinTermNode] = field(default_factory=set)
    seen_term_cnt: int = 0

    def make_term_known(self, term: NonlinTerm, scoper: Scoper) -> NonlinTermNode:
        node = self.term_nodes.get(term)
        target_field = 'mod_rewrite_var' if term.type == NonlinTermType.MOD else 'div_rewrite_var'
        if node:
            placeholder_var = getattr(node, target_field)
            if getattr(node, target_field):
                return self.term_nodes[term]

        nonlin_var_id = self.seen_term_cnt
        self.seen_term_cnt += 1
        placeholder_var_name = f'quotient_{nonlin_var_id}' if term.type == NonlinTermType.DIV else f'reminder_{nonlin_var_id}'
        placeholder_var = scoper.put_var_into_current_scope(placeholder_var_name)

        if not node:
            node = NonlinTermNode(body=term, was_dropped=False)
            self.term_nodes[term] = node

        setattr(node, target_field, placeholder_var)
        return node

    def make_node_root(self, node: NonlinTermNode):
        if node in self.graph_roots:
            return

        self.graph_roots.add(node)
        for var, _ in node.body.lin_terms:
            self.index[var].append(node)

    def drop_nodes_for_var(self, var: Var) -> List[NonlinTermNode]:
        work_list = list(self.index[var])

        dropped_nodes = list(work_list)
        while work_list:
            node = work_list.pop(-1)

            if node.was_dropped:
                # In case the root node is dependent on multiple variables quantified on the same level
                # the node might already be dropped
                continue

            node.was_dropped = True
            for dependent_node in node.dependent_terms:
                if not dependent_node.was_dropped:
                    dependent_node.was_dropped = True
                    work_list.append(dependent_node)
                    dropped_nodes.append(dependent_node)

        return dropped_nodes


@dataclass
class Expr:
    """A linear arithmetical expression of the form c_1*a_1 + c_2*a_2 + K"""
    constant_term: int = 0
    linear_terms: Dict[Var, int] = field(default_factory=dict)

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
    used_vars: Set[Var] = field(default_factory=set)


def normalize_expr(ast: Raw_AST,
                   nonlinear_term_graph: NonlinTermGraph,
                   scoper: Scoper) -> Tuple[Expr, Set[NonlinTermNode], Set[Var]]:
    if isinstance(ast, (str, int)):
        try:
            int_val = int(ast)
            return Expr(constant_term=int_val), set(), set()
        except ValueError:
            assert isinstance(ast, str)
            var = scoper.lookup_var_name(ast)
            return Expr(linear_terms={var: 1}), set(), {var}

    assert isinstance(ast, list)
    node_type = ast[0]

    expr_reductions = {'*': Expr.__mul__, '-': Expr.__sub__, '+': Expr.__add__}  # all are left-associative

    if len(ast) > 2 and node_type in expr_reductions:
        reduction = expr_reductions[node_type]
        left, dependent_terms, support = normalize_expr(ast[1], nonlinear_term_graph, scoper)
        for operand_ast in ast[2:]:
            operand, dependent_term, other_support = normalize_expr(operand_ast, nonlinear_term_graph, scoper)
            dependent_terms.update(dependent_term)
            support.update(other_support)
            left = reduction(left, operand)
        return left, dependent_terms, support
    elif len(ast) == 2 and node_type == '-':
        operand, dependent_terms, support = normalize_expr(ast[1], nonlinear_term_graph, scoper)
        return -operand, dependent_terms, support
    elif node_type in {'mod', 'div'}:
        lin_term, dependent_terms, support = normalize_expr(ast[1], nonlinear_term_graph, scoper)
        nonlin_constant, _, _ = normalize_expr(ast[2], nonlinear_term_graph, scoper)
        lin_terms = tuple(sorted(lin_term.linear_terms.items(), key=lambda var_coef_pair: var_coef_pair[0]))
        term_body = NonlinTerm(lin_terms=lin_terms, lin_term_constant=lin_term.constant_term,
                               type=NonlinTermType(node_type), nonlin_constant=nonlin_constant.constant_term)

        term_node = nonlinear_term_graph.make_term_known(term_body, scoper)

        for dep_term in dependent_terms:
            dep_term.dependent_terms.add(term_node)

        placeholder_var = term_node.div_rewrite_var if node_type == 'div' else term_node.mod_rewrite_var
        assert placeholder_var
        expr = Expr(linear_terms={placeholder_var: 1})

        if not dependent_terms:
            nonlinear_term_graph.make_node_root(term_node)

        support.add(placeholder_var)
        return expr, {term_node}, support

    raise ValueError(f'Cannot reduce unknown expression to evaluable form. {ast=}')


def convert_relation_to_evaluable_form(ast: Raw_AST, dep_graph: NonlinTermGraph, scoper: Scoper) -> Tuple[Union[Relation, BoolLiteral], ASTInfo]:
    assert isinstance(ast, list)
    predicate_symbol = ast[0]
    if not isinstance(predicate_symbol, str):
        raise ValueError(f'Cannot construct equation for predicate symbol that is not a string: {predicate_symbol=}')

    lhs, _, lhs_support = normalize_expr(ast[1], dep_graph, scoper)  # Will remove nonlinear terms and replace them with new variables
    rhs, _, rhs_support = normalize_expr(ast[2], dep_graph, scoper)
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


def split_lin_terms_into_vars_and_coefs(terms: Iterable[LinTerm]) -> Tuple[List[Var], List[int]]:
    vars: List[Var] = []
    coefs: List[int] = []
    for term in terms:
        coefs.append(term.coef)
        vars.append(term.var)
    return vars, coefs


def is_any_member_if_str(container, elem1, elem2):
    return (isinstance(elem1, str) and elem1 in container) or (isinstance(elem2, str) and elem2 in container)


def is_any_node_of_type(types: Iterable[str], node1, node2):
    is_node1 = isinstance(node1, list) and node1[0] in types
    is_node2 = isinstance(node2, list) and node2[0] in types
    return is_node1 or is_node2


@dataclass
class RewriteInstructions:
    placeholder_replacements: Dict[Var, Tuple[LinTerm, ...]] = field(default_factory=dict)
    new_atoms: List[AST_Atom] = field(default_factory=list)
    vars_to_quantify: List[Var] = field(default_factory=list)


def add_two_var_rewrite_instructions(rewrite_instructions: RewriteInstructions, node: NonlinTermNode, reminder: Var, quotient: Var):
    rewrite_instructions.placeholder_replacements[reminder] = (LinTerm(coef=1, var=reminder),)
    rewrite_instructions.placeholder_replacements[quotient] = (LinTerm(coef=1, var=quotient),)

    greater_than_zero = Relation(vars=[reminder], coefs=[-1], rhs=0, predicate_symbol='<=')
    smaller_than_modulus = Relation(vars=[reminder], coefs=[1], rhs=node.body.nonlin_constant-1, predicate_symbol='<=')

    # <TERM_BODY> = <QUOTIENT>*<NONLIN_CONSTANT> + <REMINDER> -->  <TERM_BODY> - <QUOTIENT>*<NONLIN_CONSTANT> - <REMINDER> = 0
    terms = tuple(LinTerm(coef=item[1], var=item[0]) for item in node.body.lin_terms)
    terms += (LinTerm(coef=-1, var=reminder), LinTerm(coef=-node.body.nonlin_constant, var=quotient))
    terms = sorted(terms, key=lambda term: term.var)
    vars, coefs = split_lin_terms_into_vars_and_coefs(terms)

    body_decomposition = Relation(vars=vars, coefs=coefs, rhs=-node.body.lin_term_constant, predicate_symbol='=')

    rewrite_instructions.new_atoms.extend((greater_than_zero, smaller_than_modulus, body_decomposition))


def add_quotient_single_variable_rewrite_instructions(rewrite_instructions: RewriteInstructions, node: NonlinTermNode, quotient: Var):
    rewrite_instructions.placeholder_replacements[quotient] = (LinTerm(coef=1, var=quotient),)

    # Make   0 <= <BODY> - <QUOTIENT>*<NONLIN_TERM_BODY>
    terms = tuple(LinTerm(coef=item[1], var=item[0]) for item in node.body.lin_terms)
    terms += (LinTerm(coef=-node.body.nonlin_constant, var=quotient),)
    terms = sorted(terms, key=lambda term: term.var)
    vars, coefs = split_lin_terms_into_vars_and_coefs(terms)

    # <BODY> + <BODY_CONSTANT> - N*<QUOTIENT> <= 0
    # <BODY> - N*<QUOTIENT> <= -<BODY_CONSTANT>
    # -(<BODY> - N*<QUOTIENT>) >= +<BODY_CONSTANT>
    negated_coefs = [-1*coef for coef in coefs]
    greater_than_zero = Relation(vars=vars, coefs=negated_coefs, rhs=node.body.lin_term_constant, predicate_symbol='<=')

    smaller_than_modulus = Relation(vars=vars, coefs=coefs, rhs=(node.body.nonlin_constant-1-node.body.lin_term_constant), predicate_symbol='<=')

    rewrite_instructions.new_atoms.extend([greater_than_zero, smaller_than_modulus])


def add_reminder_single_variable_rewrite_using_quotient(rewrite_instructions: RewriteInstructions, node: NonlinTermNode, quotient: Var):
    # Express reminder as <BODY> - <QUOTIENT>*N
    terms = tuple(LinTerm(coef=item[1], var=item[0]) for item in node.body.lin_terms)
    terms += (LinTerm(coef=-node.body.nonlin_constant, var=quotient),)
    terms = tuple(sorted(terms, key=lambda term: term.var))
    vars, coefs = split_lin_terms_into_vars_and_coefs(terms)

    rewrite_instructions.placeholder_replacements[quotient] = terms

    # <BODY> + <BODY_CONSTANT> - N*<QUOTIENT> >= 0
    # <BODY> - N*<QUOTIENT> >= -<BODY_CONSTANT>
    # -(<BODY> - N*<QUOTIENT>) <= +<BODY_CONSTANT>
    negated_coefs = [-1*coef for coef in coefs]
    greater_than_zero = Relation(vars=vars, coefs=negated_coefs, rhs=node.body.lin_term_constant, predicate_symbol='<=')

    # <BODY> + <BODY_CONSTANT> - N*<QUOTIENT> <= N-1
    # <BODY> - N*<QUOTIENT> <= N - 1 - <BODY_CONSTANT>
    smaller_than_modulus = Relation(vars=vars, coefs=coefs, rhs=(node.body.nonlin_constant-1-node.body.lin_term_constant), predicate_symbol='<=')

    rewrite_instructions.new_atoms.extend([greater_than_zero, smaller_than_modulus])


def add_reminder_single_variable_rewrite_using_congruence(rewrite_instructions: RewriteInstructions, node: NonlinTermNode, reminder: Var):
    rewrite_instructions.placeholder_replacements[reminder] = (LinTerm(coef=1, var=reminder),)

    greater_than_zero = Relation(vars=[reminder], coefs=[-1], rhs=0, predicate_symbol='<=')
    smaller_than_modulus = Relation(vars=[reminder], coefs=[1], rhs=node.body.nonlin_constant-1, predicate_symbol='<=')

    terms = tuple(LinTerm(coef=item[1], var=item[0]) for item in node.body.lin_terms)
    terms += (LinTerm(coef=-1, var=reminder),)
    terms = sorted(terms, key=lambda term: term.var)
    vars, coefs = split_lin_terms_into_vars_and_coefs(terms)

    # <BODY> + <BODY_CONSTANT> - <REMINDER> ~~ 0
    # <BODY> - <REMINER> ~~ -BODY_CONSTANT
    modulus = node.body.nonlin_constant
    rhs = (-node.body.lin_term_constant) % modulus
    assert 0 <= rhs and rhs < modulus
    congruence = Congruence(vars=vars, coefs=coefs, rhs=rhs, modulus=node.body.nonlin_constant)

    rewrite_instructions.new_atoms.extend([greater_than_zero, smaller_than_modulus, congruence])


def determine_how_to_rewrite_dropped_terms(dropped_nodes: Iterable[NonlinTermNode], scoper: Scoper) -> RewriteInstructions:
    rewrite_instructions = RewriteInstructions()

    for node in dropped_nodes:
        if node.div_rewrite_var is not None and node.mod_rewrite_var is not None:
            # Reuse placeholder variables
            reminder, quotient = node.mod_rewrite_var, node.div_rewrite_var
            add_two_var_rewrite_instructions(rewrite_instructions, node, reminder=reminder, quotient=quotient)

            rewrite_instructions.vars_to_quantify.extend((reminder, quotient))

        elif node.div_rewrite_var is not None:
            quotient = node.div_rewrite_var
            rewrite_instructions.vars_to_quantify.append(quotient)

            if solver_config.preprocessing.use_two_vars_when_rewriting_nonlin_terms:
                reminder = scoper.put_var_into_current_scope('dummy_reminder')  # Make a new var
                add_two_var_rewrite_instructions(rewrite_instructions, node, reminder=reminder, quotient=quotient)
                rewrite_instructions.vars_to_quantify.append(reminder)
                continue

            add_quotient_single_variable_rewrite_instructions(rewrite_instructions, node, quotient=quotient)

        elif node.mod_rewrite_var is not None:
            reminder = node.mod_rewrite_var
            rewrite_instructions.vars_to_quantify.append(reminder)

            if solver_config.preprocessing.use_two_vars_when_rewriting_nonlin_terms:
                quotient = scoper.put_var_into_current_scope('dummy_quotient')  # Make a new var
                add_two_var_rewrite_instructions(rewrite_instructions, node, reminder=reminder, quotient=quotient)
                rewrite_instructions.vars_to_quantify.append(quotient)
                continue

            if solver_config.preprocessing.use_congruences_when_rewriting_modulo:
                add_reminder_single_variable_rewrite_using_congruence(rewrite_instructions, node, reminder=reminder)
                continue

            add_reminder_single_variable_rewrite_using_quotient(rewrite_instructions, node, reminder)  # Use the variable as congruence
            rewrite_instructions.vars_to_quantify.append(reminder)

    return rewrite_instructions


def apply_substitution(vars: Iterable[Var], coefs: Iterable[int], substitution: Dict[Var, Tuple[LinTerm, ...]]) -> Tuple[List[Var], List[int]]:
    lin_term_after_substitution: List[LinTerm] = []
    for var, coef in zip(vars, coefs):
        if var in substitution:
            lin_term_after_substitution.extend(LinTerm(var=subs_term.var, coef=subs_term.coef*coef) for subs_term in substitution[var])
            continue
        lin_term_after_substitution.append(LinTerm(var=var, coef=coef))

    new_lin_term: Dict[Var, int] = defaultdict(lambda: 0)
    for term in lin_term_after_substitution:
        new_lin_term[term.var] += term.coef

    sorted_term = sorted(new_lin_term.items(), key=lambda item: item[0])

    new_vars: Tuple[Var] = tuple()
    new_coefs: Tuple[int] = tuple()
    new_vars, new_coefs = zip(*sorted_term)  # type: ignore

    return (list(new_vars), list(new_coefs))


def _replace_placeholders_by_equivalent_lin_terms(ast: AST_Node, rewrite_instructions: RewriteInstructions) -> AST_Node:
    if isinstance(ast, Relation):
        new_vars, new_coefs = apply_substitution(ast.vars, ast.coefs, rewrite_instructions.placeholder_replacements)
        return Relation(vars=new_vars, coefs=new_coefs, rhs=ast.rhs, predicate_symbol=ast.predicate_symbol)

    if isinstance(ast, Congruence):
        new_vars, new_coefs = apply_substitution(ast.vars, ast.coefs, rewrite_instructions.placeholder_replacements)
        return Congruence(vars=new_vars, coefs=new_coefs, rhs=ast.rhs, modulus=ast.modulus)

    if isinstance(ast, (str, BoolLiteral, Var)):
        return ast

    assert isinstance(ast, list)

    node_type = ast[0]
    if node_type == AST_Node_Names.EXISTS.value:
        child = _replace_placeholders_by_equivalent_lin_terms(ast[2], rewrite_instructions)
        return [AST_Node_Names.EXISTS.value, ast[1], child]

    children = (_replace_placeholders_by_equivalent_lin_terms(child, rewrite_instructions) for child in ast[1:])
    return [node_type, *children]


def _convert_ast_into_evaluable_form(ast: Raw_AST,
                                     dep_graph: NonlinTermGraph,
                                     bool_vars: Set[str],
                                     scoper: Scoper) -> Tuple[AST_Node, ASTInfo]:
    if isinstance(ast, str):
        var = scoper.lookup_var_name(ast)
        return var, ASTInfo(used_vars={var})

    if isinstance(ast, BoolLiteral):
        return ast, ASTInfo(used_vars=set())

    assert isinstance(ast, list), f'Freestanding integer found - not a part of any atom: {ast}'
    node_type = ast[0]
    assert isinstance(node_type, str)

    if node_type in {'and', 'or'}:
        new_node: AST_Node = [node_type]
        tree_info = ASTInfo()
        for child in ast[1:]:
            new_child, child_tree_info = _convert_ast_into_evaluable_form(child, dep_graph, bool_vars, scoper)
            new_node.append(new_child)
            tree_info.used_vars.update(child_tree_info.used_vars)
        return new_node, tree_info

    if node_type == 'not':
        child, child_ast_info = _convert_ast_into_evaluable_form(ast[1], dep_graph, bool_vars, scoper)
        if isinstance(child, BoolLiteral):
            return BoolLiteral(value=not child.value), child_ast_info
        return ['not', child], child_ast_info

    if node_type == 'exists':
        new_node: AST_Node = [node_type]

        raw_quantifier_list: List[Tuple[str, str]] = ast[1]  # type: ignore
        quantifier_list = scoper.enter_quantifier(raw_quantifier_list)

        child, child_ast_info = _convert_ast_into_evaluable_form(ast[2], dep_graph, bool_vars, scoper)

        bound_vars: List[Var] = [var for var in quantifier_list if var in child_ast_info.used_vars]
        if not bound_vars:
            # The underlying AST could be x = x, which would be reduced to BoolLiteral(True).
            # Remove the quantifier all together
            scoper.unwind_quantifier()
            return child, child_ast_info

        new_node.append(bound_vars)  # type: ignore

        # Child's AST Info will represent this node - remove all currently bound variables
        child_ast_info.used_vars = child_ast_info.used_vars.difference(bound_vars)

        # Try dropping any of the bound vars - collect nonlinear terms (graph nodes) that have to be instantiated
        dropped_nodes: List[NonlinTermNode] = []

        for var in bound_vars:
            dropped_nodes += dep_graph.drop_nodes_for_var(var)

        rewrite_instructions = determine_how_to_rewrite_dropped_terms(dropped_nodes, scoper)

        new_atoms = rewrite_instructions.new_atoms

        if dropped_nodes:
            if isinstance(child, list) and child[0] == 'and':
                child += new_atoms
            else:
                child = ['and', child] + new_atoms

            new_node[1] += rewrite_instructions.vars_to_quantify  # type: ignore
        new_node.append(child)

        scoper.exit_quantifier()

        return new_node, child_ast_info

    if node_type == '=':
        connectives = {'and', 'or', 'not', 'exists', 'forall'}

        if is_any_member_if_str(bool_vars, ast[1], ast[2]) or is_any_node_of_type(connectives, ast[1], ast[2]):
            lhs, lhs_info = _convert_ast_into_evaluable_form(ast[1], dep_graph, bool_vars, scoper)
            rhs, rhs_info = _convert_ast_into_evaluable_form(ast[2], dep_graph, bool_vars, scoper)
            lhs_info.used_vars.update(rhs_info.used_vars)
            return ['=', lhs, rhs], lhs_info
        lia_symbols = {'+', '-', '*', 'mod', 'div'}
        if is_any_node_of_type(lia_symbols, ast[1], ast[2]):
            return convert_relation_to_evaluable_form(ast, dep_graph, scoper)

        logger.info('Not sure whether %s is a Boolean equivalence or an atom, reducing to atom.', ast)
        return convert_relation_to_evaluable_form(ast, dep_graph, scoper)

    if node_type in ['<=', '<', '>', '>=']:
        return convert_relation_to_evaluable_form(ast, dep_graph, scoper)

    raise ValueError(f'Cannot traverse trough {node_type=} while converting AST into evaluable form. {ast=}')


def convert_ast_into_evaluable_form(ast: Raw_AST, global_symbols: Iterable[FunctionSymbol]) -> Tuple[AST_Node, Dict[Var, VarInfo]]:
    dep_graph = NonlinTermGraph()

    bool_vars = {sym.name for sym in global_symbols if sym.return_type == VariableType.BOOL}
    global_syms = [(sym.name, sym.return_type) for sym in global_symbols]
    scoper = Scoper(global_syms)

    new_ast, new_ast_info = _convert_ast_into_evaluable_form(ast, dep_graph, bool_vars, scoper)

    # There might be non-linear terms still not rewritten, e.g., if the lin. term inside the modulo term
    # depends on global symbols
    vars_with_undropped_nodes = [
        var for var, root_nodes in dep_graph.index.items() if any(not node.was_dropped for node in root_nodes)
    ]

    if not vars_with_undropped_nodes:
        return new_ast, scoper.var_table

    dropped_nodes = []
    for var in vars_with_undropped_nodes:
        dropped_nodes += dep_graph.drop_nodes_for_var(var)

    assert dropped_nodes

    rewrite_instructions = determine_how_to_rewrite_dropped_terms(dropped_nodes, scoper)
    new_atoms = rewrite_instructions.new_atoms

    new_ast = ['exists', rewrite_instructions.vars_to_quantify, ['and', new_ast, *rewrite_instructions.new_atoms]]  # type: ignore
    return new_ast, scoper.var_table
