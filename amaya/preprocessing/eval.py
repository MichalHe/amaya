from __future__ import annotations
from collections import defaultdict
from collections.abc import Iterable
from dataclasses import dataclass, field
from enum import Enum
import itertools
import math
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
    comment: Optional[str] = None


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


    def put_var_into_current_scope(self, var_name: str, raw_var_type: str = 'Int', add_id_to_name: bool = False) -> Var:
        current_scope = self.scopes[-1]

        var_id = self.next_var_id

        if add_id_to_name:
            var_name = f'{var_name}{var_id}'

        if var_name in current_scope:
            raise ValueError(f'Naming conflict - trying to insert a variable {var_name} into a scope that already contains that name')

        var_type = VariableType.from_smt_type_string(raw_var_type)
        var = Var(id=var_id)
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
        work_list = list(node for node in self.index[var] if not node.was_dropped)

        dropped_nodes = list(work_list)
        while work_list:
            node = work_list.pop(-1)

            # @Problematic: WTF?
            # if node.was_dropped:
            #     # In case the root node is dependent on multiple variables quantified on the same level
            #     # the node might already be dropped
            #     continue

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

        constant_term = lin_term.constant_term
        if node_type == 'mod':
            # Normalize the offset into [0, M-1]
            constant_term = (lin_term.constant_term % nonlin_constant.constant_term)

        term_body = NonlinTerm(lin_terms=lin_terms, lin_term_constant=constant_term,
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


def divide_relation_by_gcd(relation: Relation) -> Union[Relation, BoolLiteral]:
    # Divide both sides by GCD if configured
    if not solver_config.optimizations.do_gcd_divide:
        return relation

    gcd = math.gcd(*relation.coefs)
    new_coefs: List[int] = [coef // gcd for coef in relation.coefs]
    unsat = False
    if relation.predicate_symbol == '<=':
        new_rhs = math.floor(relation.rhs/gcd)
    else:  # Equation
        if relation.rhs % gcd:
            unsat = True
        new_rhs = relation.rhs // gcd

    if unsat:
        msg = 'GCD of relation coefs (%s) is %d, but RHS (=%d) is not divisible -> returning False.'
        logger.info(msg, relation.coefs, gcd, relation.rhs)
        return BoolLiteral(False)

    msg = 'GCD of relation coefs (%s) is %d, rewriting coefficients into %s and RHS into %d.'
    logger.info(msg, relation.coefs, gcd, new_coefs, new_rhs)
    return Relation(vars=relation.vars, coefs=new_coefs, rhs=new_rhs, predicate_symbol=relation.predicate_symbol)


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

    relation = Relation(vars=vars, coefs=coefs, rhs=abs_part, predicate_symbol=predicate_symbol)
    # We cannot do GCD rewrite as the relation will be modified later (contains placeholder variables)

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
    new_formulae: List[AST_Node] = field(default_factory=list)
    vars_to_quantify: List[Var] = field(default_factory=list)


def add_two_var_rewrite_instructions(rewrite_instructions: RewriteInstructions, node: NonlinTermNode, reminder: Var, quotient: Var):
    rewrite_instructions.placeholder_replacements[reminder] = (LinTerm(coef=1, var=reminder),)
    rewrite_instructions.placeholder_replacements[quotient] = (LinTerm(coef=1, var=quotient),)

    greater_than_zero = Relation(vars=[reminder], coefs=[-1], rhs=0, predicate_symbol='<=')
    smaller_than_modulus = Relation(vars=[reminder], coefs=[1], rhs=abs(node.body.nonlin_constant)-1, predicate_symbol='<=')

    # <TERM_BODY> = <QUOTIENT>*<NONLIN_CONSTANT> + <REMINDER> -->  <TERM_BODY> - <QUOTIENT>*<NONLIN_CONSTANT> - <REMINDER> = 0
    terms = tuple(LinTerm(coef=item[1], var=item[0]) for item in node.body.lin_terms)
    terms += (LinTerm(coef=-1, var=reminder), LinTerm(coef=-node.body.nonlin_constant, var=quotient))
    terms = sorted(terms, key=lambda term: term.var)
    vars, coefs = split_lin_terms_into_vars_and_coefs(terms)

    body_decomposition = Relation(vars=vars, coefs=coefs, rhs=-node.body.lin_term_constant, predicate_symbol='=')

    rewrite_instructions.new_formulae.extend((greater_than_zero, smaller_than_modulus, body_decomposition))


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

    rhs = abs(node.body.nonlin_constant) - 1 - node.body.lin_term_constant
    smaller_than_modulus = Relation(vars=vars, coefs=coefs, rhs=rhs, predicate_symbol='<=')

    rewrite_instructions.new_formulae.extend([greater_than_zero, smaller_than_modulus])


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
    rhs = abs(node.body.nonlin_constant) - 1 - node.body.lin_term_constant
    smaller_than_modulus = Relation(vars=vars, coefs=coefs, rhs=rhs, predicate_symbol='<=')

    rewrite_instructions.new_formulae.extend([greater_than_zero, smaller_than_modulus])


def add_reminder_single_variable_rewrite_using_congruence(rewrite_instructions: RewriteInstructions, node: NonlinTermNode, reminder: Var):
    rewrite_instructions.placeholder_replacements[reminder] = (LinTerm(coef=1, var=reminder),)

    greater_than_zero = Relation(vars=[reminder], coefs=[-1], rhs=0, predicate_symbol='<=')
    smaller_than_modulus = Relation(vars=[reminder], coefs=[1], rhs=abs(node.body.nonlin_constant)-1, predicate_symbol='<=')

    terms = tuple(LinTerm(coef=item[1], var=item[0]) for item in node.body.lin_terms)
    terms += (LinTerm(coef=-1, var=reminder),)
    terms = sorted(terms, key=lambda term: term.var)
    vars, coefs = split_lin_terms_into_vars_and_coefs(terms)

    # <BODY> + <BODY_CONSTANT> - <REMINDER> ~~ 0
    # <BODY> - <REMINER> ~~ -BODY_CONSTANT

    # @Note: It is OK to take an absolute value of the modulus here since we know that were only mod terms and no
    #        div terms with the same modulo. Moreover, it is required for correct restriction of the reminder,
    #        as the reminder needs to be 0 <= reminder <= abs(modulus) - 1. Plus the mod automaton also
    #        requires a positive modulus.
    modulus = abs(node.body.nonlin_constant)

    rhs = (-node.body.lin_term_constant) % modulus
    assert 0 <= rhs and rhs < modulus, f'rhs: {rhs=} {modulus=}'
    congruence = Congruence(vars=vars, coefs=coefs, rhs=rhs, modulus=abs(node.body.nonlin_constant))

    rewrite_instructions.new_formulae.extend([greater_than_zero, smaller_than_modulus, congruence])


def rewrite_reminder_using_linearization(emitted_reminder_with_offset: Tuple[Var, int], node: NonlinTermNode, rewrite_instructions: RewriteInstructions):
    """
    Linearize mod terms sharing the same linear terms and modulus.

    If there are two terms (mod (+ x k1) M) and (mod (+ x k2) M) with the same linear terms in the body
    and same modulus, but different offsets then we can express the second modulus as the first
    one + offset (linearization).

    Params:
        - emitted_reminder_with_offset: A mod-var that has already been emitted together with its k1
        - node: A node capturing the (mod (+ x k2) M)
        - rewrite_instructions: Instructions to put the linearization formulae into.
    """
    emitted_var, emitted_var_offset = emitted_reminder_with_offset

    # both Emitted and New are in [0, M-1] and we have   E + E_offset ~= N + N_offset
    assert node.mod_rewrite_var
    new_var: Var = node.mod_rewrite_var
    new_var_offset = (-node.body.lin_term_constant) % node.body.nonlin_constant

    # combine offset into total offset: N ~= E + (E_offset - N_offset)
    total_offset = (-emitted_var_offset + new_var_offset) % node.body.nonlin_constant

    # we have N = f(E) = E + total_offset, but due to congruence there is a nonlinear jump - find the spot where to create disjunction
    zero_point = node.body.nonlin_constant - total_offset

    def fn_case(low: int, high: int, fn_dependence: Relation):
        if low == high:
            eq = Relation(vars=[emitted_var], coefs=[1], rhs=low, predicate_symbol='=')
            return ['and', eq, fn_dependence]
        low_bound  = Relation(vars=[emitted_var], coefs=[-1], rhs=-low, predicate_symbol='<=')
        high_bound = Relation(vars=[emitted_var], coefs=[1], rhs=high, predicate_symbol='<=')
        return ['and', low_bound, high_bound, fn_dependence]

    def fn_case_for_fixed_value(val: int):
        emitted_var_val = Relation(vars=[emitted_var], coefs=[1], rhs=val, predicate_symbol='=')
        new_var_rhs     = (val+total_offset) % node.body.nonlin_constant
        new_var_val     = Relation(vars=[new_var], coefs=[1], rhs=new_var_rhs, predicate_symbol='=')
        return ['and', emitted_var_val, new_var_val]

    modulus = node.body.nonlin_constant
    fn_terms = sorted([(emitted_var, 1), (new_var, -1)], key=lambda it: it[0])
    fn_vars  = [it[0] for it in fn_terms]
    fn_coefs = [it[1] for it in fn_terms]
    fn         = Relation(vars=fn_vars, coefs=fn_coefs, rhs=total_offset, predicate_symbol='=')
    shifted_fn = Relation(vars=fn_vars, coefs=fn_coefs, rhs=total_offset-modulus, predicate_symbol='=')

    left_interval = (0, zero_point-1)
    right_interval = (zero_point, modulus-1)

    if left_interval[0] == left_interval[1]:
        result_fn = ['or', fn_case_for_fixed_value(left_interval[0]), fn_case(right_interval[0], right_interval[1], shifted_fn)]
    elif right_interval[0] == right_interval[1]:
        result_fn = ['or', fn_case(left_interval[0], left_interval[1], fn), fn_case_for_fixed_value(right_interval[0])]
    else:
        result_fn = ['or', fn_case(0, zero_point-1, fn), fn_case(zero_point, modulus-1, shifted_fn)]

    rewrite_instructions.new_formulae.append(result_fn)
    rewrite_instructions.vars_to_quantify.append(new_var)

    lower_bound = Relation(vars=[new_var], coefs=[-1], rhs=0, predicate_symbol='<=')
    upper_bound = Relation(vars=[new_var], coefs=[1], rhs=modulus-1, predicate_symbol='<=')
    rewrite_instructions.new_formulae.append(['and', lower_bound, upper_bound])


def determine_how_to_rewrite_dropped_terms(dropped_nodes: Iterable[NonlinTermNode], scoper: Scoper) -> RewriteInstructions:
    rewrite_instructions = RewriteInstructions()

    # If there are multiple reminders with the same body nonlin term, but different absolute part, e.g.
    # (mod x 5) and (mod (x + 1) 5), then it is sufficient to synthetise only one constraint, because
    #    (mod x 5)       -->       x ~= x_0 (mod 5) && 0 <= x_0 <= 4
    #    (mod (x + 1) 5) --> (x + 1) ~= x_1 (mod 5) && 0 <= x_1 <= 4
    # Or equivalently:
    #    (mod (x + 1) 5) -->       x ~= x_1 + 4 (mod 5) && 0 <= x_1 <= 4
    # But then
    #    x = x_0 + 5k_0
    #    x = x_1 + 5k_1 + 4
    # So
    #    x_0 ~= x_1 + 4  (mod 5)   <=>  x_0 + 1 = x_1
    # As both reminders are in [0, 4] we can linearize
    # x_1 = f(x_0) = x_1 + 1
    # f([0,4]) = [1,4] + [0]  (we have to do a linearization split)
    NonlinTermWithoutAbs = Tuple[Tuple[Tuple[Var, int], ...], int]
    VarWithOffset = Tuple[Var, int]  # To represent RHS of the already introduced congruence
    nonlin_mod_terms_emitted: Dict[NonlinTermWithoutAbs, VarWithOffset] = {}

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
                reminder = scoper.put_var_into_current_scope('dummy_reminder', add_id_to_name=True)  # Make a new var
                add_two_var_rewrite_instructions(rewrite_instructions, node, reminder=reminder, quotient=quotient)
                rewrite_instructions.vars_to_quantify.append(reminder)
                continue

            add_quotient_single_variable_rewrite_instructions(rewrite_instructions, node, quotient=quotient)

        elif node.mod_rewrite_var is not None:
            term_without_abs = (node.body.lin_terms, node.body.nonlin_constant)
            if term_without_abs in nonlin_mod_terms_emitted and solver_config.optimizations.linearize_similar_mod_terms:
                # We have already a variable that captures (mod (<LinBody> + K) M), instead of dropping another congruence
                # we can just emit a linearized var for current node
                emitted_var_with_offset = nonlin_mod_terms_emitted[term_without_abs]
                rewrite_reminder_using_linearization(emitted_var_with_offset, node, rewrite_instructions)
                continue

            reminder = node.mod_rewrite_var

            rewrite_instructions.vars_to_quantify.append(reminder)

            # Store info in case there will be nonlinear terms that can be linearized
            offset = (-node.body.lin_term_constant % node.body.nonlin_constant)
            nonlin_mod_terms_emitted[term_without_abs] = (reminder, offset)

            if solver_config.preprocessing.use_two_vars_when_rewriting_nonlin_terms:
                quotient = scoper.put_var_into_current_scope('dummy_quotient', add_id_to_name=True)  # Make a new var
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

        new_atoms = rewrite_instructions.new_formulae

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
    new_atoms = rewrite_instructions.new_formulae

    new_ast = ['exists', rewrite_instructions.vars_to_quantify, ['and', new_ast, *rewrite_instructions.new_formulae]]  # type: ignore
    return new_ast, scoper.var_table
