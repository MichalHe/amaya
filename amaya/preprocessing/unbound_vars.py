from __future__ import annotations
from collections import defaultdict
from dataclasses import (
    dataclass,
    field
)
import functools
import math
import itertools
from math import gcd
from typing import (
    Any,
    Dict,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from amaya.relations_structures import (
    AST_Atom,
    AST_NaryNode,
    AST_Node,
    AST_Node_Names,
    BoolLiteral,
    Congruence,
    Relation,
    Var,
)

from amaya import logger


@dataclass
class Value_Interval:
    lower_limit: Optional[int] = None
    upper_limit: Optional[int] = None

    def __repr__(self) -> str:
        lower = self.lower_limit if self.lower_limit is not None else '-inf'
        upper = self.upper_limit if self.upper_limit is not None else '+inf'
        return f'<{lower}, {upper}>'


@dataclass
class AST_Internal_Node_With_Bounds_Info:
    node_type: str
    children: List[AST_Node_With_Bounds_Info]
    var_values: Dict[Var, List[Value_Interval]] = field(default_factory=lambda: defaultdict(lambda: [Value_Interval(None, None)]))


@dataclass
class AST_Quantifier_Node_With_Bounds_Info:
    node_type: str
    child: AST_Node_With_Bounds_Info
    bindings: List[Var]
    var_values: Dict[Var, List[Value_Interval]] = field(default_factory=lambda: defaultdict(lambda: [Value_Interval(None, None)]))


@dataclass
class AST_Leaf_Node_With_Bounds_Info:
    contents: Union[Relation, str, Congruence, Var, BoolLiteral]
    var_values: Dict[Var, List[Value_Interval]] = field(default_factory=lambda: defaultdict(lambda: [Value_Interval(None, None)]))


AST_Node_With_Bounds_Info = Union[AST_Leaf_Node_With_Bounds_Info, AST_Quantifier_Node_With_Bounds_Info, AST_Internal_Node_With_Bounds_Info]


def make_value_interval_intersection(left_intervals: List[Value_Interval], right_intervals: List[Value_Interval]):
    if not left_intervals or not right_intervals:
        return []

    def _max(a, b):
        if a is None:
            return b
        if b is None:
            return a
        return max(a, b)

    def _min(a, b):
        if a is None:
            return b
        if b is None:
            return a
        return min(a, b)

    result: List[Value_Interval] = []
    left_idx = 0
    right_idx = 0

    while left_idx < len(left_intervals) and right_idx < len(right_intervals):
        left = left_intervals[left_idx]
        right = right_intervals[right_idx]

        lower = _max(left.lower_limit, right.lower_limit)
        upper = _min(left.upper_limit, right.upper_limit)

        if upper == left.upper_limit:
            left_idx += 1
        else:
            right_idx += 1

        if lower is None or upper is None or lower <= upper:
            result.append(Value_Interval(lower, upper))

    return result


def make_value_interval_union(left_intervals: List[Value_Interval], right_intervals: List[Value_Interval]):
    if not left_intervals:
        return right_intervals
    if not right_intervals:
        return left_intervals

    def is_less(point_a, point_b):
        if point_a[0] is None:
            return -1 if point_a[1] == 's' else 1
        if point_b[0] is None:
            return 1 if point_b[1] == 's' else -1
        return -1 if point_a[0] < point_b[0] else 1

    points = []
    for interval in itertools.chain(left_intervals, right_intervals):
        points.append((interval.lower_limit, 's'))
        points.append((interval.upper_limit, 'e'))

    sorted_points = sorted(points, key=functools.cmp_to_key(is_less))

    start = None
    end = None
    resulting_intervals = []
    for point in sorted_points:
        if not start:
            start = point
            continue
        if not end:
            end = point
            continue

        if end[1] == point[1] or end[1] == 's':
            # Both are starts, or both are ends so we can safely add point to the current interval
            end = point
        else:
            resulting_intervals.append(Value_Interval(lower_limit=start[0], upper_limit=end[0]))
            start = point
            end = None

    resulting_intervals.append(Value_Interval(lower_limit=start[0], upper_limit=end[0]))

    # @Todo: Do interval coalesence
    return resulting_intervals


def make_value_interval_negation(intervals: List[Value_Interval]) -> List[Value_Interval]:
    if not intervals:
        return [Value_Interval(lower_limit=None, upper_limit=None)]

    result = []

    if intervals[0].lower_limit is not None:
        result.append(Value_Interval(lower_limit=None, upper_limit=intervals[0].lower_limit - 1))

    for i in range(len(intervals)-1):
        start = intervals[i].upper_limit + 1  # type: ignore
        end = intervals[i+1].lower_limit - 1  # type: ignore
        result.append(Value_Interval(lower_limit=start, upper_limit=end))

    if intervals[-1].upper_limit is not None:
        result.append(Value_Interval(lower_limit=intervals[-1].upper_limit + 1, upper_limit=None))

    return result


def perform_variable_bounds_analysis_on_ast(ast: AST_Node) -> AST_Node_With_Bounds_Info:
    if isinstance(ast, Relation):
        relation: Relation = ast
        bounds_info = AST_Leaf_Node_With_Bounds_Info(contents=relation)

        if len(relation.vars) == 1:
            var, coef = relation.vars[0], relation.coefs[0]
            bound = relation.rhs / coef

            if coef <= 0:
                bound = math.floor(bound)
            else:
                bound = math.ceil(bound)

            if relation.predicate_symbol == '=':
                bounds_info.var_values[var] = [Value_Interval(bound, bound)]
            elif relation.predicate_symbol == '<=':
                value_interval = Value_Interval()
                if coef > 0:
                    value_interval.upper_limit = bound
                else:
                    value_interval.lower_limit = bound
                bounds_info.var_values[var] = [value_interval]
        else:
            for var in relation.vars:
                bounds_info.var_values[var] = [Value_Interval(None, None)]
        return bounds_info

    elif isinstance(ast, (str, Congruence, BoolLiteral, Var)):
        return AST_Leaf_Node_With_Bounds_Info(contents=ast)

    node_type = ast[0]

    assert isinstance(node_type, str)

    if node_type in ('exists', 'forall'):
        subtree_bounds_info = perform_variable_bounds_analysis_on_ast(ast[2])

        quantified_vars: Set[Var] = set(ast[1])  # type: ignore
        var_values: Dict[Var, List[Value_Interval]] = {}
        for var, var_value_intervals in subtree_bounds_info.var_values.items():
            new_var_value_intervals = [Value_Interval(None, None)] if var in quantified_vars else var_value_intervals
            var_values[var] = new_var_value_intervals

        quantifier_node_with_bounds_info = AST_Quantifier_Node_With_Bounds_Info(node_type=node_type,
                                                                                child=subtree_bounds_info,
                                                                                bindings=ast[1],  # type: ignore
                                                                                var_values=var_values)
        return quantifier_node_with_bounds_info

    elif node_type == 'and':
        subtrees_with_bounds = [perform_variable_bounds_analysis_on_ast(subtree) for subtree in ast[1:]]

        overall_bounds_info = AST_Internal_Node_With_Bounds_Info(node_type=node_type, children=subtrees_with_bounds)
        for subtree_with_bounds in subtrees_with_bounds:
            for var, var_value_intervals in subtree_with_bounds.var_values.items():
                overall_bounds_info.var_values[var] = make_value_interval_intersection(overall_bounds_info.var_values[var],
                                                                                            var_value_intervals)

        return overall_bounds_info

    elif node_type == 'or':
        subtrees_with_bounds = [perform_variable_bounds_analysis_on_ast(subtree) for subtree in ast[1:]]

        overall_bounds_info = AST_Internal_Node_With_Bounds_Info(node_type=node_type, children=subtrees_with_bounds)
        for subtree_with_bounds in subtrees_with_bounds:
            for var, bounds_info in subtree_with_bounds.var_values.items():
                overall_bounds_info.var_values[var] = make_value_interval_union(overall_bounds_info.var_values[var],
                                                                                     bounds_info)

        return overall_bounds_info

    elif node_type == 'not':
        subtree_bounds_info = perform_variable_bounds_analysis_on_ast(ast[1])
        negated_var_values: Dict[Var, List[Value_Interval]] = {}

        if len(subtree_bounds_info.var_values) == 1:
            for var, bounds in subtree_bounds_info.var_values.items():
                negated_var_values[var] = make_value_interval_negation(bounds)
        else:
            negated_var_values = {var: [Value_Interval(None, None)] for var in subtree_bounds_info.var_values}

        return AST_Internal_Node_With_Bounds_Info(node_type=node_type,
                                                  children=[subtree_bounds_info],
                                                  var_values=negated_var_values)

    elif node_type == '=':  # Bool equivalence
        subtree_bounds_info = [perform_variable_bounds_analysis_on_ast(child) for child in ast[1:]]
        return AST_Internal_Node_With_Bounds_Info(node_type=node_type,
                                                  children=subtree_bounds_info)

    raise ValueError(f'[Variable bounds analysis] Cannot descend into AST - unknown node: {node_type=}, {ast=}')


def will_relation_be_always_satisfied_due_to_unbound_var(relation: Relation,
                                                         quantified_vars_with_bounds: Dict[str, Bounds_Info]
                                                         ) -> bool:
    # We know that the Relation can be always satisfied, and thus reduced to True if:
    # - it has the form of `ax + by ... >= C`, y has no upper bound and b > 0
    # - it has the form of `ax + by ... >= C`, y has no lower bound and b < 0
    # - it has the form of `ax + by ... <= C`, y has no lower bound and b > 0
    # - it has the form of `ax + by ... <= C`, y has no upper bound and b < 0
    for i, var in enumerate(relation.vars):
        if var not in quantified_vars_with_bounds:
            continue
        var_coef = relation.variable_coefficients[i]
        var_bounds = quantified_vars_with_bounds[var]

        if relation.predicate_symbol in ('<', '<='):
            can_var_term_be_arbitrarly_small = (
                (var_coef > 0 and not var_bounds.has_lower_bound) or (var_coef < 0 and not var_bounds.has_upper_bound)
            )
            return can_var_term_be_arbitrarly_small
        if relation.predicate_symbol in ('>', '>='):
            can_var_term_be_arbitrarly_large = (
                (var_coef > 0 and not var_bounds.has_upper_bound) or (var_coef < 0 and not var_bounds.has_lower_bound)
            )
            return can_var_term_be_arbitrarly_large
    return False


def simplify_modulo_terms_with_unbound_vars_in_relation(relation: Relation,
                                                        quantified_vars_with_bounds: Dict[str, Bounds_Info]
                                                        ) -> Relation:
    simplified_relation = Relation(variable_names=relation.variable_names,
                                   variable_coefficients=relation.variable_coefficients,
                                   modulo_terms=[],  # We will fill them with the terms that could not be simplified
                                   modulo_term_coefficients=[],
                                   div_terms=relation.div_terms,
                                   div_term_coefficients=relation.div_term_coefficients,
                                   absolute_part=relation.absolute_part,
                                   predicate_symbol=relation.predicate_symbol)

    for modulo_term_coef, modulo_term in zip(relation.modulo_term_coefficients, relation.modulo_terms):
        simplified_modulo_value: Optional[int] = None
        for var_name in modulo_term.variables:
            if not var_name in quantified_vars_with_bounds:
                continue
            var_bounds = quantified_vars_with_bounds[var_name]
            if not var_bounds.has_lower_bound or not var_bounds.has_upper_bound:
                simplified_modulo_value = modulo_term.constant
                break

        if simplified_modulo_value is not None:
            # Move the constant to which was the modulo term simplified directly to the right side
            simplified_relation.absolute_part -= modulo_term_coef * simplified_modulo_value
        else:
            # The term could not be simplified, append it as it is
            simplified_relation.modulo_terms.append(modulo_terms)
            simplified_relation.modulo_term_coefficients.append(modulo_term_coef)

    return simplified_relation


def remove_existential_quantification_of_unbound_vars(ast: AST_Node_With_Bounds_Info,
                                                      quantified_vars_with_bounds: Dict[str, Bounds_Info]
                                                      ) -> Union[bool, AST_Node_With_Bounds_Info]:

    if isinstance(ast, AST_Leaf_Node_With_Bounds_Info):
        if isinstance(ast.contents, Relation):
            if will_relation_be_always_satisfied_due_to_unbound_var(ast.contents, quantified_vars_with_bounds):
                return True
            simplified_relation = simplify_modulo_terms_with_unbound_vars_in_relation(ast.contents,
                                                                                      quantified_vars_with_bounds)
            return AST_Leaf_Node_With_Bounds_Info(contents=simplified_relation, bounds=ast.bounds)
        return ast

    elif isinstance(ast, AST_Quantifier_Node_With_Bounds_Info):
        for var_name, dummy_type in ast.bindings:
            quantified_vars_with_bounds[var_name] = ast.bounds[var_name]

        # @Optimize: Here we should also propagate back information that some variables are not present in the subtree,
        #            so we can drop some of the variables from the quantifier altogether
        subtree = remove_existential_quantification_of_unbound_vars(ast.children[0], quantified_vars_with_bounds)
        if isinstance(subtree, bool):
            return subtree  # The entire subtree was trivially satisfiable

        for var_name, dummy_type in ast.bindings:
            del quantified_vars_with_bounds[var_name]

        return AST_Quantifier_Node_With_Bounds_Info(node_type=ast.node_type, bindings=ast.bindings,
                                                    bounds=ast.bounds, children=[subtree])

    elif isinstance(ast, AST_Internal_Node_With_Bounds_Info):
        simplified_children = [
            remove_existential_quantification_of_unbound_vars(child, quantified_vars_with_bounds) for child in ast.children
        ]
        if ast.node_type == 'and':
            if any((child is False for child in simplified_children)):
                return False
            new_node_children = [child for child in simplified_children if not isinstance(child, bool)]
            if not new_node_children:
                return True  # All children are Booleans, but none of them is False, thus all must be True
            if len(new_node_children) == 1:
                return new_node_children[0]
        elif ast.node_type == 'or':
            if any((child is True for child in simplified_children)):
                return True
            new_node_children = [child for child in simplified_children if not isinstance(child, bool)]
            if not new_node_children:
                return False  # All children are Booleans, but none of them is True, thus all must be False
            if len(new_node_children) == 1:
                return new_node_children[0]
        elif ast.node_type == 'not':
            new_node_children = list(simplified_children)  # There is only one child
            if isinstance(new_node_children[0], bool):
                return not new_node_children[0]
        else:
            err_msg = (f'[Simplify quantification with var bounds]: Cannot descend into internal node '
                       f'{ast.node_type=} {ast=}')
            raise ValueError(err_msg)

        return AST_Internal_Node_With_Bounds_Info(node_type=ast.node_type, bounds=ast.bounds,
                                                  children=new_node_children)
    assert False


def _simplify_bounded_atoms(ast: AST_Node_With_Bounds_Info, vars_with_rewritten_bounds: Set[Var]) -> Optional[AST_Node]:
    if isinstance(ast, AST_Leaf_Node_With_Bounds_Info):
        if isinstance(ast.contents, (Var, Congruence, str, BoolLiteral)):
            return ast.contents

        relation: Relation = ast.contents
        if len(relation.vars) == 1:
            # The current relation represents a bound on a single variable
            bound_for_var = relation.vars[0]
            if bound_for_var in vars_with_rewritten_bounds:
                return None
        return relation

    if isinstance(ast, AST_Internal_Node_With_Bounds_Info):
        if ast.node_type == 'and':
            # At the current level we want to rewrite bounds only for those variables that will
            # not have their bounds rewritten at some upper level
            vars_to_rewrite_bounds_at_current_level: Set[Var] = set()
            for var, bound_info in ast.var_values.items():
                if len(bound_info) == 0:
                    return BoolLiteral(False)

                if len(bound_info) == 1 and var not in vars_with_rewritten_bounds:
                    bound = bound_info[0]
                    if bound.lower_limit is None and bound.upper_limit is None:
                        continue
                    vars_to_rewrite_bounds_at_current_level.add(var)

            new_ast_node: AST_NaryNode = ['and']
            for var_to_rewrite_bounds in vars_to_rewrite_bounds_at_current_level:
                var_bounds = ast.var_values[var_to_rewrite_bounds][0]
                if var_bounds.lower_limit is not None:
                    lower_bound = Relation.new_lin_relation(variable_names=[var_to_rewrite_bounds], variable_coefficients=[-1],
                                                            predicate_symbol='<=', absolute_part=-var_bounds.lower_limit)
                    new_ast_node.append(lower_bound)
                if var_bounds.upper_limit is not None:
                    upper_bound = Relation.new_lin_relation(variable_names=[var_to_rewrite_bounds], variable_coefficients=[1],
                                                            predicate_symbol='<=', absolute_part=var_bounds.upper_limit)
                    new_ast_node.append(upper_bound)

            vars_to_not_rewrite_at_lower_levels = vars_to_rewrite_bounds_at_current_level.union(vars_with_rewritten_bounds)
            for subtree in ast.children:
                simplified_subtree = _simplify_bounded_atoms(subtree, vars_to_not_rewrite_at_lower_levels)
                if simplified_subtree:
                    new_ast_node.append(simplified_subtree)
            return new_ast_node if len(new_ast_node) > 1 else None
        else:
            rewritten_subtrees = (_simplify_bounded_atoms(subtree, vars_with_rewritten_bounds) for subtree in ast.children)
            preserved_subtrees = (tree for tree in rewritten_subtrees if tree)
            new_ast_node = [ast.node_type, *preserved_subtrees]
            return new_ast_node if len(new_ast_node) > 1 else None

    if isinstance(ast, AST_Quantifier_Node_With_Bounds_Info):
        rewritten_subtree = _simplify_bounded_atoms(ast.child, vars_with_rewritten_bounds)

        assert_msg = ('The entire subtree under a quantifier has been factored out, meaning the quantifier has no semantic value?'
                      ' More likely are doing something wrong.')

        assert rewritten_subtree, assert_msg
        return [ast.node_type, ast.bindings, rewritten_subtree]  # type: ignore

    raise ValueError(f'Don\'t know how to process the node {ast=} when simplifying variable bounds.')


def _fmt_bound_analysis_tree_into_str(ast: AST_Node_With_Bounds_Info, depth: int) -> List[str]:
    prefix = '  '*depth
    if isinstance(ast, AST_Quantifier_Node_With_Bounds_Info):
        result = [f'{prefix}{ast.node_type}{ast.bindings}']
        result += _fmt_bound_analysis_tree_into_str(ast.child, depth+1)
        return result
    if isinstance(ast, AST_Internal_Node_With_Bounds_Info):
        result = [f'{prefix}{ast.node_type}  :: {dict(ast.var_values)}']
        for child in ast.children:
            result += _fmt_bound_analysis_tree_into_str(child, depth+1)
        return result
    if isinstance(ast, AST_Leaf_Node_With_Bounds_Info):
        return [f'{prefix}{ast.contents}']


def fmt_bound_analysis_tree_into_str(ast):
    return '\n'.join(_fmt_bound_analysis_tree_into_str(ast, 0))


def simplify_bounded_atoms(ast: AST_Node) -> Optional[AST_Node]:
    ast_with_bounds = perform_variable_bounds_analysis_on_ast(ast)
    simplified_tree = _simplify_bounded_atoms(ast_with_bounds, set())
    return simplified_tree


def _simplify_unbounded_equations(ast: AST_Node) -> AST_Node:
    if is_atom(ast):
        return ast

    assert isinstance(ast, list), ast
    node_type = ast[0]

    if node_type == 'exists':
        if isinstance(ast[2], Relation) and ast[2].predicate_symbol == '=':
            bound_vars: List[Var] = ast[1]  # type: ignore
            rel: Relation = ast[2]

            bound_var_coefs: List[int] = []
            remaining_lin_terms: List[Tuple[Var, int]] = []
            for var, coef in zip(rel.vars, rel.coefs):
                if var in bound_vars:
                    bound_var_coefs.append(coef)
                    continue
                remaining_lin_terms.append((var, coef))
            remaining_lin_terms = sorted(remaining_lin_terms, key = lambda var_coef_pair: var_coef_pair[0])

            if not remaining_lin_terms:
                return BoolLiteral(value=True)

            vars, coefs = [], []
            for var, coef in remaining_lin_terms:
                vars.append(var)
                coefs.append(coef)

            if sum(coef > 0 for coef in coefs):
                coefs = [-1 * coef for coef in coefs]

            modulus = gcd(*bound_var_coefs)
            congruence = Congruence(vars=list(vars), coefs=list(coefs), rhs=rel.rhs, modulus=modulus)
            return congruence
        return [node_type, ast[1], _simplify_unbounded_equations(ast[2])]
    else:
        children = (_simplify_unbounded_equations(child) for child in ast[1:])
        ret: AST_Node = [node_type, *children]
        return ret


def simplify_unbounded_equations(ast: AST_Node) -> AST_Node:
    return _simplify_unbounded_equations(ast)


def drop_negation_if_holding(ast: AST_Node, holding_negation: bool) -> AST_Node:
    return [AST_Node_Names.NOT.value, ast] if holding_negation else ast


def _push_negations_towards_atoms(ast: AST_Node, holding_negation) -> AST_Node:
    if isinstance(ast, str):
        return drop_negation_if_holding(ast, holding_negation)

    if isinstance(ast, Relation):
        rel: Relation = ast
        if rel.predicate_symbol == '=':
            return drop_negation_if_holding(rel, holding_negation)
        if not holding_negation:
            return rel
        assert rel.predicate_symbol == '<='
        negated_coefs = [-coef for coef in rel.coefs]
        rhs = -(rel.rhs+ 1)
        return Relation(vars=rel.vars, coefs=negated_coefs, rhs=rhs, predicate_symbol='<=')

    if isinstance(ast, Congruence):
        return drop_negation_if_holding(ast, holding_negation)

    if isinstance(ast, BoolLiteral):
        return BoolLiteral(value = not ast.value) if holding_negation else ast

    assert isinstance(ast, list)

    node_type: str = ast[0]  # type: ignore
    if node_type == AST_Node_Names.EXISTS.value:
        return drop_negation_if_holding(ast, holding_negation)

    if node_type == AST_Node_Names.AND.value:
        res_node_type = AST_Node_Names.OR.value if holding_negation else AST_Node_Names.AND.value
        return [res_node_type, *(_push_negations_towards_atoms(child, holding_negation) for child in ast[1:])]

    if node_type == AST_Node_Names.OR.value:
        res_node_type = AST_Node_Names.AND.value if holding_negation else AST_Node_Names.OR.value
        return [res_node_type, *(_push_negations_towards_atoms(child, holding_negation) for child in ast[1:])]

    if node_type == AST_Node_Names.NOT.value:
        holding_negation = not holding_negation
        return _push_negations_towards_atoms(ast[1], holding_negation=holding_negation)

    if node_type == AST_Node_Names.BOOL_EQUIV.value:
        return drop_negation_if_holding(ast, holding_negation)

    raise ValueError(f'Unhandled node type while pushing negation towards atoms: {ast=}')



def push_negations_towards_atoms(ast: AST_Node) -> AST_Node:
    """
    Push negations towards atom.

    Example:
        (not (and X (exists Z (Y (Z)))))   --->    (or (not X) (not (exists Z (Y (Z)))))
    """
    return _push_negations_towards_atoms(ast, holding_negation=False)


@dataclass(frozen=True)
class FrozenLinAtom:
    coefs: Tuple[int, ...]
    vars: Tuple[Var, ...]
    predicate_sym: str
    rhs: int

    @staticmethod
    def from_relation(rel: Relation) -> FrozenLinAtom:
        return FrozenLinAtom(coefs=tuple(rel.coefs), vars=tuple(rel.vars),
                             predicate_sym=rel.predicate_symbol, rhs=rel.rhs)

@dataclass(frozen=True)
class FrozenCongruence:
    coefs: Tuple[int, ...]
    vars: Tuple[Var, ...]
    modulus: int
    rhs: int

    @staticmethod
    def from_congruence(congruence: Congruence) -> FrozenCongruence:
        return FrozenCongruence(coefs=tuple(congruence.coefs), vars=tuple(congruence.vars), modulus=congruence.modulus, rhs=congruence.rhs)


@dataclass
class Literal:
    positive: bool = field(hash=False)
    id: int = field(hash=True)


def produce_dnf(and_literals: List[Literal], or_literals: List[Literal], literal_decoding_table: Dict[int, AST_Atom]) -> AST_Node:
    produced_clauses: List[Tuple[Literal, ...]] = []
    for or_literal in or_literals:
        produced_clauses.append((or_literal, *and_literals))

    # Detect contradictions
    # @Performance: This implementation is simply terrible; definitely needs improvements
    simplified_clauses: List[List[Literal]] = []
    for clause in produced_clauses:
        simplified_clause: List[Literal] = []
        seen_literals: Dict[int, Literal] = {}

        is_clause_contradiction = False
        for literal in clause:
            if literal.id not in seen_literals:
                seen_literals[literal.id] = literal
                simplified_clause.append(literal)
            else:
                if seen_literals[literal.id].positive != literal.positive:
                    is_clause_contradiction = True
                    break
                else:
                    pass  # Do not include the same literal multiple times in the same clause

        if not is_clause_contradiction:
            simplified_clauses.append(simplified_clause)

    if not simplified_clauses:
        return BoolLiteral(value=False)


    def decode_literal(literal: Literal) -> AST_Node:
        atom = literal_decoding_table[literal.id]
        return atom if literal.positive else [AST_Node_Names.NOT.value, atom]

    def decode_clause(clause: Iterable[Literal]) -> AST_Node:
        return [AST_Node_Names.AND.name, *(decode_literal(literal) for literal in clause)]

    if len(simplified_clauses) == 1:  # Do not introduce an extra OR node
        clause = simplified_clauses[0]
        if len(clause) == 1:
            return decode_literal(clause[0])
        return decode_clause(clause)

    return [AST_Node_Names.OR.name, *(decode_clause(clause) for clause in simplified_clauses)]


def is_atom(ast: AST_Node) -> bool:
    atom_types = (str, BoolLiteral, Relation, Congruence, Var)
    return any(isinstance(ast, atom_type) for atom_type in atom_types)


def is_literal(ast: AST_Node) -> bool:
    if is_atom(ast):
        return True

    assert isinstance(ast, list)
    return ast[0] == AST_Node_Names.NOT.value and is_atom(ast[1])



LiteralIds = Tuple[int, ...]
LiteralIdDecodingTable = Dict[int, Literal]
FrozenAtom = Union[str, BoolLiteral, FrozenLinAtom, FrozenCongruence]

def do_and_or_tree_lookahead_and_produce_dnf(ast: AST_Node) -> Optional[AST_Node]:
    if not isinstance(ast, list):
        return None

    node_type: str = ast[0]  # type: ignore
    if node_type != AST_Node_Names.AND.value:
        return None

    children = ast[1:]
    and_literals = [child for child in children if is_literal(child)]
    or_nodes = [child for child in children if isinstance(child, list) and child[0] == AST_Node_Names.OR.value]

    flattening_happened = len(or_nodes) == 1
    if not flattening_happened:
        return None

    if len(or_nodes) + len(and_literals) != len(children):
        return None

    or_node = or_nodes[0]
    if not all(is_literal(or_child) for or_child in or_node[1:]):
        return None

    def freeze_atom(atom: AST_Atom) -> FrozenAtom:
        if isinstance(atom, Relation):
            return FrozenLinAtom.from_relation(atom)
        elif isinstance(atom, Congruence):
            return FrozenCongruence.from_congruence(atom)
        else:
            assert isinstance(atom, str) or isinstance(atom, BoolLiteral), atom
            return atom

    # We have a valid AND-OR tree

    literal_decoding_table: Dict[int, AST_Atom] = {}
    literal_table: Dict[Union[FrozenLinAtom, FrozenCongruence, str, BoolLiteral], int] = {}

    def make_atoms_into_literals(ast: AST_NaryNode) -> List[Literal]:
        literals: List[Literal] = []
        for _child in ast:
            child: AST_Atom = _child  # type: ignore

            is_positive = True
            if isinstance(child, list) and child[0] == AST_Node_Names.NOT.value:
                child = child[1]
                is_positive = False

            frozen_atom = freeze_atom(child)
            if frozen_atom in literal_table:
                literal_id = literal_table[frozen_atom]
            else:
                literal_id = len(literal_table)
                literal_table[frozen_atom] = literal_id
                literal_decoding_table[literal_id] = child
            literals.append(Literal(positive=is_positive, id=literal_id))
        return literals

    or_literals = make_atoms_into_literals(or_node[1:])
    and_literals = make_atoms_into_literals(and_literals)

    if not set(lit.id for lit in or_literals).issubset(lit.id for lit in and_literals):
        return None

    dnf = produce_dnf(and_literals, or_literals, literal_decoding_table)
    return dnf


def _convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast: AST_Node) -> AST_Node:
    """
    Convert 2-deep AND-OR trees into DNF if they are talking about similar atoms.

    Conversion is performed if the subordinate tree is talking about a subset of parent atoms.
    """

    if is_atom(ast):
        return ast

    assert isinstance(ast, list)
    node_type: str = ast[0]  # type: ignore

    if node_type == AST_Node_Names.AND.value:
        children = ast[1:]
        atoms = [child for child in children if is_atom(child)]
        or_nodes = [child for child in children if isinstance(child, list) and child[0] == AST_Node_Names.OR.value]

        # Are we dealing with an AND-OR tree?
        dnf = do_and_or_tree_lookahead_and_produce_dnf(ast)
        if dnf:
            return dnf

        return [AST_Node_Names.AND.value, *(_convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(child) for child in children)]

    if node_type == AST_Node_Names.EXISTS.value:
        return [AST_Node_Names.EXISTS.value, ast[1], _convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast[2])]

    if node_type == AST_Node_Names.NOT.value:
        return [AST_Node_Names.NOT.value, _convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast[1])]

    if node_type == AST_Node_Names.OR.value:
        children =  ast[1:]
        return [AST_Node_Names.OR.value, *(_convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(child) for child in children)]

    logger.warning(f'Unhandled node while converting tree into DNF: %s', ast)
    return [node_type, *(_convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(child) for child in ast[1:])]


def convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast: AST_Node) -> AST_Node:
    result = _convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast)
    return result
