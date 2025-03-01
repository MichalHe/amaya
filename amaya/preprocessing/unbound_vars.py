from __future__ import annotations
from collections import defaultdict
import fractions
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
    cast,
)
from amaya.preprocessing.eval import LinTerm, Scoper, VarInfo, split_lin_terms_into_vars_and_coefs

from amaya.relations_structures import (
    AST_Atom,
    AST_Connective,
    AST_NaryNode,
    AST_Negation,
    AST_Node,
    AST_Node_Names,
    AST_Quantifier,
    ASTp_Node,
    BoolLiteral,
    Bound_Type,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
    Value_Interval,
    ast_get_binding_list,
    ast_get_node_type,
    get_hard_bound_semantics,
    make_and_node,
    make_exists_node,
    pprint_formula,
    unzip_lin_terms,
)

from amaya import logger
from amaya.config import solver_config


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


def _make_value_interval_union(left_intervals: List[Value_Interval], right_intervals: List[Value_Interval]) -> List[Value_Interval]:
    intervals = left_intervals + right_intervals
    min_lower_bound = None

    for interval in intervals:
        if interval.lower_limit is not None:
            min_lower_bound = min(min_lower_bound, interval.lower_limit) if min_lower_bound else interval.lower_limit

    if min_lower_bound is None:
        min_lower_bound = 0
    else:
        min_lower_bound = -1

    def get_lower_bound(interval: Value_Interval) -> int:
        if interval.lower_limit is None:
            return min_lower_bound
        return interval.lower_limit

    intervals = sorted(intervals, key=get_lower_bound)

    interval_union = []
    current_interval = intervals[0]
    for interval in intervals[1:]:
        if current_interval.upper_limit is None:
            interval_union.append(current_interval)
            return interval_union

        # The intervals are sorted by their lower limits, therefore, the `current_interval`
        # also has lower limit = -inf
        if interval.lower_limit is None:
            if interval.upper_limit is None:
                current_interval = Value_Interval()
                continue  # We will return in the next iteration either way

            old_val: int = current_interval.upper_limit
            new_val: int = interval.upper_limit
            current_interval.upper_limit = max(old_val, new_val)
            continue

        if interval.lower_limit <= current_interval.upper_limit:  # The intervals overlap
            if interval.upper_limit is None:
                current_interval.upper_limit = None
            else:
                current_interval.upper_limit = max(current_interval.upper_limit, interval.upper_limit)
        else: # The intervals do not overlap
            interval_union.append(current_interval)
            current_interval = interval

    return interval_union


def make_value_interval_union(left_intervals: List[Value_Interval], right_intervals: List[Value_Interval]):
    if not left_intervals:
        return right_intervals
    if not right_intervals:
        return left_intervals

    # Start = 's', End = 'e'
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

            bound = math.floor(bound) if coef <= 0 else math.ceil(bound)

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
        overall_bounds_info.var_values = defaultdict(list)
        seen_vars: Dict[Var, int] = defaultdict(int)

        for subtree_with_bounds in subtrees_with_bounds:
            for var, bounds_info in subtree_with_bounds.var_values.items():
                overall_bounds_info.var_values[var] = make_value_interval_union(overall_bounds_info.var_values[var],
                                                                                bounds_info)
                seen_vars[var] += 1

        for seen_var, seen_cnt in seen_vars.items():
            if seen_cnt < len(subtrees_with_bounds):
                overall_bounds_info.var_values[seen_var] = [Value_Interval()]

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


def filter_vars_with_no_info_from_node(vars_with_bounds_rewritten: Set[Var], node: AST_Internal_Node_With_Bounds_Info) -> Set[Var]:
    vars_with_no_info_about_their_value: Set[Var] = set()

    for var in vars_with_bounds_rewritten:
        var_values = node.var_values.get(var, [Value_Interval()])

        if len(var_values) != 1:
            continue

        value_interval = var_values[0]
        if value_interval.lower_limit is None and value_interval.upper_limit is None:
            vars_with_no_info_about_their_value.add(var)

    return vars_with_bounds_rewritten.difference(vars_with_no_info_about_their_value)


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
                if len(bound_info) == 1 and var not in vars_with_rewritten_bounds:
                    bound = bound_info[0]
                    if bound.lower_limit is None and bound.upper_limit is None:
                        continue
                    vars_to_rewrite_bounds_at_current_level.add(var)

            new_ast_node: AST_NaryNode = ['and']
            for var_to_rewrite_bounds in vars_to_rewrite_bounds_at_current_level:
                var_bounds = ast.var_values[var_to_rewrite_bounds][0]
                are_bounds_equal = var_bounds.lower_limit == var_bounds.upper_limit
                if var_bounds.lower_limit is not None:
                    if are_bounds_equal:  # Both of the bounds have value (!= None)
                        eq = Relation(vars=[var_to_rewrite_bounds], coefs=[1], predicate_symbol='=', rhs=var_bounds.lower_limit)
                        new_ast_node.append(eq)
                        continue

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
            vars_to_not_rewrite = filter_vars_with_no_info_from_node(vars_with_rewritten_bounds, ast)
            rewritten_subtrees = (_simplify_bounded_atoms(subtree, vars_to_not_rewrite) for subtree in ast.children)
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
            rhs = rel.rhs % modulus
            congruence = Congruence(vars=list(vars), coefs=list(coefs), rhs=rhs, modulus=modulus)
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


def _push_negations_towards_atoms(ast: AST_Node, holding_negation: bool) -> AST_Node:
    if isinstance(ast, (Var, str)):
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

    assert isinstance(ast, list), ast

    node_type: str = ast[0]  # type: ignore
    if node_type == AST_Node_Names.EXISTS.value:
        if holding_negation:
            child = _push_negations_towards_atoms(ast[2], False)
            return ['not', [node_type, ast[1], child]]
        else:  # Not holding negation
            return [node_type, ast[1], _push_negations_towards_atoms(ast[2], holding_negation)]

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
    result = _push_negations_towards_atoms(ast, holding_negation=False)
    return result


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
    return isinstance(ast, atom_types)


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

    if node_type == AST_Node_Names.BOOL_EQUIV.value:
        new_children = (_convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(child) for child in ast[1:])
        return [node_type, *new_children]

    logger.warning(f'Unhandled node while converting tree into DNF: %s', ast)
    return [node_type, *(_convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(child) for child in ast[1:])]


def convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast: AST_Node) -> AST_Node:
    result = _convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast)
    return result


def _collect_variables_present_in_formula(ast: AST_Node) -> Set[Var]:
    if isinstance(ast, (Relation, Congruence)):
        return set(ast.vars)
    if isinstance(ast, Var):
        return set([ast])
    if isinstance(ast, BoolLiteral):
        return set()

    assert isinstance(ast, list), ast

    node_type = ast_get_node_type(ast)
    if node_type == 'exists':
        return _collect_variables_present_in_formula(ast[2])

    return functools.reduce(set.union, (_collect_variables_present_in_formula(child) for child in ast[1:]), set())


def replace_congruence_component_with_term(congruence: Congruence, component: Tuple[Tuple[int, Var]], replace_term: Tuple[int, Var]) -> Congruence:
    component_vars = tuple(term[1] for term in component)

    new_terms: List[Tuple[int, Var]] = [term for term in congruence.linear_terms() if term[1] not in component_vars]
    new_terms.append(replace_term)
    new_terms = sorted(new_terms, key=lambda it: it[1])

    vars, coefs = [], []
    for coef, var in new_terms:
        vars.append(var)
        coefs.append(coef)

    return Congruence(vars=vars, coefs=coefs, rhs=congruence.rhs, modulus=congruence.modulus)



def _try_rewrite_congruence_on_unbund_vars(exists_and_tree: AST_NaryNode, var_table: Dict[Var, VarInfo]) -> Optional[AST_NaryNode]:
    bound_vars = ast_get_binding_list(exists_and_tree)
    and_node = exists_and_tree[2]
    leaves = and_node[1:]  # type:ignore

    _used_vars = (_collect_variables_present_in_formula(leaf) for leaf in leaves if not isinstance(leaf, Congruence))
    used_vars = functools.reduce(set.union, _used_vars, set())
    bound_vars_used_only_in_congruences = set(bound_vars) - used_vars

    congruences, non_congruences = [], []
    for child in leaves:
        if isinstance(child, Congruence):
            congruences.append(child)
        else:
            non_congruences.append(child)

    if not bound_vars_used_only_in_congruences:
        return None

    new_congruences: List[Congruence] = []
    new_bound_vars: List[Var] = []
    var_to_replace_multiple_unbound_with = next(iter(bound_vars_used_only_in_congruences))

    LinTerm = Tuple[Tuple[int, Var], ...]
    unbound_components: Dict[LinTerm, Tuple[Var, List[int]]] = {}

    free_var_id = max(var_table).id + 1
    for congruence_idx, congruence in enumerate(congruences):
        unbound_vars: List[Var] = []
        unbound_coefs: List[int] = []
        for coef, var in zip(congruence.coefs, congruence.vars):
            if var in bound_vars_used_only_in_congruences:
                unbound_vars.append(var)
                unbound_coefs.append(coef)

        if not unbound_vars:
            new_congruences.append(congruence)
            continue

        component: Tuple[Tuple[int, Var], ...] = tuple(sorted(zip(unbound_coefs, unbound_vars), key=lambda it: it[0]))
        if component in unbound_components:
            unbound_components[component][1].append(congruence_idx)
        else:
            unbound_components[component] = (Var(free_var_id), [congruence_idx])
            free_var_id += 1

    for component, var_and_congruence_indices in unbound_components.items():
        var, congruence_indices = var_and_congruence_indices
        component_gcd = gcd(*(lin_term[0] for lin_term in component))

        if component_gcd == 1:
            # The term b.y can generate the entire ring (Z_mod, +, *). If there are multiple congruences,
            # then we need cannot drop them as they "communicate" via the term
            if len(congruence_indices) == 1:
                continue

            # There are multiple congruences with the same term, introduce a new single variable so they can
            # communicate
            replacement_term = (component_gcd, var)
            for congruence_idx in congruence_indices:
                congruence = congruences[congruence_idx]
                new_congruence = replace_congruence_component_with_term(congruence, component, replacement_term)
                new_congruences.append(new_congruence)

            new_bound_vars.append(var)
            continue

        # Modulus and GCD have some common divisor > 1, meaning that the rhs (-b.y + k) can generate only
        # some cyclic subset of Z_mod and we cannot further simplify the songruence
        if len(component) == 1:
            new_congruences.extend(congruences[idx] for idx in congruence_indices)
            continue

        coef = component_gcd
        replacement_term = (component_gcd, var)
        for congruence_idx in congruence_indices:
            congruence = congruences[congruence_idx]
            new_congruence = replace_congruence_component_with_term(congruence, component, replacement_term)
            new_congruences.append(new_congruence)

        new_bound_vars.append(var)

    # Variables that were part of some relations were not considered unbound and therefore they must be stil part of the quantifier
    new_binding_list = [var for var in bound_vars if var not in bound_vars_used_only_in_congruences] + new_bound_vars
    assert new_binding_list, exists_and_tree
    new_and_node = make_and_node([*non_congruences, *new_congruences])
    new_node = make_exists_node(new_binding_list, new_and_node)

    for new_var in new_bound_vars:
        var_table[new_var] = VarInfo(name='congruence replacement', type=VariableType.INT)

    return new_node


def _simplify_congruences_on_unbounded_existential_vars(ast: AST_Node, var_table: Dict[Var, VarInfo]) -> AST_Node:
    if not isinstance(ast, list):
        return ast

    node_type = ast_get_node_type(ast)

    if node_type == 'exists':
        # Perform lookahead to check whether we have (exists Vars (and Atoms))
        child: AST_Node = ast[2]
        if not isinstance(child, list):
            return ast

        child_type = ast_get_node_type(child)
        if child_type == 'and':
            new_ast = _try_rewrite_congruence_on_unbund_vars(ast, var_table)
            if not new_ast:
                return ['exists', ast[1], _simplify_congruences_on_unbounded_existential_vars(ast[2], var_table)]
            return new_ast
        return ['exists', ast[1], _simplify_congruences_on_unbounded_existential_vars(ast[2], var_table)]

    # The node is some N-ary
    rewritten_children = tuple(_simplify_congruences_on_unbounded_existential_vars(child, var_table) for child in ast[1:])
    return [node_type, *rewritten_children]


def simplify_congruences_on_unbounded_existential_vars(ast: AST_Node, var_table: Dict[Var, VarInfo]) -> AST_Node:
    ret = _simplify_congruences_on_unbounded_existential_vars(ast, var_table)
    return ret


def _collect_used_free_variables(ast: AST_Node, bound_vars: Set[Var]) -> Set[Var]:
    if isinstance(ast, Var):
        return {ast}
    if isinstance(ast, (Relation, Congruence)):
        return set(ast.vars).difference(bound_vars)
    if not isinstance(ast, list):
        return set()

    node_type = ast_get_node_type(ast)
    if node_type == 'exists':
        newly_bound_vars = ast_get_binding_list(ast)
        new_bound_vars = bound_vars.union(newly_bound_vars)
        return _collect_used_free_variables(ast[2], new_bound_vars)

    return functools.reduce(set.union, (_collect_used_free_variables(child, bound_vars) for child in ast[1:]), set())


def _are_exists_and_trees_isomorphic(left: AST_Node, right: AST_Node, isomorphism: Dict[Var, Var]) -> bool:
    if type(left) != type(right):
        return False

    if isinstance(left, (Relation, Congruence)):
        assert isinstance(right, (Relation, Congruence))

        if len(left.vars) != len(right.vars):
            return False

        if sorted(left.coefs) != sorted(right.coefs):
            return False

        left_vars_to_coefs: Dict[Var, int] = {var:coef for coef, var in left.linear_terms()}
        right_vars_to_coefs: Dict[Var, int] = {var:coef for coef, var in right.linear_terms()}

        for left_var in left.vars:
            left_coef = left_vars_to_coefs[left_var]
            right_var = isomorphism[left_var]
            right_coef = right_vars_to_coefs[right_var]

            if left_coef != right_coef:
                return False
        return True

    if isinstance(left, BoolLiteral):
        assert isinstance(right, BoolLiteral)
        return left.value == right.value

    if not isinstance(left, list):
        logger.warning('Unhandled branch in isomorphism checking, assumimg that the trees are not isomorphic')
        return False

    assert isinstance(left, list)
    assert isinstance(right, list)

    left_node_type  = ast_get_node_type(left)
    right_node_type = ast_get_node_type(right)

    if left_node_type != right_node_type:
        return False

    if len(left) != len(right):
        return False

    if left_node_type == 'exists':
        left_bindings = ast_get_binding_list(left)
        right_bindings = ast_get_binding_list(right)
        if len(left_bindings) != len(right_bindings):
            return False

        # @Incomplete: Extend the isomorphism in a naive fashion
        isomorphism = dict(isomorphism)
        for left_var, right_var in zip(left_bindings, right_bindings):
            isomorphism[left_var] = right_var

        return _are_exists_and_trees_isomorphic(left[2], right[2], isomorphism)

    return all(_are_exists_and_trees_isomorphic(left_child, right_child, isomorphism) for left_child, right_child in zip(left[1:], right[1:]))


def are_exists_and_trees_isomorphic(left: AST_Node, right: AST_Node, free_vars: Iterable[Var]) -> bool:
    isomorphism = {free_var: free_var for free_var in free_vars}
    are_isomorphic = _are_exists_and_trees_isomorphic(left, right, isomorphism)
    return are_isomorphic


def _check_if_children_are_conflicting(children: List[AST_NaryNode], free_vars: Tuple[Var, ...]) -> bool:
    positive, negative = [], []
    for child in children:
        if ast_get_node_type(child) == 'not':
            negative.append(child)
        else:
            positive.append(child)

    # @Incomplete: There could be other clauses that might nothing to do with the conflict
    if len(positive) != 1 or len(negative) != 1:
        return False

    neg_node = negative[0][1] # Strip the leading 'not'
    return are_exists_and_trees_isomorphic(positive[0], neg_node, free_vars)


def _detect_conflics_on_isomorphic_fragments(ast: AST_Node) -> AST_Node:
    """ Detects conflicting conjunctive clauses that conflict because of different renaming of bound vars. """
    if not isinstance(ast, list):
        return ast

    node_type = ast_get_node_type(ast)
    if node_type == 'exists':
        return ['exists', ast[1], _detect_conflics_on_isomorphic_fragments(ast[2])]

    if node_type == 'and':
        rewritten_children = [_detect_conflics_on_isomorphic_fragments(child) for child in ast[1:]]

        children: List[AST_NaryNode] = [child for child in rewritten_children if isinstance(child, list)]
        free_vars_to_children: Dict[Tuple[Var, ...], List[AST_NaryNode]] = defaultdict(list)
        for child in children:
            free_vars = tuple(sorted(_collect_used_free_variables(child, set())))
            free_vars_to_children[free_vars].append(child)

        for free_vars, children_with_same_free_vars in free_vars_to_children.items():
            # @Incomplete: There could be other clauses that might nothing to do with the conflict, for now we focus on (and A (not A))
            if len(children_with_same_free_vars) > 2:
                continue

            if _check_if_children_are_conflicting(children_with_same_free_vars, free_vars):
                return BoolLiteral(value=False)

        # No clauses were found conflicting
        return ['and', *rewritten_children]

    return [ast[0], *(_detect_conflics_on_isomorphic_fragments(child) for child in ast[1:])]


def detect_conflics_on_isomorphic_fragments(ast: AST_Node) -> AST_Node:
    """ Detects conflicting conjunctive clauses that conflict because of different renaming of bound vars. """
    return _detect_conflics_on_isomorphic_fragments(ast)



@dataclass
class Parent_Context_Var_Values:
    """ Keeps track of values asserted in somewhere parent nodes. """
    seen_vars: Set[Var] = field(default_factory=set)
    asserted_var_values: List[Dict[Var, Value_Interval]] = field(default_factory=lambda: [defaultdict(Value_Interval)])

    def enter_context(self):
        new_ctx = {}
        self.asserted_var_values.append(new_ctx)

    def enter_blocking_context(self):
        new_ctx = {var: Value_Interval() for var in self.seen_vars}
        self.asserted_var_values.append(new_ctx)

    def lookup_asserted_values(self, var: Var) -> Value_Interval:
        for ctx in reversed(self.asserted_var_values):
            if var in ctx:
                return ctx[var]
        return Value_Interval()  # [-Inf,Inf]

    def exit_context(self):
        self.asserted_var_values.pop(-1)

    def assert_new_var_value(self, var: Var, new_interval: Value_Interval):
        self.seen_vars.add(var)

        active_ctx = self.asserted_var_values[-1]
        active_ctx[var] = new_interval

    def get_known_variable_domains(self) -> Dict[Var, Value_Interval]:
        domains = {}

        for context in reversed(self.asserted_var_values):
            domains.update(context)
            if len(domains) == len(self.seen_vars):
                return domains

        return domains


def _insert_all_asserting_bounds_into_current_context(and_connective: AST_Connective, contexter: Parent_Context_Var_Values):
    children = and_connective.children
    bounds = (child for child in children if isinstance(child, Relation) and len(child.vars) == 1)
    for bound in bounds:
        var, coef = bound.vars[0], bound.coefs[0]
        rhs = bound.rhs

        val_interval = contexter.lookup_asserted_values(var)

        if bound.predicate_symbol == '=':
            if (rhs % coef) != 0:
                return BoolLiteral(False)  # e.g. x >= 3, and we are in a child: (3x = 5 AND <Subformula>)
            implied_val = rhs // coef

            upper = val_interval.upper_limit if val_interval.upper_limit is not None else implied_val + 1
            lower = val_interval.lower_limit if val_interval.lower_limit is not None else implied_val - 1

            if implied_val < lower or implied_val > upper:
                return BoolLiteral(False)  # e.g. x >= 3, and we are in a child: (x = 0 AND <Subformula>)

            new_interval = Value_Interval(lower_limit=implied_val, upper_limit=implied_val)
            contexter.assert_new_var_value(var, new_interval)
            continue

        if coef < 0:  # Lower limit
            implied_val = math.ceil(rhs / coef)
            old_lower = val_interval.lower_limit if val_interval.lower_limit is not None else implied_val - 1
            new_lower = max(implied_val, old_lower)
            contexter.assert_new_var_value(var, Value_Interval(new_lower, val_interval.upper_limit))
        else:  # Upper limit
            implied_val = math.floor(rhs / coef)
            old_upper = val_interval.upper_limit if val_interval.upper_limit is not None else implied_val + 1
            new_upper = min(implied_val, old_upper)
            contexter.assert_new_var_value(var, Value_Interval(val_interval.lower_limit, new_upper))


def _prune_in_connective(connective: AST_Connective, contexter: Parent_Context_Var_Values) -> ASTp_Node:
    match connective.type:
        case Connective_Type.AND:
            contexter.enter_context()

            children = connective.children
            _insert_all_asserting_bounds_into_current_context(connective, contexter)

            new_bounds = []
            for var, var_values in contexter.asserted_var_values[-1].items():
                is_single_value_implied = var_values.lower_limit == var_values.upper_limit
                if var_values.lower_limit is not None and is_single_value_implied:
                    new_bounds.append(Relation(vars=[var], coefs=[1], rhs=var_values.lower_limit, predicate_symbol='='))
                    continue

                if var_values.lower_limit is not None:
                    new_bounds.append(Relation(vars=[var], coefs=[-1], rhs=-var_values.lower_limit, predicate_symbol='<='))

                if var_values.upper_limit is not None:
                    new_bounds.append(Relation(vars=[var], coefs=[1], rhs=var_values.upper_limit, predicate_symbol='<='))

            def is_bound(node: ASTp_Node):
                return isinstance(node, Relation) and len(node.vars) == 1

            _new_rich_children = (_prune_conjunctions_false_due_to_parent_context(child, contexter) for child in children if not is_bound(child))
            new_rich_children = tuple((child for child in _new_rich_children if child != BoolLiteral(True)))

            if any(child == BoolLiteral(False) for child in new_rich_children):
                return BoolLiteral(False)

            contexter.exit_context()

            new_subtree = (*new_bounds, *new_rich_children)
            if len(new_subtree) == 0:
                return BoolLiteral(True)
            if len(new_subtree) == 1:
                return new_subtree[0]

            new_node = AST_Connective(referenced_vars=connective.referenced_vars,
                                      type=Connective_Type.AND,
                                      children=new_subtree,
                                      variable_bounds=contexter.get_known_variable_domains())

            return new_node

        case Connective_Type.OR:
            _new_children = (_prune_conjunctions_false_due_to_parent_context(child, contexter) for child in connective.children)
            new_children = tuple(child for child in _new_children if child != BoolLiteral(False))

            if any(child == BoolLiteral(True) for child in new_children):
                return BoolLiteral(True)

            if len(new_children) == 0:
                return BoolLiteral(False)
            if len(new_children) == 1:
                return new_children[0]

            new_node = AST_Connective(referenced_vars=connective.referenced_vars, type=Connective_Type.OR, children=new_children)
            return new_node
        case Connective_Type.EQUIV:
            new_children = tuple(_prune_conjunctions_false_due_to_parent_context(child, contexter) for child in connective.children)
            return AST_Connective(referenced_vars=connective.referenced_vars, type=Connective_Type.EQUIV, children=new_children)
        case _:
            raise NotImplementedError(f'Connective not handled when doing interval analysis: {connective=}')


def three_value_logic_mult(value: int | None, scalar: int) -> int | None:
    return value * scalar if value is not None else None


def three_value_add(value: int | None, other_val: int | None) -> int | None:
    if value is None or other_val is None:
        return None
    return value + other_val


def compute_lin_term_expr_bound(rel: Relation, contexter: Parent_Context_Var_Values) -> Value_Interval:
    var_coefs_iterator = zip(rel.vars, rel.coefs)
    var, coef = next(var_coefs_iterator)

    lin_term_bounds = contexter.lookup_asserted_values(var).copy()
    lin_term_bounds.lower_limit = three_value_logic_mult(lin_term_bounds.lower_limit, coef)
    lin_term_bounds.upper_limit = three_value_logic_mult(lin_term_bounds.upper_limit, coef)
    if coef < 0:
        lin_term_bounds.lower_limit, lin_term_bounds.upper_limit = lin_term_bounds.upper_limit, lin_term_bounds.lower_limit

    for var, coef in var_coefs_iterator:
        var_bounds = contexter.lookup_asserted_values(var)
        lower_limit = three_value_logic_mult(var_bounds.lower_limit, coef)
        upper_limit = three_value_logic_mult(var_bounds.upper_limit, coef)
        if coef < 0:
            lower_limit, upper_limit = upper_limit, lower_limit

        lin_term_bounds.lower_limit = three_value_add(lin_term_bounds.lower_limit, lower_limit)
        lin_term_bounds.upper_limit = three_value_add(lin_term_bounds.upper_limit, upper_limit)

    return lin_term_bounds

def rewrite_using_bounds_on_lhs_lin_term(relation: Relation, contexter: Parent_Context_Var_Values) -> ASTp_Node | None:
    """
    Rewrite given relation by computing overapproximation of LHS values and checking its feasability.

    Enabled if solver_config.optimizations.rewrite_by_overapprox_relation_rhs is True.
    """
    if not solver_config.optimizations.rewrite_existential_equations_via_gcd:
        return None

    if relation.predicate_symbol == '<=':
        lhs_expr_bound = compute_lin_term_expr_bound(relation, contexter)
        if lhs_expr_bound.lower_limit is not None and lhs_expr_bound.lower_limit > relation.rhs:
            return BoolLiteral(False)
        elif lhs_expr_bound.upper_limit is not None and lhs_expr_bound.upper_limit <= relation.rhs:
            return BoolLiteral(True)
    elif relation.predicate_symbol == '=':
        lhs_expr_bound = compute_lin_term_expr_bound(relation, contexter)
        higher_than_lower_lim = relation.rhs >= lhs_expr_bound.lower_limit if lhs_expr_bound.lower_limit is not None else True
        lower_than_upper_lim = relation.rhs <= lhs_expr_bound.upper_limit if lhs_expr_bound.upper_limit is not None else True
        can_be_satisfied = higher_than_lower_lim and lower_than_upper_lim
        if not can_be_satisfied:
            return BoolLiteral(False)
    return None


def _prune_conjunctions_false_due_to_parent_context(node: ASTp_Node, contexter: Parent_Context_Var_Values) -> ASTp_Node:
    if isinstance(node, Relation):
        relation: Relation = node

        if len(relation.vars) > 1:
            rel_rewritten_using_bounds = rewrite_using_bounds_on_lhs_lin_term(relation, contexter)
            if rel_rewritten_using_bounds is not None:
                return rel_rewritten_using_bounds
            return node

        var, coef = relation.vars[0], relation.coefs[0]
        rhs = relation.rhs

        if relation.predicate_symbol == '<=':

            ctx_vals = contexter.lookup_asserted_values(var)

            if coef < 0:
                implied_val = math.ceil(rhs / coef)
                # Look whether the current bound requires var value to be higher then possible due to parent's constraints
                parents_upper_limit = ctx_vals.upper_limit if ctx_vals.upper_limit is not None else implied_val + 1
                if implied_val > parents_upper_limit:  # Parent asserts that x must be <= than 5, child says x must be >= 6
                    return BoolLiteral(False)

                # Look whether we are strengthening the lower bound or not
                ctx_lower_val = ctx_vals.lower_limit
                if not ctx_lower_val:
                    return node

                if ctx_lower_val > implied_val:  # The relation can be strenghtened
                    rhs = -ctx_lower_val   # Because coef is negative -x <= k  <-> x >= -k
                    return Relation(vars=relation.vars, coefs=[-1], rhs=rhs, predicate_symbol='<=')
            else:  # coef > 0
                implied_val = math.floor(rhs / coef)
                parents_lower_limit = ctx_vals.lower_limit if ctx_vals.lower_limit is not None else implied_val - 1
                if implied_val < parents_lower_limit:  # Parent asserts that x must be >= 0, child says x must be <= -1
                    return BoolLiteral(False)

                ctx_upper_val = ctx_vals.upper_limit
                if not ctx_upper_val:
                    return node

                if ctx_upper_val < implied_val:  # The relation can be strenghtened
                    return Relation(vars=relation.vars, coefs=[1], rhs=ctx_upper_val, predicate_symbol='<=')
            return node

        # relation is an equation
        if (relation.rhs % coef) != 0:  # -2x = 5
            return BoolLiteral(False)

        implied_val = relation.rhs // coef  # x = +/- implied_value
        val_interval = contexter.lookup_asserted_values(var)

        upper = val_interval.upper_limit if val_interval.upper_limit is not None else implied_val + 1
        lower = val_interval.lower_limit if val_interval.lower_limit is not None else implied_val - 1

        if implied_val < lower or implied_val > upper:
            return BoolLiteral(False)

        return Relation(vars=[var], coefs=[1], rhs=implied_val, predicate_symbol='=')

    if isinstance(node, (Congruence, Var, BoolLiteral)):  # Congruences, BoolLiterals etc
        return node

    match node:
        case AST_Connective():
            return _prune_in_connective(node, contexter)

        case AST_Negation():
            child = node.child
            if isinstance(child, Relation) and child.predicate_symbol == '=':
                # Check if what the negated equation implies is already implied from parent context
                eq = child
                var, coef, rhs = eq.vars[0], eq.coefs[0], eq.rhs
                if (rhs % coef) != 0:
                    return BoolLiteral(True)
                implied_val = rhs // coef

                val_interval = contexter.lookup_asserted_values(var)
                upper = val_interval.upper_limit if val_interval.upper_limit is not None else implied_val + 1
                lower = val_interval.lower_limit if val_interval.lower_limit is not None else implied_val - 1

                # If the implied_value is not included in the interval, then we can just ignore it
                if implied_val < lower or implied_val > upper:
                    return BoolLiteral(True)

            # Once we've passed through a negation we forget everything about parent context.
            # alternatively, we would need a ritcher interval domain to precisely handle nagations.
            # contexter.enter_blocking_context()
            new_child = _prune_conjunctions_false_due_to_parent_context(child, contexter)
            new_node = AST_Negation(referenced_vars=node.referenced_vars, child=new_child)
            # contexter.exit_context()
            return new_node

        case AST_Quantifier():
            child = _prune_conjunctions_false_due_to_parent_context(node.child, contexter)
            return AST_Quantifier(referenced_vars=node.referenced_vars, bound_vars=node.bound_vars, child=child)

        case _:
            raise NotImplementedError(f'ASTp node not handled when doing interval analysis: {node=}')


def prune_conjunctions_false_due_to_parent_context(root: ASTp_Node) -> ASTp_Node:
    """
    Remove conjunctions that are false due to them assessing variable values that are falsified in partent contexts.

    For example:
        (and (>= x 0) (or (and (= x 3) (= y 2)) <Subformula>)) would remove (and (= x 3) (= y  2))
    """
    contexter = Parent_Context_Var_Values()
    result = _prune_conjunctions_false_due_to_parent_context(root, contexter)
    return result


@dataclass
class Var_Monotonicity:
    increasing: bool = False
    decreasing: bool = False
    congruences: List[Tuple[int, Congruence]] = field(default_factory=list)
    limits: Value_Interval = field(default_factory=Value_Interval)


def _set_limit_on_interestring_var_if_bound(relation: Relation, var_info: Dict[Var, Var_Monotonicity], is_positive: bool) -> bool:
    """
    Set the hard limit information for a variable if that is the semantics of the given relation.

    Returns:
        True if a variable (hard) bound was set.
    """
    if relation.is_hard_bound():
        var, coef = relation.vars[0], relation.coefs[0]

        if var not in var_info:
            return True  # The relation is a hard bound (True), but the variable is not considered as interestring

        bounds = var_info[var]
        if coef < 0:
            bound_val = math.ceil(relation.rhs / coef)  # -3x <= 1 ---> x >= (-1/3) ---> x is in [0, ...]
            bounds.limits.try_strengthen_lower(bound_val)
        else:
            bound_val = math.floor(relation.rhs / coef)  # 3x <= 1 ---> x <= (1/3) ---> x is in [..., 0]
            bounds.limits.try_strengthen_upper(bound_val)
        return True

    elif relation.specifies_a_single_value_for_var():
        if not is_positive:
            var = relation.vars[0]
            bounds = var_info[var]
            bounds.increasing = True
            bounds.decreasing = True
            return True

        var, coef = relation.vars[0], relation.coefs[0]
        if var not in var_info:
            return True

        bound_val = relation.rhs // coef
        bounds = var_info[var]
        bounds.limits.try_strengthen_lower(bound_val)
        bounds.limits.try_strengthen_upper(bound_val)
        return True
    return False


@dataclass
class Monotonicity_Info:
    are_bounds_unsure: bool = False
    seen_vars: Dict[Var, Var_Monotonicity] = field(default_factory=lambda: defaultdict(Var_Monotonicity))
    congruence_counter: int = 0

    def should_analyse_var(self, var: Var) -> bool:
        return var in self.seen_vars

    def get_next_congruence_id(self) -> int:
        congruence_id = self.congruence_counter
        self.congruence_counter += 1
        return congruence_id


def _determine_monotonicity_of_variables(tree: ASTp_Node, monotonicity_info: Monotonicity_Info, is_positive: bool) -> None:
    match tree:
        case Relation():
            if _set_limit_on_interestring_var_if_bound(tree, monotonicity_info.seen_vars, is_positive):
                return

            for coef, var in tree.linear_terms():
                if not monotonicity_info.should_analyse_var(var):
                    continue

                if tree.predicate_symbol == '=':
                    var_monotonicity = monotonicity_info.seen_vars[var]
                    var_monotonicity.increasing = True
                    var_monotonicity.decreasing = True
                    continue

                if coef < 0:
                    monotonicity_info.seen_vars[var].increasing = True
                else:
                    monotonicity_info.seen_vars[var].decreasing = True

        case Congruence():
            for var_idx, var in enumerate(tree.vars):
                if monotonicity_info.should_analyse_var(var):
                    congruence_idx = monotonicity_info.get_next_congruence_id()
                    monotonicity_info.seen_vars[var].congruences.append((congruence_idx, tree))

        case BoolLiteral() | Var():
            return

        case AST_Connective():
            # The monotonicity analysis is an underapproximation - although different OR branches might
            # imply different variable monotonicity, the result is the same as if traversing through AND
            for child in tree.children:
                _determine_monotonicity_of_variables(child, monotonicity_info, is_positive)

        case AST_Negation():
            # Only thing that we should be able to see at this point is (not <eq>) since all of the negations
            # have been pushed inwards. An equation automatically implies that we do not know the monotonicity
            # of any variable, and therefore, it should be OK to just recurse down.
            _determine_monotonicity_of_variables(tree.child, monotonicity_info, is_positive=(not is_positive))

        case AST_Quantifier():
            for var in tree.bound_vars:
                assert var not in monotonicity_info.seen_vars or monotonicity_info.seen_vars[var] == Var_Monotonicity()
                monotonicity_info.seen_vars[var] = Var_Monotonicity()

            _determine_monotonicity_of_variables(tree.child, monotonicity_info, is_positive=is_positive)

        case _:
            raise ValueError(f'Node not handled when determining monotonicity of variable: {tree=}')


def _substitute_var_with_value(root: ASTp_Node, var: Var, value: Optional[int], contexter: Parent_Context_Var_Values) -> ASTp_Node:
    """ Substitute a *free* variable with a given value (None=inf). """
    match root:
        case Relation() | Congruence():
            if var not in root.vars:
                # Just make a note about the var values asserted here, as other places where the substitution
                # was successful might induce a conflict.
                if isinstance(root, Relation) and len(root.vars) == 1:
                    other_var = root.vars[0]
                    value_interval = contexter.lookup_asserted_values(other_var)
                    value_interval.apply_assertion(root)
                    contexter.assert_new_var_value(other_var, value_interval)
                return root

            if value is None:
                return BoolLiteral(True)

            new_coefs, new_vars = [], []
            var_coef = 1
            for other_coef, other_var in root.linear_terms():
                if other_var == var:
                    var_coef = other_coef
                    continue
                new_coefs.append(other_coef)
                new_vars.append(other_var)

            new_rhs = root.rhs - var_coef*value

            if not new_vars:
                if isinstance(root, Relation):
                    ret = BoolLiteral(True) if new_rhs >= 0 else BoolLiteral(False)
                    return ret
                else:  # root is a Congruence
                    ret = BoolLiteral(True) if (new_rhs % root.modulus) == 0 else BoolLiteral(False)
                    return ret

            if isinstance(root, Congruence):
                new_congruence = Congruence(vars=new_vars, coefs=new_coefs, rhs=(new_rhs % root.modulus), modulus=root.modulus)
                return new_congruence

            coefs_gcd = math.gcd(*new_coefs)
            if root.predicate_symbol == '=' and (new_rhs % coefs_gcd) != 0:
                # Unsat, e.g., 3x = 4 does not have a solution in integers
                return BoolLiteral(False)

            new_rhs = math.floor(new_rhs / coefs_gcd)
            new_coefs = [coef // coefs_gcd for coef in new_coefs]
            relation = Relation(vars=new_vars, coefs=new_coefs, rhs=new_rhs, predicate_symbol=root.predicate_symbol)

            strengthened = False
            if relation.is_hard_bound():
                bound_type, affected_var, bound_val = get_hard_bound_semantics(relation)
                value_interval = contexter.lookup_asserted_values(affected_var)
                if bound_type == Bound_Type.LOWER:
                    value_interval.try_strengthen_lower(bound_val)
                else:
                    value_interval.try_strengthen_upper(bound_val)

            elif relation.specifies_a_single_value_for_var():
                affected_var = relation.vars[0]
                implied_val = relation.rhs // relation.coefs[0]  # We know that coefs divides rhs because otherwise we would already returned False
                value_interval = contexter.lookup_asserted_values(affected_var)
                value_interval.try_strengthen_lower(implied_val)
                value_interval.try_strengthen_upper(implied_val)

            else:
                return relation

            # We have strengthened the intervals, check whether we did not found any conflict after substitution
            if value_interval.implies_contradiction():
                return BoolLiteral(False)
            return relation

        case BoolLiteral() | Var():
            return root

        case AST_Connective():
            def subst_value_with_separate_context(node: ASTp_Node, var: Var, value: Optional[int], contexter: Parent_Context_Var_Values) -> ASTp_Node:
                contexter.enter_context()
                result = _substitute_var_with_value(node, var, value, contexter)
                contexter.exit_context()
                return result

            if root.type == Connective_Type.AND:
                # If we have an AND node then the subtrees can share asserted values (if a subtree asserts that x=5 then x=5 must hold in all other subtrees)
                contexter.enter_context()
                _subst_children = (_substitute_var_with_value(child, var, value, contexter) for child in root.children)
                subst_children = tuple(child for child in _subst_children if child is not None)
                contexter.exit_context()
            else:
                _subst_children = (subst_value_with_separate_context(child, var, value, contexter) for child in root.children)
                subst_children = tuple(child for child in _subst_children if child is not None)

            subst_children = _use_bool_laws_to_simplify_connective_plain(root.type, subst_children)
            if len(subst_children) == 1:
                return subst_children[0]

            return root.replace_children(subst_children)

        case AST_Quantifier():
            new_child = _substitute_var_with_value(root.child, var, value, contexter)
            if isinstance(new_child, BoolLiteral):
                return new_child
            new_bound_vars = root.bound_vars if var not in root.bound_vars else tuple(it for it in root.bound_vars if it != var)
            return AST_Quantifier(referenced_vars=root.referenced_vars, bound_vars=new_bound_vars, child=new_child)

        case AST_Negation():
            contexter.enter_blocking_context()

            new_child = _substitute_var_with_value(root.child, var, value, contexter)

            if new_child == BoolLiteral(True):
                return BoolLiteral(False)
            elif new_child == BoolLiteral(False):
                return BoolLiteral(True)
            elif isinstance(new_child, Relation) and new_child.predicate_symbol == '<=':
                return new_child.negate()

            contexter.exit_context()
            return AST_Negation(referenced_vars=root.referenced_vars, child=new_child)

        case _:
            raise ValueError(f'Invalid substitution. Trying substitute {var} := {value} into {type(root)}')


def _do_bounds_imply_conflict(var_info: Var_Monotonicity) -> bool:
    if var_info.limits.lower_limit is None or var_info.limits.upper_limit is None:
        return False

    return var_info.limits.upper_limit < var_info.limits.lower_limit


@dataclass
class Rewrite_Info:
    result: ASTp_Node
    rewrite_happend: bool = False
    should_continue: bool = True  # Contains meaningful value only when rewrite_happend=True
    quantifier_present: bool = True  # Contains meaningful value only when rewrite_happend=True


def _rewrite_exists_equations(exists_node: AST_Quantifier) -> Optional[Tuple[ASTp_Node, bool]]:
    if not isinstance(exists_node.child, Relation):
        return None

    bound_vars = exists_node.bound_vars
    rel = exists_node.child
    if rel.predicate_symbol == '=':
        bound_vars_coefs = []
        for coef, var in rel.linear_terms():
            if var in bound_vars:
                bound_vars_coefs.append(coef)
        gcd = math.gcd(*bound_vars_coefs)
        if not bound_vars_coefs:
            return rel, False
        if gcd == 1:
            return BoolLiteral(True), False
    else:
        if any(bound_var in rel.vars for bound_var in bound_vars):
            return BoolLiteral(True), False
        else: # Inequation that does not speak about the quantified variable.
            return exists_node.child, False
    return None


def _rewrite_surjective_transformations(exists_node: AST_Quantifier) -> Rewrite_Info:
    if not isinstance(exists_node.child, AST_Connective) or exists_node.child.type != Connective_Type.AND:
        return Rewrite_Info(result=exists_node, rewrite_happend=False)

    and_node: AST_Connective = exists_node.child

    if not all(isinstance(subtree, Relation) for subtree in and_node.children):
        return Rewrite_Info(result=exists_node, rewrite_happend=False)

    # E(x1) (x1 >= 0 /\ x1 - 5x2 \in [0, 4])    <-->  x2 >= 0    [IMPLEMENTED]
    # E(x2) (x2 >= 0 /\ x1 - 5x2 \in [K, K+4])  <-->  x1 >= K    [NOT IMPLEMENTED]
    # E(x1) (x1 >= 0 /\ x1  = 5x2)            <-->  True
    # E(x1) (x1 >= 0 /\ 5x1 = x2)             <-->  (x2 = 0 mod 5) /\ x2 >= 0
    Linear_Term = Tuple[int, Var]
    for bound_var in exists_node.bound_vars:

        bound_var_value = Value_Interval()

        dependencies: Dict[Var, List[int]] = defaultdict(list)

        is_surjection = False

        relations: Tuple[Relation,...] = and_node.children  # type: ignore
        for subtree_idx, subtree in enumerate(relations):
            assert isinstance(subtree, Relation)
            if not bound_var in subtree.vars:
                continue

            if subtree.is_hard_bound():
                bound_type, _, bound_val = get_hard_bound_semantics(subtree)
                if bound_type == Bound_Type.LOWER:
                    bound_var_value.try_strengthen_lower(bound_val)
                else:
                    bound_var_value.try_strengthen_upper(bound_val)
                continue

            for var in subtree.vars:
                if var == bound_var:
                    continue
                dependencies[var].append(subtree_idx)

        is_fin = (bound_var_value.upper_limit is not None) and (bound_var_value.lower_limit is not None)
        if is_fin:
            continue

        if len(dependencies) > 1:
            # @Incomplete: There are multiple variables dependent on this one...
            # but I am not sure whether there can be any simplification done.
            # maybe we could do something better than nothing.
            continue

        rels_to_replace: List[Tuple[List[int], List[ASTp_Node]]] = []
        for dependent_var, relation_indices in dependencies.items():
            if not len(relation_indices) == 2:
                continue

            rel1, rel2 = relations[relation_indices[0]], relations[relation_indices[1]]

            if rel1.predicate_symbol != '<=' or rel2.predicate_symbol != '<=':
                continue

            rel1_terms = tuple(rel1.linear_terms())
            rel2_terms = tuple(rel2.linear_terms())
            rel2_terms_negated = tuple((-it[0], it[1]) for it in rel2_terms)

            are_terms_complementary = rel1_terms == rel2_terms_negated
            if not are_terms_complementary or len(rel1_terms) > 2:
                continue

            bound_var_idx = rel1.vars.index(bound_var)
            dep_var_idx = 1 - bound_var_idx
            pos, neg = rel1, rel2

            if abs(pos.coefs[bound_var_idx]) == 1:  #  E(x1) (x1 >= 0 /\ x1 - 5x2 \in [0, 4])    <-->  x2 >= 0
                if pos.coefs[bound_var_idx] == -1:
                    pos, neg = neg, pos

                # pos :=  1x + k*<neg> <= Z1,
                # neg := -1x - k*<neg> <= Z2,
                value_interval = Value_Interval(lower_limit=neg.rhs, upper_limit=pos.rhs)
                if value_interval.lower_limit != 0:
                    continue

                other_var_coef = pos.coefs[dep_var_idx]

                if value_interval.upper_limit != (-other_var_coef) - 1:
                    continue

                new_bounds: List[ASTp_Node] = list(bound_var_value.synthetize_atoms(rel1.vars[dep_var_idx]))
                rels_to_replace.append((relation_indices, new_bounds))

            elif abs(pos.coefs[dep_var_idx]) == 1:  #  E(x2) (x2 >= 0 /\ x1 - 5x2 \in [K, K+4])  <-->  x1 >= K
                if pos.coefs[dep_var_idx] == -1:  # Pos looks like 5x2 - x1, swap so pos would be x1 - 5x2
                    pos, neg = neg, pos

                # pos :=  1x - 5x2 <= Z1,
                # neg := -1x - 5x2 <= Z2    <=>   1x + 5x2 >= -Z2
                value_interval_width = pos.rhs + neg.rhs + 1# -(-Z2); +1 because range is inclusive, i.e., [a,a] contains 1 number
                bound_var_coef = -pos.coefs[bound_var_idx]

                if value_interval_width != bound_var_coef:
                    continue

                if not bound_var_value.lower_limit and not bound_var_value.upper_limit:
                    #  E(x2) (x1 - 5x2 \in [K, K+4]) - says nothing about the value of free variable
                    rels_to_replace.append((relation_indices, []))
                    continue

                if bound_var_value.lower_limit != 0 or bound_var_value.upper_limit is not None:
                    continue

                dep_var = pos.vars[dep_var_idx]
                implied_bound = Relation(vars=[dep_var], coefs=[-1], rhs=neg.rhs, predicate_symbol='<=')

                rels_to_replace.append((relation_indices, [implied_bound]))

        added_subformulae: List[ASTp_Node] = []
        removed_subformulae_indices: List[int] = []
        for thrown_out_atom_indices, new_atoms in rels_to_replace:
            removed_subformulae_indices.extend(thrown_out_atom_indices)
            added_subformulae.extend(new_atoms)

        kept_relations: Tuple[ASTp_Node,...] = tuple(subtree for subtree_idx, subtree in enumerate(relations) if subtree_idx not in removed_subformulae_indices)
        new_node_subtrees = kept_relations + tuple(added_subformulae)
        if not new_node_subtrees:
            new_node_subtrees = (BoolLiteral(True),)

        new_connective = AST_Connective(referenced_vars=and_node.referenced_vars, type=and_node.type, children=new_node_subtrees)

        result = AST_Quantifier(referenced_vars=exists_node.referenced_vars,
                                bound_vars=exists_node.bound_vars,
                                child=new_connective if len(new_connective.children) > 1 else new_connective.children[0])

        return Rewrite_Info(result=result, rewrite_happend=True, should_continue=True, quantifier_present=True)

    return Rewrite_Info(result=exists_node, rewrite_happend=False, should_continue=True, quantifier_present=True)


@dataclass
class Exists_Optimization_Result:
    node: ASTp_Node
    contains_quantifier: bool
    contains_rewritable_congruence: bool = False
    vars_to_rewrite_congruences_with: List[Var] = field(default_factory=list)


def _optimize_congruences_on_unbound_vars(root: ASTp_Node, opt_result: Exists_Optimization_Result) -> ASTp_Node:
    def filter_our_referenced_vars(referenced_vars: Tuple[Var, ...]) -> Tuple[Var, ...]:
        return tuple(var for var in referenced_vars if var not in opt_result.vars_to_rewrite_congruences_with)

    match root:
        case Relation():
            if any(var in root.vars for var in opt_result.vars_to_rewrite_congruences_with):
                return BoolLiteral(True)
            return root
        case Congruence():
            usable_terms: List[LinTerm] = [LinTerm(coef=term[0], var=term[1]) for term in root.linear_terms() if term[1] in opt_result.vars_to_rewrite_congruences_with]
            terms_gcd = math.gcd(*(term.coef for term in usable_terms))
            new_modulus = math.gcd(root.modulus, terms_gcd)

            new_terms = [term for term in root.linear_terms() if term[1] not in opt_result.vars_to_rewrite_congruences_with]
            coefs = [term[0] for term in new_terms]
            vars  = [term[1] for term in new_terms]

            if not vars:
                return BoolLiteral(True)

            return Congruence(vars=vars, coefs=coefs, modulus=new_modulus, rhs=(root.rhs % new_modulus))
        case Var():
            return root
        case AST_Connective():
            rewritten_children = (_optimize_congruences_on_unbound_vars(child, opt_result) for child in root.children)
            referenced_vars = filter_our_referenced_vars(root.referenced_vars)
            return AST_Connective(referenced_vars=referenced_vars, type=Connective_Type.AND, children=tuple(rewritten_children))
        case AST_Quantifier():
            optimized_child = _optimize_congruences_on_unbound_vars(root.child, opt_result)
            bound_vars = tuple(var for var in root.bound_vars if var not in opt_result.vars_to_rewrite_congruences_with)
            if not bound_vars:
                return optimized_child
            if isinstance(optimized_child, BoolLiteral):
                return optimized_child
            referenced_vars = filter_our_referenced_vars(root.referenced_vars)
            return AST_Quantifier(referenced_vars=referenced_vars, bound_vars=bound_vars, child=optimized_child)
        case AST_Negation():
            optimized_child = _optimize_congruences_on_unbound_vars(root.child, opt_result)
            referenced_vars = filter_our_referenced_vars(root.referenced_vars)
            return AST_Negation(referenced_vars=referenced_vars, child=optimized_child)
        case _:
            raise ValueError('Unhandled node while optimizing congruences on unbound variables.')


def optimize_congruences_on_unbound_vars(root: ASTp_Node, opt_result: Exists_Optimization_Result) -> Exists_Optimization_Result:
    optimized_tree = _optimize_congruences_on_unbound_vars(root, opt_result)
    contains_quantifier = isinstance(root, AST_Quantifier)
    return Exists_Optimization_Result(node=optimized_tree, contains_quantifier=contains_quantifier)


def _optimize_exists_tree(exists_node: AST_Quantifier) -> Exists_Optimization_Result:
    """
    Optimize the structure of exists (X) where X is quantifier free.

    Returns:
        - A possibly optimized X
        - True if any quantifier lingers (is still present)
    """

    # Apply specific rewrite rules
    logger.debug('Optimizing exists tree: %s', exists_node)
    if (rewrite_info := _rewrite_exists_equations(exists_node)):
        return Exists_Optimization_Result(node=rewrite_info[0], contains_quantifier=rewrite_info[1])

    rewrite_info = _rewrite_surjective_transformations(exists_node)
    if rewrite_info.rewrite_happend:
        if not rewrite_info.should_continue:
            return Exists_Optimization_Result(rewrite_info.result, contains_quantifier=rewrite_info.quantifier_present)

        assert rewrite_info.quantifier_present
        assert isinstance(rewrite_info.result, AST_Quantifier)

        exists_node = rewrite_info.result

    monotonicity_info = Monotonicity_Info()
    _determine_monotonicity_of_variables(exists_node, monotonicity_info, is_positive=True)

    vars_to_instantiate: List[Tuple[Var, int | None]] = []
    contains_optimizable_congruences: bool = False
    vars_to_optimize_congruences_with: List[Var] = []
    for var, var_monotonicity in monotonicity_info.seen_vars.items():
        if _do_bounds_imply_conflict(var_monotonicity):
            return Exists_Optimization_Result(node=BoolLiteral(False), contains_quantifier=False)

        if var_monotonicity.limits.upper_limit == var_monotonicity.limits.lower_limit and var_monotonicity.limits.lower_limit is not None:
            logger.info(f'The variable {var} has a known value {var_monotonicity.limits.upper_limit}')
            # The variable has a known value so we can instantiate it regardless of its context
            vars_to_instantiate.append((var, var_monotonicity.limits.upper_limit))
            continue

        is_variable_in_other_atoms = var_monotonicity.increasing or var_monotonicity.decreasing
        is_direction_of_optimal_value_known = (var_monotonicity.increasing != var_monotonicity.decreasing)
        if not is_direction_of_optimal_value_known and is_variable_in_other_atoms:
            continue  # Some atoms would like the variable to be large, some would like it to be small...

        var_causes_nonlinearities = len(var_monotonicity.congruences) > 0
        if is_direction_of_optimal_value_known and not var_causes_nonlinearities:
            optimal_value = var_monotonicity.limits.upper_limit if var_monotonicity.increasing else var_monotonicity.limits.lower_limit
            vars_to_instantiate.append((var, optimal_value))
            continue

        # Assess whether the variable can be inf in a suitable direction - then we can deal with one Congruence
        var_has_limited_nonlinearity = len(var_monotonicity.congruences) == 1
        can_be_pos_inf = (not var_monotonicity.decreasing) and var_monotonicity.limits.upper_limit is None
        can_be_neg_inf = (not var_monotonicity.increasing) and var_monotonicity.limits.lower_limit is None
        can_be_inf = can_be_pos_inf or can_be_neg_inf

        if can_be_inf and var_has_limited_nonlinearity:
            congruence_idx, congruence = var_monotonicity.congruences[0]
            var_idx = congruence.vars.index(var)
            coef = (-congruence.coefs[var_idx] + congruence.modulus) % congruence.modulus  # Move x to the other side
            new_mod = gcd(coef, congruence.modulus)
            if gcd(coef, congruence.modulus) == 1:
                vars_to_instantiate.append((var, None))
            else:
                contains_optimizable_congruences = True
                vars_to_optimize_congruences_with.append(var)

        if not is_variable_in_other_atoms and len(var_monotonicity.congruences) == 0 and can_be_inf:  # Var has only limits of the type \exists x (x >= 10 AND x >= 20), so it can be instantiated with -infty
            vars_to_instantiate.append((var, None))

    optimized_tree_child = exists_node.child
    if vars_to_instantiate:
        for var, var_value in vars_to_instantiate:
            var_info   = monotonicity_info.seen_vars[var]
            logger.debug('Substituting %s=%s into the exists tree', var, var_value)
            fixed_tree = _substitute_var_with_value(optimized_tree_child, var, var_value, Parent_Context_Var_Values())
            logger.debug('Fixed tree: %s', fixed_tree)
            if not fixed_tree:
                return Exists_Optimization_Result(node=BoolLiteral(True), contains_quantifier=False)
            optimized_tree_child = fixed_tree

        quantifier_lingers = len(exists_node.bound_vars) - len(vars_to_instantiate) > 0

        instantiated_vars: Set[Var] = set(var for var, _ in vars_to_instantiate)
        remaining_quantified_vars: Tuple[Var, ...] = tuple(sorted(set(exists_node.bound_vars) - instantiated_vars))
        if remaining_quantified_vars:
            referenced_vars = tuple(set(exists_node.referenced_vars) - instantiated_vars)
            optimized_tree = AST_Quantifier(referenced_vars=referenced_vars, bound_vars=remaining_quantified_vars, child=optimized_tree_child)
        else:
            optimized_tree = optimized_tree_child  # All variables have been instantiated; remove the quantifier node

        logger.debug('Result: %s', optimized_tree)
        return Exists_Optimization_Result(node=optimized_tree,
                                          contains_quantifier=quantifier_lingers,
                                          contains_rewritable_congruence=contains_optimizable_congruences,
                                          vars_to_rewrite_congruences_with=vars_to_optimize_congruences_with)

    logger.debug('Did not perform any modification to the tree.')
    return Exists_Optimization_Result(node=exists_node,
                                      contains_quantifier=True,
                                      contains_rewritable_congruence=contains_optimizable_congruences,
                                      vars_to_rewrite_congruences_with=vars_to_optimize_congruences_with)


def _optimize_exists_tree_using_const_values_only(exists_node: AST_Quantifier) -> Tuple[ASTp_Node, bool]:
    is_exists_and_tree = isinstance(exists_node.child, AST_Connective) and exists_node.child.type == Connective_Type.AND
    if not is_exists_and_tree:
        return exists_node, True

    bound_vars = exists_node.bound_vars

    assert isinstance(exists_node.child, AST_Connective)
    and_node: AST_Connective = exists_node.child

    substitutions_to_make: List[Tuple[Var, int]] = []
    for subtree in and_node.children:
        if not isinstance(subtree, Relation):
            continue
        if not subtree.specifies_a_single_value_for_var():
            continue

        var = subtree.vars[0]
        if var not in bound_vars:
            continue

        coef = subtree.coefs[0]

        if (subtree.rhs % coef) != 0:
            return BoolLiteral(False), False

        implied_val = subtree.rhs // coef
        substitutions_to_make.append((var, implied_val))

    if not substitutions_to_make:
        return exists_node, True

    result: ASTp_Node = exists_node
    for var, value in substitutions_to_make:
        new_node = _substitute_var_with_value(result, var, value, Parent_Context_Var_Values())
        result = new_node

    if isinstance(result, AST_Quantifier) and not result.bound_vars:
        return result.child, True

    any_quantifier_lingers = len(bound_vars) > len(substitutions_to_make)
    return result, True


def _apply_bound_based_theory_reasoning(connective_type: Connective_Type,
                                        connective_children: Tuple[Tuple[ASTp_Node, bool], ...]) -> Tuple[Tuple[ASTp_Node, bool], ...]:
    """
    Params:
        - connective_children: Children of the connective that is being rewritten
                               with True iff they contain a quantifier.
    """
    if connective_type != Connective_Type.AND:
        return connective_children

    var_bounds: Dict[Var, Value_Interval] = defaultdict(Value_Interval)
    var_singular_congruences: Dict[Var, List[int]] = defaultdict(list)

    untouched_subtrees_mask: List[bool] = [True] * len(connective_children)

    for child_idx, child_info in enumerate(connective_children):
        child, does_child_contain_quantifier = child_info
        if isinstance(child, Congruence) and len(child.vars) == 1:
            var = child.vars[0]
            var_singular_congruences[var].append(child_idx)
            continue

        if not isinstance(child, Relation) or len(child.vars) > 1:
            continue

        var = child.vars[0]
        bounds = var_bounds[var]

        if child.is_hard_bound():
            bound_type, _, bound_value = get_hard_bound_semantics(child)
            if bound_type == Bound_Type.LOWER:
                bounds.try_strengthen_lower(bound_value)
            else:
                bounds.try_strengthen_upper(bound_value)
            untouched_subtrees_mask[child_idx] = False  # The atom has been consumed

        elif child.specifies_a_single_value_for_var():
            if child.is_unsat_eq():
                return ((BoolLiteral(False), False), )

            implied_val = child.rhs // child.coefs[0]
            bounds.try_strengthen_lower(implied_val)
            bounds.try_strengthen_upper(implied_val)
            untouched_subtrees_mask[child_idx] = False  # The atom has been consumed

        if bounds.lower_limit is None or bounds.upper_limit is None:
            continue

        if bounds.implies_contradiction():
            return ((BoolLiteral(False), False), )

    new_bounds = []
    for var, bound in var_bounds.items():
        is_fin = bound.lower_limit is not None and bound.upper_limit is not None
        var_congruences = var_singular_congruences[var]
        if is_fin and var_congruences:
            upper_bound: int = cast(int, bound.upper_limit)
            lower_bound: int = cast(int, bound.lower_limit)

            implied_var_values: Tuple[int, int] | None = None
            for congruence_idx in var_congruences:
                _congruence, _ = connective_children[congruence_idx]
                congruence = cast(Congruence, _congruence)
                if not congruence.is_normalized():
                    congruence = congruence.normalize()
                if not congruence:  # The congruence could not be normalized
                    continue

                # Congruence has the form 1*x = K (mod M)                <->  x = M*l + K
                # Bounds give restriction on x values: x_bound = [a, b]  <->  x >= a AND x <= b
                # Substitute x in the lower bound:                        ::  M*l + K >= a  <->  l >= (a - K) / M  <->  l >= math.ceil((a - K) / M)
                # Substitute x in the upper bound:                        ::  M*l + K <= b  <->  l <= (b - K) / M  <->  l <= math.floor((b - K) / M)
                smallest_solution = math.ceil((lower_bound-congruence.rhs) / congruence.modulus)
                largest_solution  = math.floor((upper_bound-congruence.rhs) / congruence.modulus)

                # smallest_solution and largest_solution talk in terms of multiplies of M, turn it back into x
                smallest_solution = smallest_solution*congruence.modulus + congruence.rhs
                largest_solution  = largest_solution*congruence.modulus + congruence.rhs

                if not implied_var_values:
                    implied_var_values = (smallest_solution, largest_solution)
                else:
                    new_smallest_solution = max(smallest_solution, implied_var_values[0])
                    new_largest_solution = min(largest_solution, implied_var_values[1])
                    implied_var_values = (new_smallest_solution, new_largest_solution)
                logger.debug('Congruence solving for %s - implied var values: %s', var, implied_var_values)

            if not implied_var_values:
                continue

            if implied_var_values[0] > implied_var_values[1]:
                logger.info('Detected conflict via congruence solving on variable: %s', var)
                congruences = [connective_children[congruence_idx][0] for congruence_idx in var_congruences]
                logger.info('%s has finite range: [%d, %d] and the following congruences: %s', var, lower_bound, upper_bound, congruences)
                return ((BoolLiteral(False), False),)

            if implied_var_values[0] == implied_var_values[1]:
                logger.info('Detected only single possible value for variable %s via congruence solving', var)
                congruences = [connective_children[congruence_idx][0] for congruence_idx in var_congruences]
                logger.info('%s has finite range: [%d, %d] and the following congruences: %s', var, lower_bound, upper_bound, congruences)

                implied_value = implied_var_values[0]
                bound.lower_limit = implied_value
                bound.upper_limit = implied_value

        new_bounds.extend((bound, False) for bound in bound.synthetize_atoms(var))

    untouched_subtrees = (child for child_idx, child in enumerate(connective_children) if untouched_subtrees_mask[child_idx])
    result = tuple(new_bounds) + tuple(untouched_subtrees)
    return result


def _use_bool_laws_to_simplify_connective(connective_type: Connective_Type,
                                          subtrees: Tuple[Tuple[ASTp_Node, bool], ...]) -> Tuple[Tuple[ASTp_Node, bool], ...]:
    """
    Use idempotence and anihilation to simplify the connective subtrees.

    Params:
        - subtress - connective subtrees together with True iff they contain a quantifier

    Returns:
        - simplified subtrees (Bool literals are filtered out) with information about quantifier presense
    """
    if connective_type == Connective_Type.EQUIV:
        return subtrees

    if connective_type == Connective_Type.AND:
        neutral_elem = BoolLiteral(True)
        zero_elem    = BoolLiteral(False)
    else:
        neutral_elem = BoolLiteral(False)
        zero_elem    = BoolLiteral(True)

    if any(it[0] == zero_elem for it in subtrees):
        return (zero_elem, False),

    result = tuple(it for it in subtrees if it[0] != neutral_elem)
    if len(result) == 0:
        return ((neutral_elem, False), )
    return result


def _use_bool_laws_to_simplify_connective_plain(connective_type: Connective_Type,
                                                subtrees: Tuple[ASTp_Node, ...]) -> Tuple[ASTp_Node, ...]:
    """
    Use idempotence and anihilation to simplify the connective subtrees.
    """
    if connective_type == Connective_Type.EQUIV:
        return subtrees

    if connective_type == Connective_Type.AND:
        neutral_elem = BoolLiteral(True)
        zero_elem = BoolLiteral(False)
    else:
        neutral_elem = BoolLiteral(False)
        zero_elem = BoolLiteral(True)

    if zero_elem in subtrees:
        return (zero_elem,)

    result = tuple(it for it in subtrees if it != neutral_elem)
    if len(result) == 0:
        return (neutral_elem, )
    return result


def _shallow_flatten_connective(connective_type: Connective_Type,
                                connective_children: Tuple[Tuple[ASTp_Node, bool], ...]) -> Tuple[Tuple[ASTp_Node, bool], ...]:
    flattened_children: List[Tuple[ASTp_Node, bool]] = []

    for child, contains_quantifier in connective_children:
        if isinstance(child, AST_Connective) and child.type == connective_type:
            flattened_children.extend((ch, contains_quantifier) for ch in child.children)
        else:
            flattened_children.append((child, contains_quantifier))

    return tuple(flattened_children)


def _optimize_bottom_quantifiers(root: ASTp_Node) -> Tuple[ASTp_Node, bool]:
    match root:
        case Relation() | Congruence() | Var() | BoolLiteral():
            return root, False

        case AST_Connective():
            is_and_connective = root.type == Connective_Type.AND
            _optimized_subtrees = tuple(_optimize_bottom_quantifiers(child) for child in root.children)
            _optimized_subtrees = _shallow_flatten_connective(root.type, _optimized_subtrees)

            _optimized_subtrees = _apply_bound_based_theory_reasoning(root.type, _optimized_subtrees)
            _optimized_subtrees = _use_bool_laws_to_simplify_connective(root.type, _optimized_subtrees)

            optimized_subtrees = tuple(it[0] for it in _optimized_subtrees)
            any_quantifier_lingers: bool = functools.reduce(lambda a, b: a or b, (it[1] for it in _optimized_subtrees), False)
            if len(optimized_subtrees) == 1:
                return optimized_subtrees[0], any_quantifier_lingers

            new_node = AST_Connective(referenced_vars=root.referenced_vars,
                                      type=root.type,
                                      children=optimized_subtrees,
                                      variable_bounds=root.variable_bounds)

            return (new_node, any_quantifier_lingers or not is_and_connective)

        case AST_Negation():
            optimized_child, any_quantifier_present = _optimize_bottom_quantifiers(root.child)
            if optimized_child == BoolLiteral(True):
                return BoolLiteral(False), False
            elif optimized_child == BoolLiteral(False):
                return BoolLiteral(True), False
            elif isinstance(optimized_child, Relation) and optimized_child.predicate_symbol == '<=':
                return optimized_child.negate(), False

            new_node = AST_Negation(referenced_vars=root.referenced_vars, child=optimized_child)

            return new_node, any_quantifier_present

        case AST_Quantifier():
            optimized_child, subtree_contains_quantifiers = _optimize_bottom_quantifiers(root.child)
            new_node = AST_Quantifier(referenced_vars=root.referenced_vars, bound_vars=root.bound_vars, child=optimized_child)

            if subtree_contains_quantifiers:
                # return new_node, subtree_contains_quantifiers
                new_node, this_quantifier_present = _optimize_exists_tree_using_const_values_only(new_node)
                return new_node, subtree_contains_quantifiers or this_quantifier_present

            exist_opt_result = _optimize_exists_tree(new_node)
            if exist_opt_result.contains_rewritable_congruence:
                exist_opt_result = optimize_congruences_on_unbound_vars(exist_opt_result.node, exist_opt_result)
            return exist_opt_result.node, exist_opt_result.contains_quantifier

        case _:
            raise NotImplementedError(f'Unhandled node while optimizing bottom quantifiers {root=}.')


def optimize_bottom_quantifiers(root: ASTp_Node) -> ASTp_Node:
    optimized_tree, _ = _optimize_bottom_quantifiers(root)
    return optimized_tree


def _interval_length(interval: Tuple[int, int]) -> int:
    return interval[1] - interval[0] + 1


def _strenghten_value_intervals(congruence: Congruence, value_intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not all(abs(coef) == 1 for coef in congruence.coefs):
        return value_intervals

    def interval_length(interval: Tuple[int, int]) -> int:
        return interval[1] - interval[0] + 1

    smaller_i, larger_i = value_intervals
    smaller_var_i, larger_var_i = 0, 1

    if interval_length(smaller_i) > interval_length(larger_i):
        smaller_i, larger_i = larger_i, smaller_i
        smaller_var_i, larger_var_i = larger_var_i, smaller_var_i

    if interval_length(smaller_i) >= congruence.modulus:
        return value_intervals # The intervals cannot be strenghtened

    def _solve_congruence_for_value(var_idx: int, var_value: int, value_interval: Tuple[int, int]):
        rhs = congruence.rhs - congruence.coefs[var_idx] * var_value
        rhs %= congruence.modulus
        if rhs < 0:
            rhs += congruence.modulus

        other_var_idx = 1 - var_idx
        other_var_coef = congruence.coefs[other_var_idx]

        if other_var_coef < 0:  # Multiply the congruence by -1
            rhs *= -1
            rhs += congruence.modulus

        # RHS is curently in [0, ... Modulus], shift it into the required interval
        shift_times = math.floor(value_interval[0]/congruence.modulus)
        shifted_val = rhs + shift_times*congruence.modulus
        if shifted_val < value_interval[0]:
            shifted_val += congruence.modulus

        return shifted_val

    raise NotADirectoryError('Interval strenghtening is not implemented yet.')
    return []



@dataclass
class Linearized_Var_Spec:
    var: Var
    idx: int
    coef: int
    interval: Tuple[int, int]


def _should_linearize(x_var_spec: Linearized_Var_Spec, y_var_spec: Linearized_Var_Spec, congruence: Congruence, x_stride: fractions.Fraction) -> bool:
    if abs(y_var_spec.coef) != 1:
        return False  # Both variables have a |coefficient| > 1 which requires a complex tiling of the 2D space

    if abs(x_var_spec.interval[1] - x_var_spec.interval[0]) / x_stride > 4:
        return False  # Linearization would create a very large disjunction

    if _interval_length(y_var_spec.interval) > congruence.modulus:
        return False  # We can linearize, but we give up (likely too many disjuncts would be created)

    return True


def _attempt_congruence_linearization(congruence: Congruence, contexter: Parent_Context_Var_Values, monotonicity: Monotonicity_Info) -> AST_Connective | None:
    if len(congruence.vars) != 2:
        return None

    var_ranges: List[Tuple[int, int]] = []

    can_linearize = True

    for var in congruence.vars:
        # Check if the variable domain is explicitely finite
        var_bounds = contexter.lookup_asserted_values(var)
        is_fin = var_bounds.lower_limit is not None and var_bounds.upper_limit is not None
        if is_fin:
            assert var_bounds.lower_limit is not None
            assert var_bounds.upper_limit is not None

            var_ranges.append((var_bounds.lower_limit, var_bounds.upper_limit))
            continue

        # Check if the variable domain is implicitly finite because of monotonicity
        var_monotonicity = monotonicity.seen_vars.get(var, Var_Monotonicity())

        if var_monotonicity.increasing and var_monotonicity.decreasing:
            can_linearize = False
            break

        is_c_best_from_below = var_bounds.upper_limit is not None and var_monotonicity.increasing
        if is_c_best_from_below:
            assert var_bounds.upper_limit
            value_interval = (var_bounds.upper_limit-congruence.modulus+1, var_bounds.upper_limit)
            var_ranges.append(value_interval)
            continue

        is_c_best_from_above = var_bounds.lower_limit is not None and var_monotonicity.decreasing
        if is_c_best_from_above:
            assert var_bounds.lower_limit
            value_interval = (var_bounds.lower_limit, var_bounds.lower_limit+congruence.modulus-1)
            var_ranges.append(value_interval)
            continue

        can_linearize = False
        break

    if not can_linearize:
        return None

    # y_coef*y + x_coef*x = K --> move X to the other side, and multiply by inverse(y_coef) to get  y =  x_coef' * x + K'
    x_var_spec = Linearized_Var_Spec(var=congruence.vars[0], idx=0, coef=-congruence.coefs[0], interval=var_ranges[0])
    y_var_spec = Linearized_Var_Spec(var=congruence.vars[1], idx=1, coef=congruence.coefs[1], interval=var_ranges[1])

    y_coef_inverse = pow(y_var_spec.coef, -1, congruence.modulus)

    if y_coef_inverse == 0:
        return None

    y_var_spec.coef = 1
    x_var_spec.coef = (x_var_spec.coef * y_coef_inverse) % congruence.modulus
    rhs = (congruence.rhs*y_coef_inverse) % congruence.modulus

    leftmost_x = x_var_spec.interval[0]
    x_stride = fractions.Fraction(congruence.modulus, x_var_spec.coef)

    if not _should_linearize(x_var_spec, y_var_spec, congruence, x_stride):
        return None

    try:
        _x_inv = pow(-x_var_spec.coef, -1, congruence.modulus) % congruence.modulus
        first_zero = fractions.Fraction((rhs * _x_inv) % congruence.modulus, 1)
    except ValueError:
        # -<x_coef>*x = rhs
        if rhs % (x_var_spec.coef) == 0:
            first_zero_val = rhs / -x_var_spec.coef
            first_zero = fractions.Fraction(first_zero_val)
        else:
            return None

    first_zero_distance = leftmost_x*x_var_spec.coef - first_zero
    strides_from_first_zero = first_zero_distance / x_stride

    x_below = first_zero + math.floor(strides_from_first_zero) * x_stride
    x_below = fractions.Fraction(x_below, x_var_spec.coef)
    x_above = x_below + x_stride

    # Calculate the offset as a distance from origin which has offset -rhs'
    first_offset = -first_zero - math.floor(strides_from_first_zero) * x_stride

    def emit_branch(branches: List[AST_Connective], x_start: fractions.Fraction, x_end: fractions.Fraction, offset: fractions.Fraction):
        lower_bound = Relation(vars=[x_var_spec.var], coefs=[-x_start.denominator], rhs=-x_start.numerator, predicate_symbol='<=')
        upper_bound = Relation(vars=[x_var_spec.var], coefs=[x_end.denominator], rhs=x_end.numerator-1, predicate_symbol='<=')
        fn = Relation(vars=[x_var_spec.var, y_var_spec.var], coefs=[x_var_spec.coef*offset.denominator, -1*offset.denominator], rhs=-offset.numerator, predicate_symbol='=')
        branches.append(AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND, children=(lower_bound, upper_bound, fn)))

    branches: List[AST_Connective] = []
    emit_branch(branches, x_below, x_above, first_offset)

    # At every iteration [start, end] when we reach end, we need to make it zero again ---> subtract x_alpha
    branch_x_start = x_above
    iter = 0
    offset = first_offset

    while branch_x_start < x_var_spec.interval[1]:
        branch_x_end = branch_x_start + x_stride
        offset -= x_stride
        emit_branch(branches, branch_x_start, branch_x_end, offset)
        branch_x_start += x_stride

    or_node = AST_Connective(referenced_vars=tuple(), type=Connective_Type.OR, children=tuple(branches))
    return or_node


def _linearize_congruences(root: ASTp_Node, contexter: Parent_Context_Var_Values, monotonicity: Monotonicity_Info) -> ASTp_Node:
    match root:
        case BoolLiteral() | Var() | Relation():
            return root
        case Congruence():
            linearized_congruence = _attempt_congruence_linearization(root, contexter, monotonicity)
            if linearized_congruence:
                return linearized_congruence
            return root

        case AST_Connective():
            def _linearize_isolated_subtree(subtree: ASTp_Node) -> ASTp_Node:
                contexter.enter_context()
                new_subtree = _linearize_congruences(subtree, contexter, monotonicity)
                contexter.exit_context()
                return new_subtree

            if root.type == Connective_Type.AND:
                # @Optimize: Assertions from other trees might be propagated into the current one, but are not at the moment
                contexter.enter_context()

                _insert_all_asserting_bounds_into_current_context(root, contexter)
                _optimized_subtrees = tuple(_linearize_congruences(subtree, contexter, monotonicity) for subtree in root.children)

                contexter.exit_context()
            else:
                _optimized_subtrees = tuple(_linearize_isolated_subtree(subtree) for subtree in root.children)

            return root.replace_children(_optimized_subtrees)

        case AST_Negation():
            contexter.enter_context()
            subtree = _linearize_congruences(root.child, contexter, monotonicity)
            contexter.exit_context()
            return AST_Negation(referenced_vars=root.referenced_vars, child=subtree)

        case AST_Quantifier():
            subtree = _linearize_congruences(root.child, contexter, monotonicity)
            return AST_Quantifier(referenced_vars=root.referenced_vars, bound_vars=root.bound_vars, child=subtree)

        case _:
            raise NotImplementedError(f'Node {type(root)} not handled when doing congruence linearization.')


def linearize_congruences(root: ASTp_Node) -> ASTp_Node:
    contexter = Parent_Context_Var_Values()

    monotonicity = Monotonicity_Info()
    _determine_monotonicity_of_variables(root, monotonicity, is_positive=True)

    opt = _linearize_congruences(root, contexter, monotonicity)
    return opt
