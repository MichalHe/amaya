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
from amaya.preprocessing.eval import VarInfo

from amaya.relations_structures import (
    AST_Atom,
    AST_NaryNode,
    AST_Node,
    AST_Node_Names,
    BoolLiteral,
    Congruence,
    Relation,
    Var,
    VariableType,
    ast_get_binding_list,
    ast_get_node_type,
    make_and_node,
    make_exists_node,
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


def _rewrite_congruence_on_unbund_vars(exists_and_tree: AST_NaryNode, var_table: Dict[Var, VarInfo]) -> AST_NaryNode:
    bound_vars = ast_get_binding_list(exists_and_tree)
    and_node = exists_and_tree[2]
    leaves = and_node[1:]  # type:ignore

    relations: List[Relation] = [leaf for leaf in leaves if isinstance(leaf, Relation)]  # type: ignore
    congruences: List[Congruence] = [leaf for leaf in leaves if isinstance(leaf, Congruence)]  # type: ignore

    # Collect existential variables that have no bounds on them
    vars_with_no_bounds: List[Var] = []
    for var in bound_vars:
        no_bound: bool = all(var not in rel.vars for rel in relations)  # Underapproximation?
        if no_bound:
            vars_with_no_bounds.append(var)

    new_congruences: List[Congruence] = []
    new_bound_vars: List[Var] = []
    for congruence in congruences:
        # separate the congruence (a.x + b.y ~ k) where y are unbound vars
        unbound_vars, unbound_coefs = [], []
        for coef, var in zip(congruence.coefs, congruence.vars):
            if var in vars_with_no_bounds:
                unbound_vars.append(var)
                unbound_coefs.append(coef)

        if not unbound_vars:
            new_congruences.append(congruence)
            continue

        coef_gcd = math.gcd(*unbound_coefs)
        if coef_gcd == 1:  # Drop the congruence altogether
            continue

        coef_modulus_gcd = math.gcd(coef_gcd, congruence.modulus)
        if coef_modulus_gcd == 1:  # The term b.y can generate the entire ring (Z_mod, +, *)
            continue

        # Modulus and GCD have some common divisor > 1, meaning that the rhs (-b.y + k) can generate only
        # some cyclic subset of Z_mod and we cannot further simplify the songruence
        if len(unbound_vars) == 1:
            new_congruences.append(congruence)
            continue

        # Replace the term b.y with GCD.y' where y' is a new variable. This helps to speed up the automaton
        # construction as the construction of A(congruence) is exponential in #vars

        # We can avoid introducing new variables
        coef = coef_gcd
        new_var = vars_with_no_bounds[0]
        var_table[new_var].comment = 'Reused to rewrite congruence(s) on unbound vars'

        lin_terms = [term for term in congruence.linear_terms() if term[1] not in unbound_vars]
        lin_terms.append((coef, new_var))
        lin_terms = sorted(lin_terms, key=lambda term: term[1])  # Sort by variable id

        vars = [term[1] for term in lin_terms]
        coefs = [term[0] for term in lin_terms]

        new_congruences.append(Congruence(vars=vars, coefs=coefs, rhs=congruence.rhs, modulus=congruence.modulus))
        new_bound_vars.append(new_var)

    # Variables that were part of some relations were not considered unbound and therefore they must be stil part of the quantifier
    new_binding_list = [var for var in bound_vars if var not in vars_with_no_bounds] + new_bound_vars
    new_and_node = make_and_node([*relations, *new_congruences])
    new_node = make_exists_node(new_binding_list, new_and_node)
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
            leaves = child[1:]
            if not all(isinstance(leaf, (Relation, Congruence)) for leaf in leaves):
                return ['exists', ast[1], _simplify_congruences_on_unbounded_existential_vars(ast[2], var_table)]

            return _rewrite_congruence_on_unbund_vars(ast, var_table)
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
