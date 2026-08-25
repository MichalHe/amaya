from amaya.relations_structures import Relation
from amaya.preprocessing.ite_preprocessing import (
    Variable_Manager,
    rewrite_ite_expressions,
)

import pytest


ite_simple_input_ast = ['ite', 'C', 'P', 'N']
ite_simple_output_ast = ['or', ['and', 'C', 'P'], ['and', ['not', 'C'], 'N']]


ite_rich_cond = [
    'and',
    ['not', Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=10)],
    Relation.new_lin_relation(variable_names=['x'], variable_coefficients=[1], predicate_symbol='<=', absolute_part=10),
]

ite_rich_cond_input_ast = ['ite', ite_rich_cond, 'P', 'N']
ite_rich_cond_output_ast = [
    'or',
    ['and', ite_rich_cond, 'P'],
    ['and', ['not', ite_rich_cond], 'N'],
]

ite_nested_input_ast = [
    'ite',
    'C1',
    ['ite', 'C2', 'P2', 'N2'],
    ['ite', 'C3', 'P3', 'N3'],
]

ite_nested_output_ast = [
    'or',
    [
        'and',
        'C1',
        [
            'or',
            ['and', 'C2', 'P2'],
            ['and', ['not', 'C2'], 'N2'],
        ]
    ],
    [
        'and',
        ['not', 'C1'],
        [
            'or',
            ['and', 'C3', 'P3'],
            ['and', ['not', 'C3'], 'N3'],
        ]
    ],
]


# These three cases never touch an arithmetic term, so they never involve ITE_Table/Variable_Manager
# at all - the ite sits directly at a Boolean position and is expanded in place. This is unaffected
# by whatever encoding relation-level ites end up using.
@pytest.mark.parametrize(('input_ast', 'expected_ast'),
    (
        (ite_simple_input_ast, ite_simple_output_ast),
        (ite_rich_cond_input_ast, ite_rich_cond_output_ast),
        (ite_nested_input_ast, ite_nested_output_ast),
    )
)
def test_rewrite_ite_expressions_boolean_position(input_ast, expected_ast):
    actual_ast = rewrite_ite_expressions(input_ast, Variable_Manager())
    assert actual_ast == expected_ast


def test_rewrite_ite_expressions_relation_without_ite_is_unchanged():
    """A relation containing no ite at all should be returned as-is (no fresh variables introduced)."""
    ast = ['<=', ['+', 'x', 'y'], 10]
    actual_ast = rewrite_ite_expressions(ast, Variable_Manager())
    assert actual_ast == ast


@pytest.mark.xfail(strict=True, reason=(
    "rewrite_ite_expressions only recurses into the positive/negative branches of a Boolean-position "
    "ite, never into its condition - if the condition itself contains an ite, it is left unrewritten "
    "and survives as a raw 'ite' node that nothing downstream knows how to handle."
))
def test_rewrite_ite_expressions_nested_condition_in_boolean_position():
    input_ast = ['ite', ['ite', 'B', 'B1', 'B2'], 'P', 'N']

    # What a correct rewrite should produce: the condition is itself recursively rewritten first,
    # just like the branches already are.
    rewritten_condition = ['or', ['and', 'B', 'B1'], ['and', ['not', 'B'], 'B2']]
    expected_ast = [
        'or',
        ['and', rewritten_condition, 'P'],
        ['and', ['not', rewritten_condition], 'N'],
    ]

    actual_ast = rewrite_ite_expressions(input_ast, Variable_Manager())
    assert actual_ast == expected_ast


def _eval(expr, env):
    """Tiny evaluator for the small arithmetic/Boolean fragment used below - understands both the
    pre-rewrite ('ite' present) and post-rewrite (fresh ite_N vars + '=' constraints) forms."""
    if isinstance(expr, int):
        return expr
    if isinstance(expr, str):
        if expr in env:
            return env[expr]
        return int(expr)

    op = expr[0]
    if op == 'ite':
        return _eval(expr[2], env) if _eval(expr[1], env) else _eval(expr[3], env)
    if op == '+':
        return sum(_eval(arg, env) for arg in expr[1:])
    if op == '<=':
        return _eval(expr[1], env) <= _eval(expr[2], env)
    if op == '=':
        return _eval(expr[1], env) == _eval(expr[2], env)
    if op == 'and':
        return all(_eval(arg, env) for arg in expr[1:])
    if op == 'or':
        return any(_eval(arg, env) for arg in expr[1:])
    if op == 'not':
        return not _eval(expr[1], env)
    raise ValueError(f'Unhandled node in test evaluator: {expr!r}')


def test_rewrite_ite_expressions_preserves_semantics_of_ite_in_relation():
    """
    Whatever encoding relation-level ites end up using (fresh variable + constraints, enumeration, ...),
    the rewritten formula must remain equisatisfiable with the original for every assignment of the
    surrounding variables - existentially quantifying over any freshly introduced variables.
    """
    original_ast = ['<=', ['+', 'x', ['ite', 'C', 3, 20]], 10]

    rewritten_ast = rewrite_ite_expressions(original_ast, Variable_Manager())
    print(rewritten_ast)

    fresh_vars = sorted({
        var for var in _collect_leaves(rewritten_ast)
        if var not in ('x', 'C') and not _is_int_literal(var)
    })

    for x in range(-5, 15):
        for c in (False, True):
            env = {'x': x, 'C': c}
            expected = _eval(original_ast, env)

            actual = any(
                _eval(rewritten_ast, {**env, **dict(zip(fresh_vars, values))})
                for values in _fresh_var_assignments(len(fresh_vars))
            )
            assert actual == expected, f'Mismatch for {env}: expected {expected}, got {actual}'


def _collect_leaves(ast) -> set:
    if isinstance(ast, int):
        return set()
    if isinstance(ast, str):
        return {ast}
    leaves = set()
    for child in ast[1:]:
        leaves |= _collect_leaves(child)
    return leaves


def _is_int_literal(token: str) -> bool:
    try:
        int(token)
        return True
    except ValueError:
        return False


def _fresh_var_assignments(count: int, low: int = -20, high: int = 20):
    if count == 0:
        yield ()
        return
    for value in range(low, high + 1):
        for rest in _fresh_var_assignments(count - 1, low, high):
            yield (value, *rest)
