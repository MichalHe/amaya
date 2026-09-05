"""
Regression tests for three crashes in `amaya.preprocessing.unbound_vars` found by running
`prune_conjunctions_false_due_to_parent_context` / `detect_conflics_on_isomorphic_fragments`
repeatedly (as the fixpoint pipeline does) instead of once (as the legacy sequence does) - see
`OPTIMIZATION_PIPELINE_PLAN.md` step 7 and `PROGRESS.md`.

None of these are pipeline-specific bugs: all three functions can be called directly, by anyone,
on the degenerate shapes below, and would have crashed before this fix regardless of how they were
scheduled. The pipeline just happens to be the first caller to construct these shapes in practice
(a constant relation surviving into a negation, or a variable that isn't part of the isomorphism
being checked).
"""
from amaya.preprocessing.unbound_vars import (
    are_exists_and_trees_isomorphic,
    prune_conjunctions_false_due_to_parent_context,
)
from amaya.relations_structures import AST_Negation, Relation, Var


X, Y, Z = Var(id=1), Var(id=2), Var(id=3)


def _const_eq(rhs: int) -> Relation:
    """A relation with no variables - both sides fully constant, e.g. `0 = rhs`."""
    return Relation(vars=[], coefs=[], rhs=rhs, predicate_symbol='=')


def test_negated_constant_equation_does_not_crash():
    # Regression for IndexError: `eq.vars[0]` on a negated equation with 0 variables.
    always_true_negated = AST_Negation(referenced_vars=(), child=_const_eq(0))  # not (0 = 0)
    result = prune_conjunctions_false_due_to_parent_context(always_true_negated)
    assert result is not None  # must not raise

    always_false_negated = AST_Negation(referenced_vars=(), child=_const_eq(5))  # not (0 = 5)
    result = prune_conjunctions_false_due_to_parent_context(always_false_negated)
    assert result is not None


def test_constant_relation_does_not_crash():
    # Regression for IndexError: `relation.vars[0]` on a 0-variable relation reached directly
    # (not through a negation).
    result = prune_conjunctions_false_due_to_parent_context(_const_eq(0))
    assert result is not None


def test_isomorphism_check_with_unmapped_variable_reports_false_not_keyerror():
    # `left` uses Z, which is not among `free_vars` (so not seeded into the isomorphism map) and
    # does not occur in `right` either - checking isomorphism must report "not isomorphic"
    # instead of raising KeyError while looking up Z's counterpart on the right side.
    left = Relation(vars=[Z], coefs=[1], rhs=0, predicate_symbol='<=')
    right = Relation(vars=[Y], coefs=[1], rhs=0, predicate_symbol='<=')

    assert are_exists_and_trees_isomorphic(left, right, free_vars=[X]) is False
