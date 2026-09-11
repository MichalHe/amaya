"""
Tests for `amaya.dpllt_automata` (the experimental DPLL(T)-style top-level strategy, see
`docs/DPLLT_WITH_AUTOMATA.md`). T1-T15 are the test plan of the design document's section 15, in its
naming.

The unit tests (T1-T9) exercise the split, the renaming of binders apart, the monotone abstraction,
the implicant minimization, the assertion assembly and the conjunction-prefix automaton cache. The
end-to-end tests (T10-T15) compare the strategy's verdict against the ordinary evaluator's on the
same input; a disagreement there is the failure mode every soundness argument in the design document
exists to prevent.
"""
import copy
import itertools
import logging
import random

import pytest

from amaya import dsl, parse
from amaya import logger as amaya_logger
from amaya.alphabet import LSBF_Alphabet
from amaya.config import (
    ASSERTION_OPTIMIZER_MODE_NONE,
    ASSERTION_OPTIMIZER_MODE_RESTRICTED,
    BackendType,
    DpllTAutomataConfig,
    SolutionDomain,
    solver_config,
)
from amaya.dpllt_automata import (
    Assertion_Automaton_Builder,
    Monotone_Skeleton_Node_Type,
    abstract_chi_into_monotone_sat_formula,
    count_abstraction_models,
    find_bounds_refutation,
    build_assertion_formula_for_atom_ids,
    collect_bound_vars_of_subformula,
    compute_literal_abstraction_key,
    does_subformula_contain_disjunction,
    evaluate_monotone_skeleton,
    freshen_bound_variables_in_subformula,
    is_chi_eligible_subformula,
    is_literal_node,
    minimize_asserted_atom_ids,
    perform_whole_evaluation_on_source_text_with_dpllt_automata,
    split_formula_into_phi_and_chi,
)
from amaya.preprocessing.eval import VarInfo
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
)
from amaya.sat_toplevel import isolated_sat_formula_context
from amaya.solver_core import EvaluationContext


X, Y, Z = Var(id=1), Var(id=2), Var(id=3)


def _le(var_coef_pairs, rhs: int) -> Relation:
    coefs = [coef for coef, _ in var_coef_pairs]
    vars = [var for _, var in var_coef_pairs]
    return Relation(vars=vars, coefs=coefs, rhs=rhs, predicate_symbol='<=')


def _congruence(var_coef_pairs, rhs: int, modulus: int) -> Congruence:
    coefs = [coef for coef, _ in var_coef_pairs]
    vars = [var for _, var in var_coef_pairs]
    return Congruence(vars=vars, coefs=coefs, rhs=rhs, modulus=modulus)


def _make_var_table(*var_type_pairs) -> dict:
    return {
        var: VarInfo(name=f'v{var.id}', type=var_type, is_formula_param=is_formula_param)
        for var, var_type, is_formula_param in var_type_pairs
    }


# --- T1: eligibility ---------------------------------------------------------------------------

def test_T1_chi_eligibility_accepts_positive_existential_shapes():
    assert is_literal_node(_le([(1, X)], 3))
    assert is_literal_node(X)
    assert is_literal_node(BoolLiteral(True))
    assert is_literal_node(dsl._neg(_le([(1, X)], 3)))
    assert is_literal_node(dsl._neg(_congruence([(1, X)], 0, 5)))
    assert not is_literal_node(dsl._neg(dsl._and(_le([(1, X)], 3), _le([(1, Y)], 3))))

    assert is_chi_eligible_subformula(_le([(1, X)], 3))
    assert is_chi_eligible_subformula(dsl._and(_le([(1, X)], 3), dsl._neg(_le([(1, Y)], 3))))
    assert is_chi_eligible_subformula(dsl._or(_le([(1, X)], 3), dsl._exists((Y,), _le([(1, Y)], 3))))
    assert is_chi_eligible_subformula(dsl._exists((Y,), dsl._or(_le([(1, Y)], 3), _le([(1, X)], 3))))


def test_T1_chi_eligibility_rejects_negated_and_mixed_polarity_shapes():
    negated_quantifier = dsl._neg(dsl._exists((Y,), _le([(1, Y)], 3)))
    assert not is_chi_eligible_subformula(negated_quantifier)
    assert not is_chi_eligible_subformula(dsl._and(_le([(1, X)], 3), negated_quantifier))
    assert not is_chi_eligible_subformula(dsl._neg(dsl._and(_le([(1, X)], 3), _le([(1, Y)], 3))))

    equivalence = AST_Connective(referenced_vars=(X, Y), type=Connective_Type.EQUIV,
                                 children=(_le([(1, X)], 3), _le([(1, Y)], 3)))
    assert not is_chi_eligible_subformula(equivalence)
    assert not is_chi_eligible_subformula(dsl._or(_le([(1, X)], 3), equivalence))


def test_T1_disjunction_detection():
    assert not does_subformula_contain_disjunction(dsl._and(_le([(1, X)], 3), _le([(1, Y)], 3)))
    assert does_subformula_contain_disjunction(dsl._and(_le([(1, X)], 3),
                                                        dsl._or(_le([(1, Y)], 3), _le([(1, Z)], 3))))
    assert does_subformula_contain_disjunction(dsl._exists((Y,), dsl._or(_le([(1, Y)], 3), _le([(1, X)], 3))))


# --- T2: the split -----------------------------------------------------------------------------

def test_T2_every_conjunct_lands_in_exactly_one_part():
    eligible_conjunct = dsl._or(_le([(1, X)], 3), dsl._exists((Y,), _le([(1, Y)], 3)))
    ineligible_conjunct = dsl._neg(dsl._exists((Z,), _le([(1, Z)], 3)))
    literal_conjunct = _le([(1, X)], 10)

    root = dsl._and(eligible_conjunct, ineligible_conjunct, literal_conjunct)
    split = split_formula_into_phi_and_chi(root)

    assert split.chi_conjuncts == (eligible_conjunct, literal_conjunct)
    assert split.phi_conjuncts == (ineligible_conjunct,)
    assert len(split.chi_conjuncts) + len(split.phi_conjuncts) == len(root.children)


def test_T2_non_conjunction_root_leaves_one_part_empty():
    eligible_root = dsl._or(_le([(1, X)], 3), _le([(1, Y)], 3))
    split = split_formula_into_phi_and_chi(eligible_root)
    assert split.chi_conjuncts == (eligible_root,)
    assert split.phi_conjuncts == tuple()

    ineligible_root = dsl._neg(dsl._exists((Z,), _le([(1, Z)], 3)))
    split = split_formula_into_phi_and_chi(ineligible_root)
    assert split.chi_conjuncts == tuple()
    assert split.phi_conjuncts == (ineligible_root,)


# --- T3: renaming the binders apart ------------------------------------------------------------

def test_T3_freshening_makes_binders_pairwise_distinct_and_extends_the_var_table():
    var_table = _make_var_table((X, VariableType.INT, True), (Y, VariableType.INT, False))

    # Two binders sharing one `Var` id - the shape miniscoping produces by pushing one quantifier
    # into a disjunction.
    formula = dsl._or(dsl._exists((Y,), _le([(1, X), (1, Y)], 5)),
                      dsl._exists((Y,), _le([(1, X), (2, Y)], 7)))

    freshened_formula = freshen_bound_variables_in_subformula(formula, var_table)

    quantifiers = [child for child in freshened_formula.children if isinstance(child, AST_Quantifier)]
    assert len(quantifiers) == 2
    first_bound_vars, second_bound_vars = quantifiers[0].bound_vars, quantifiers[1].bound_vars
    assert set(first_bound_vars).isdisjoint(second_bound_vars)
    assert Y not in set(first_bound_vars) | set(second_bound_vars)

    for bound_var in itertools.chain(first_bound_vars, second_bound_vars):
        assert bound_var in var_table
        assert var_table[bound_var].type == VariableType.INT
        assert not var_table[bound_var].is_formula_param

    assert collect_bound_vars_of_subformula(freshened_formula) == frozenset(first_bound_vars + second_bound_vars)


def test_T3_freshening_keeps_atom_terms_sorted_and_does_not_mutate_the_input():
    var_table = _make_var_table((X, VariableType.INT, True), (Y, VariableType.INT, False))
    atom = _le([(1, X), (1, Y)], 5)
    formula = dsl._exists((Y,), atom)

    freshened_formula = freshen_bound_variables_in_subformula(formula, var_table)

    assert atom.vars == [X, Y], 'the original atom must not be rewritten in place'
    freshened_atom = freshened_formula.child
    assert freshened_atom.vars == sorted(freshened_atom.vars)
    assert freshened_atom.vars != atom.vars


# --- T4: literal identity ----------------------------------------------------------------------

def test_T4_abstraction_keys_identify_literals():
    assert compute_literal_abstraction_key(_le([(1, X)], 3)) == compute_literal_abstraction_key(_le([(1, X)], 3))
    assert compute_literal_abstraction_key(_le([(1, X)], 3)) != compute_literal_abstraction_key(_le([(1, X)], 4))

    atom = _le([(1, X)], 3)
    assert compute_literal_abstraction_key(atom) != compute_literal_abstraction_key(dsl._neg(atom))

    assert (compute_literal_abstraction_key(_congruence([(1, X)], 0, 5))
            != compute_literal_abstraction_key(_congruence([(1, X)], 0, 7)))

    assert compute_literal_abstraction_key(X) != compute_literal_abstraction_key(Y)
    assert compute_literal_abstraction_key(X) == compute_literal_abstraction_key(Var(id=X.id))


# --- T5: the abstraction is monotone -----------------------------------------------------------

def _skeleton_contains_no_negation(skeleton) -> bool:
    if skeleton.type in (Monotone_Skeleton_Node_Type.ATOM, Monotone_Skeleton_Node_Type.CONSTANT):
        return True
    return all(_skeleton_contains_no_negation(child) for child in skeleton.children)


def test_T5_abstraction_skeleton_contains_no_negation():
    chi = dsl._or(dsl._exists((Y,), dsl._and(_le([(1, X), (1, Y)], 5), dsl._neg(_le([(1, Y)], 0)))),
                  dsl._neg(_le([(1, X)], 20)))

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula((chi,))

    assert _skeleton_contains_no_negation(abstraction.skeleton)
    # The three literals are `x + y <= 5`, `not (y <= 0)` and `not (x <= 20)`; a negated atom is a
    # literal of its own.
    assert abstraction.atom_count == 3


def test_T5_negated_literal_and_its_positive_counterpart_get_different_ids():
    atom = _le([(1, X)], 3)
    chi = dsl._and(atom, dsl._neg(atom))

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula((chi,))

    assert abstraction.atom_count == 2


# --- T6: implicant minimization ----------------------------------------------------------------

def test_T6_minimized_literal_set_is_a_minimal_model_of_the_abstraction():
    chi = dsl._and(_le([(1, X)], 10),
                   dsl._or(_le([(1, Y)], 3), _le([(1, Z)], 4), _le([(1, Y), (1, Z)], 5)))

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula((chi,))

    all_atom_ids = set(abstraction.manager.literal_by_atom_id)
    minimized_atom_ids = minimize_asserted_atom_ids(abstraction, all_atom_ids)

    assert evaluate_monotone_skeleton(abstraction.skeleton, minimized_atom_ids)
    assert len(minimized_atom_ids) == 2, 'one mandatory conjunct plus one disjunct'
    for atom_id in minimized_atom_ids:
        assert not evaluate_monotone_skeleton(abstraction.skeleton, minimized_atom_ids - {atom_id})


def test_T6_minimization_repairs_a_literal_set_that_does_not_satisfy_the_abstraction():
    chi = dsl._or(_le([(1, X)], 3), _le([(1, Y)], 4))

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula((chi,))

    minimized_atom_ids = minimize_asserted_atom_ids(abstraction, set())
    assert evaluate_monotone_skeleton(abstraction.skeleton, minimized_atom_ids)


# --- T7: assembling the assertion --------------------------------------------------------------

def test_T7_assertion_prefix_holds_exactly_the_mentioned_binders():
    var_table = _make_var_table((X, VariableType.INT, True), (Y, VariableType.INT, False),
                                (Z, VariableType.INT, False))
    chi = dsl._or(dsl._exists((Y,), _le([(1, X), (1, Y)], 5)),
                  dsl._exists((Z,), _le([(1, X), (1, Z)], 7)))
    chi = freshen_bound_variables_in_subformula(chi, var_table)
    chi_bound_vars = collect_bound_vars_of_subformula(chi)

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula((chi,))

    first_branch_atom_id = 0
    assertion = build_assertion_formula_for_atom_ids(abstraction, {first_branch_atom_id}, chi_bound_vars)

    assert isinstance(assertion, AST_Quantifier)
    mentioned_vars = set(abstraction.manager.literal_by_atom_id[first_branch_atom_id].vars)
    assert set(assertion.bound_vars) == mentioned_vars & chi_bound_vars
    assert len(assertion.bound_vars) == 1

    # `referenced_vars` must be accurate on every produced node - the evaluator relies on it.
    assert set(assertion.referenced_vars) == mentioned_vars


def test_T7_assertion_without_bound_vars_is_the_bare_conjunction():
    var_table = _make_var_table((X, VariableType.INT, True), (Y, VariableType.INT, True))
    chi = dsl._or(_le([(1, X)], 5), _le([(1, Y)], 7))

    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula((chi,))

    assertion = build_assertion_formula_for_atom_ids(abstraction, {0, 1}, frozenset())
    assert isinstance(assertion, AST_Connective) and assertion.type == Connective_Type.AND
    assert set(assertion.referenced_vars) == {X, Y}

    unprojected_assertion = build_assertion_formula_for_atom_ids(abstraction, {0, 1}, frozenset(),
                                                                 project_bound_vars=False)
    assert not isinstance(unprojected_assertion, AST_Quantifier)


# --- T8, T9: the conjunction-prefix automaton cache --------------------------------------------

@pytest.fixture
def mtbdd_solver_config():
    """ Run over integers with the MTBDD backend, restoring the global config afterwards. """
    saved_backend = solver_config.backend_type
    saved_domain = solver_config.solution_domain
    saved_optimizations = copy.deepcopy(solver_config.optimizations)
    saved_dpllt = copy.deepcopy(solver_config.dpllt_automata)
    saved_log_level = amaya_logger.level

    solver_config.backend_type = BackendType.MTBDD
    solver_config.solution_domain = SolutionDomain.INTEGERS
    amaya_logger.setLevel(logging.WARNING)

    yield solver_config

    solver_config.backend_type = saved_backend
    solver_config.solution_domain = saved_domain
    solver_config.optimizations = saved_optimizations
    solver_config.dpllt_automata = saved_dpllt
    amaya_logger.setLevel(saved_log_level)


def _langs_equal(first_nfa, second_nfa) -> bool:
    """ Whether two (possibly nondeterministic) MTBDD automata accept the same language. """
    first_dfa, second_dfa = first_nfa.determinize(), second_nfa.determinize()
    only_in_first = first_dfa.intersection(second_dfa.complement())
    only_in_second = second_dfa.intersection(first_dfa.complement())
    return only_in_first.find_model() is None and only_in_second.find_model() is None


def _make_evaluation_context(var_table) -> EvaluationContext:
    alphabet = LSBF_Alphabet.from_vars(var_table.keys())
    return EvaluationContext(alphabet=alphabet, var_table=var_table)


def test_T8_prefix_cache_stores_one_entry_per_prefix_and_preserves_the_language(mtbdd_solver_config):
    import amaya.cse_cache  # noqa: F401  - installs MTBDD_NFA.renamed_copy, which the cache needs

    var_table = _make_var_table((X, VariableType.INT, True), (Y, VariableType.INT, True),
                                (Z, VariableType.INT, True))
    ctx = _make_evaluation_context(var_table)

    shared_conjunct_a = _le([(1, X)], 6)
    shared_conjunct_b = _le([(-1, Y)], -2)
    first_assertion = AST_Connective(referenced_vars=(X, Y, Z), type=Connective_Type.AND,
                                     children=(shared_conjunct_a, shared_conjunct_b, _le([(1, Z)], 4)))
    second_assertion = AST_Connective(referenced_vars=(X, Y, Z), type=Connective_Type.AND,
                                      children=(shared_conjunct_a, shared_conjunct_b, _le([(1, Z)], 9)))

    builder = Assertion_Automaton_Builder()
    first_nfa = builder.build_automaton_for_assertion(first_assertion, ctx)
    entries_after_first_build = len(builder.intersection_prefix_cache)
    second_nfa = builder.build_automaton_for_assertion(second_assertion, ctx)

    assert entries_after_first_build == 3, 'one entry per prefix length of a three-conjunct assertion'
    assert builder.prefix_cache_hits == 1
    assert builder.longest_prefix_hit_length == 2

    uncached_builder = Assertion_Automaton_Builder(max_prefix_cache_entries=0)
    uncached_first_nfa = uncached_builder.build_automaton_for_assertion(first_assertion, ctx)
    uncached_second_nfa = uncached_builder.build_automaton_for_assertion(second_assertion, ctx)

    assert _langs_equal(first_nfa, uncached_first_nfa)
    assert _langs_equal(second_nfa, uncached_second_nfa)


def test_T9_projecting_the_assertion_prefix_does_not_corrupt_the_cached_automata(mtbdd_solver_config):
    import amaya.cse_cache  # noqa: F401

    var_table = _make_var_table((X, VariableType.INT, True), (Y, VariableType.INT, False))
    ctx = _make_evaluation_context(var_table)

    conjunction = AST_Connective(referenced_vars=(X, Y), type=Connective_Type.AND,
                                 children=(_le([(1, X), (1, Y)], 5), _le([(-1, Y)], -3)))
    assertion = AST_Quantifier(referenced_vars=(X, Y), bound_vars=(Y,), child=conjunction)

    builder = Assertion_Automaton_Builder()
    builder.build_automaton_for_assertion(assertion, ctx)

    cached_full_prefix_key = max(builder.intersection_prefix_cache, key=len)
    cached_nfa = builder.intersection_prefix_cache[cached_full_prefix_key]

    reference_nfa = parse.run_evaluation_procedure(conjunction, ctx)
    assert _langs_equal(cached_nfa, reference_nfa), (
        'the projection performed on the automaton handed out by the cache must not have been applied '
        'to the automaton the cache holds'
    )


# --- T10-T15: end-to-end differential tests ----------------------------------------------------

@pytest.fixture(params=[BackendType.NATIVE, BackendType.MTBDD], ids=['native', 'mtbdd'])
def quiet_solver_config(request):
    """ Run the differential comparison on both backends, restoring the global config afterwards. """
    saved_backend = solver_config.backend_type
    saved_dpllt = copy.deepcopy(solver_config.dpllt_automata)
    saved_log_level = amaya_logger.level

    solver_config.backend_type = request.param
    solver_config.dpllt_automata = DpllTAutomataConfig()
    amaya_logger.setLevel(logging.WARNING)

    yield solver_config

    solver_config.backend_type = saved_backend
    solver_config.dpllt_automata = saved_dpllt
    amaya_logger.setLevel(saved_log_level)


def _is_sat_according_to_ordinary_evaluation(source_text: str) -> bool:
    result = parse.perform_whole_evaluation_on_source_text(source_text)
    return result is not None and result.model is not None


def _is_sat_according_to_dpllt(source_text: str) -> bool:
    result = perform_whole_evaluation_on_source_text_with_dpllt_automata(source_text)
    return result is not None and result.model is not None


def _assert_verdicts_agree(source_text: str):
    expected_verdict = _is_sat_according_to_ordinary_evaluation(source_text)
    actual_verdict = _is_sat_according_to_dpllt(source_text)
    assert actual_verdict == expected_verdict, f'verdicts disagree on:\n{source_text}'


def _compare_verdicts_tolerating_shared_evaluator_defects(source_text: str) -> bool:
    """
    Compare the two verdicts, returning whether a comparison was actually made.

    A generated formula can reach one of two defects of the shared automata evaluator, neither of which
    involves this module and both of which reproduce on a plain `run-amaya.py get-sat`:

    * `amaya.automatons.NFA.union` raises `KeyError` when one operand has no states, which is what an
      intersection that removed every non-finishing state produces (native backend).
    * `amaya.parse.evaluate_exists_expr` projects every bound variable unconditionally, and
      `amaya.mtbdd_transitions.MTBDDTransitionFn.project_variable_away` raises `ValueError` when the
      variable is not one of the automaton's tracks - which happens once a pass has removed the only
      atom that constrained it (MTBDD backend).

    A formula is skipped when the *ordinary* evaluation raises, since that is what defines the expected
    verdict and there is then nothing to compare against. The DPLL(T) strategy raising on a formula the
    ordinary evaluation decides is a failure, not a skip. Note the strategy survives some of these
    formulae that the ordinary evaluation does not: `Assertion_Automaton_Builder._project_bound_vars_away`
    skips variables the automaton does not track, which is the second defect above.
    """
    try:
        expected_verdict = _is_sat_according_to_ordinary_evaluation(source_text)
    except Exception:  # noqa: BLE001 - a defect of the shared evaluator, see the docstring
        return False

    actual_verdict = _is_sat_according_to_dpllt(source_text)
    assert actual_verdict == expected_verdict, f'verdicts disagree on:\n{source_text}'
    return True


T10_SOURCE = """
(declare-fun x () Int)
(assert (exists ((y Int)) (and (= (+ x y) 5) (<= 3 y))))
(check-sat)
"""

T11_SOURCE = """
(declare-fun x () Int)
(declare-fun z () Int)
(assert (or (exists ((y Int)) (and (= (+ x y) 5) (<= 3 y)))
            (exists ((v Int)) (and (= (+ x v) 20) (<= 12 v)))))
(assert (not (exists ((w Int)) (and (= (+ z w) 1) (<= 0 w) (<= 100 x)))))
(assert (<= 100 x))
(check-sat)
"""

T12_SOURCE = """
(declare-fun x () Int)
(assert (or (exists ((y Int)) (and (<= (+ x y) 5) (<= 3 y)))
            (exists ((y Int)) (and (<= (+ x y) 9) (<= 7 y)))))
(assert (<= 0 x))
(check-sat)
"""

T14_SOURCE = """
(declare-fun b () Bool)
(declare-fun x () Int)
(assert (or (and b (<= x 3)) (and b (<= 10 x))))
(assert (not (and b (<= 100 x))))
(check-sat)
"""


def test_T10_conjunction_without_disjunction_falls_through(quiet_solver_config):
    _assert_verdicts_agree(T10_SOURCE)


def test_T11_blocking_drives_a_second_iteration(quiet_solver_config):
    _assert_verdicts_agree(T11_SOURCE)


def test_T12_nested_quantifiers_under_a_disjunction(quiet_solver_config):
    _assert_verdicts_agree(T12_SOURCE)


def test_T13_binders_sharing_a_var_id_are_renamed_apart(quiet_solver_config):
    """
    Two `AST_Quantifier` nodes binding the same `Var` id, with disjoint requirements on it.

    Without `freshen_bound_variables_in_subformula`, an implicant drawing a literal from each branch
    hoists both binders into one prefix, forcing one value on two independent variables and turning a
    satisfiable formula into UNSAT.
    """
    var_table = _make_var_table((X, VariableType.INT, True), (Y, VariableType.INT, False))
    shared_binder_formula = dsl._or(dsl._exists((Y,), _le([(1, Y)], -10)),
                                    dsl._exists((Y,), _le([(-1, Y)], -10)))

    freshened_formula = freshen_bound_variables_in_subformula(shared_binder_formula, var_table)
    quantifiers = [child for child in freshened_formula.children if isinstance(child, AST_Quantifier)]

    first_binder_var = quantifiers[0].bound_vars[0]
    second_binder_var = quantifiers[1].bound_vars[0]
    assert first_binder_var != second_binder_var

    chi_bound_vars = collect_bound_vars_of_subformula(freshened_formula)
    with isolated_sat_formula_context():
        abstraction = abstract_chi_into_monotone_sat_formula((freshened_formula,))

    # Asserting one literal from each branch must produce a prefix binding two distinct variables.
    assertion = build_assertion_formula_for_atom_ids(abstraction, {0, 1}, chi_bound_vars)
    assert isinstance(assertion, AST_Quantifier)
    assert len(set(assertion.bound_vars)) == 2


def test_T14_free_bool_parameter_shared_between_the_two_parts(quiet_solver_config):
    """
    Guards the assertion-optimizer contract: the verdict must not depend on which optimizer mode the
    assertion is put through, even though `phi` constrains a Bool parameter the assertion also mentions.
    """
    solver_config.dpllt_automata = DpllTAutomataConfig(assertion_optimizer=ASSERTION_OPTIMIZER_MODE_NONE)
    verdict_without_optimizer = _is_sat_according_to_dpllt(T14_SOURCE)

    solver_config.dpllt_automata = DpllTAutomataConfig(assertion_optimizer=ASSERTION_OPTIMIZER_MODE_RESTRICTED)
    verdict_with_restricted_optimizer = _is_sat_according_to_dpllt(T14_SOURCE)

    assert verdict_without_optimizer == verdict_with_restricted_optimizer
    assert verdict_without_optimizer == _is_sat_according_to_ordinary_evaluation(T14_SOURCE)


def _generate_random_formula_source(rng: random.Random) -> str:
    """ A small LIA formula shaped so that the split finds something to work with. """
    def random_atom(var_name: str) -> str:
        coefficient = rng.choice((1, 2, -1))
        bound = rng.randint(-6, 6)
        relation = rng.choice(('<=', '>=', '='))
        return f'({relation} (* {coefficient} {var_name}) {bound})'

    disjunct_count = rng.randint(2, 3)
    disjuncts = []
    for disjunct_index in range(disjunct_count):
        bound_var_name = f'y{disjunct_index}'
        atoms = ' '.join(random_atom(rng.choice(('x', bound_var_name))) for _ in range(rng.randint(1, 3)))
        disjuncts.append(f'(exists (({bound_var_name} Int)) (and {atoms} '
                         f'(<= (+ x {bound_var_name}) {rng.randint(-4, 8)})))')

    general_conjunct = f'(not (exists ((w Int)) (and (<= 0 w) {random_atom("x")})))'

    return (
        '(declare-fun x () Int)\n'
        f'(assert (or {" ".join(disjuncts)}))\n'
        f'(assert {general_conjunct})\n'
        f'(assert {random_atom("x")})\n'
        '(check-sat)\n'
    )


def test_T15_randomized_differential_against_the_ordinary_evaluator(quiet_solver_config):
    """
    Compare the two strategies' verdicts on generated formulae, on both backends.

    See `_compare_verdicts_tolerating_shared_evaluator_defects` for the two pre-existing evaluator
    defects the generator reaches and why skipping a formula on them does not weaken the comparison.
    """
    rng = random.Random(20260910)
    compared_formula_count = 0
    for _ in range(120):
        source_text = _generate_random_formula_source(rng)
        compared_formula_count += _compare_verdicts_tolerating_shared_evaluator_defects(source_text)

    assert compared_formula_count >= 60, ('too few formulae were actually compared for this test to '
                                          'mean anything')


# --- T16: the display-and-exit debug option ----------------------------------------------------

def test_T16_showing_the_existential_part_prints_it_and_exits(quiet_solver_config, capsys):
    solver_config.dpllt_automata = DpllTAutomataConfig(show_positive_existential_part=True)

    with pytest.raises(SystemExit) as raised_exit:
        _is_sat_according_to_dpllt(T11_SOURCE)

    assert raised_exit.value.code == 0

    printed_output = capsys.readouterr().out
    printed_lines = [line.strip() for line in printed_output.splitlines()]
    assert '----- Positive-existential part (chi) -----' in printed_lines
    # T11's positive-existential part conjoins a bound on `x` with a disjunction of two existentially
    # quantified conjunctions; the whole formula additionally has a `NOT exists` conjunct, which the
    # split must have put into the general part instead.
    assert 'or' in printed_lines
    assert sum(1 for line in printed_lines if line.startswith('exists')) == 2
    assert 'NOT' not in printed_lines


def test_T16_showing_an_empty_existential_part_reports_it_instead_of_evaluating(quiet_solver_config, capsys):
    """
    The display happens before either fall-through, so a formula the strategy would decline reports an
    empty part rather than being handed to the ordinary evaluator.
    """
    solver_config.dpllt_automata = DpllTAutomataConfig(show_positive_existential_part=True)

    source_with_no_positive_existential_conjunct = """
    (declare-fun x () Int)
    (assert (not (exists ((y Int)) (and (<= 0 y) (= (+ x y) 5)))))
    (check-sat)
    """

    with pytest.raises(SystemExit) as raised_exit:
        _is_sat_according_to_dpllt(source_with_no_positive_existential_conjunct)

    assert raised_exit.value.code == 0
    assert '<empty' in capsys.readouterr().out


# --- T17: counting what the abstraction admits -------------------------------------------------

def test_T17_model_and_minimal_implicant_counts_of_a_disjunction_of_conjunctions():
    """
    `(a AND b) OR (c AND d)` over four literals has 4 + 4 - 1 = 7 models (inclusion-exclusion on the
    two disjuncts) and exactly two minimal implicants, `{a, b}` and `{c, d}`.
    """
    chi = dsl._or(dsl._and(_le([(1, X)], 3), _le([(-1, X)], -1)),
                  dsl._and(_le([(1, Y)], 4), _le([(-1, Y)], -2)))

    counts = count_abstraction_models((chi,), enumeration_limit=1000)

    assert counts.abstracted_literal_count == 4
    assert counts.total_model_count == 7
    assert not counts.total_model_enumeration_hit_limit
    assert counts.minimal_implicant_count == 2
    assert not counts.minimal_implicant_enumeration_hit_limit


def test_T17_a_mandatory_conjunct_multiplies_neither_count():
    """ Conjoining a literal that every model must satisfy leaves both counts unchanged. """
    disjunction = dsl._or(dsl._and(_le([(1, X)], 3), _le([(-1, X)], -1)),
                          dsl._and(_le([(1, Y)], 4), _le([(-1, Y)], -2)))
    mandatory_literal = _le([(1, Z)], 7)

    counts = count_abstraction_models((mandatory_literal, disjunction), enumeration_limit=1000)

    assert counts.abstracted_literal_count == 5
    assert counts.total_model_count == 7
    assert counts.minimal_implicant_count == 2


def test_T17_counting_a_literal_that_occurs_twice_merges_it():
    """ Two occurrences of one literal are a single Boolean variable, so the abstraction has 3 models. """
    shared_literal = _le([(1, X)], 3)
    chi = dsl._or(shared_literal, dsl._and(shared_literal, _le([(1, Y)], 4)))

    counts = count_abstraction_models((chi,), enumeration_limit=1000)

    assert counts.abstracted_literal_count == 2
    assert counts.total_model_count == 2, 'the two models are those setting the shared literal true'
    assert counts.minimal_implicant_count == 1


def test_T17_enumeration_limit_turns_a_count_into_a_lower_bound():
    chi = dsl._or(dsl._and(_le([(1, X)], 3), _le([(-1, X)], -1)),
                  dsl._and(_le([(1, Y)], 4), _le([(-1, Y)], -2)))

    counts = count_abstraction_models((chi,), enumeration_limit=3)

    assert counts.total_model_count == 3
    assert counts.total_model_enumeration_hit_limit
    assert counts.minimal_implicant_count == 2
    assert not counts.minimal_implicant_enumeration_hit_limit, 'two implicants fit under a limit of three'


def test_T17_counting_an_empty_existential_part_reports_zeroes():
    counts = count_abstraction_models(tuple(), enumeration_limit=1000)

    assert counts.abstracted_literal_count == 0
    assert counts.total_model_count == 0
    assert counts.minimal_implicant_count == 0


def test_T17_the_counting_option_prints_the_counts_and_exits(quiet_solver_config, capsys):
    solver_config.dpllt_automata = DpllTAutomataConfig(count_abstraction_models=True)

    with pytest.raises(SystemExit) as raised_exit:
        _is_sat_according_to_dpllt(T11_SOURCE)

    assert raised_exit.value.code == 0

    printed_lines = [line.strip() for line in capsys.readouterr().out.splitlines()]
    assert '----- Boolean abstraction of the positive-existential part (chi) -----' in printed_lines
    assert any(line.startswith('models:') for line in printed_lines)
    assert any(line.startswith('minimal implicants:') for line in printed_lines)


# --- T18: refuting an assertion by its variable bounds alone -----------------------------------

def _build_abstraction(chi):
    """ The abstraction of `chi`, built inside its own pysat context (which is then discarded). """
    with isolated_sat_formula_context():
        return abstract_chi_into_monotone_sat_formula((chi,))


def _atom_id_of(abstraction, literal) -> int:
    return abstraction.manager.atom_id_by_literal_key[compute_literal_abstraction_key(literal)]


def test_T18_clashing_bounds_are_reported_as_a_two_literal_core():
    lower_bound = _le([(-1, X)], -219)     # -x <= -219,  i.e. x >= 219
    upper_bound = _le([(1, X)], 0)         #  x <= 0
    unrelated = _le([(1, Y)], 4)
    abstraction = _build_abstraction(dsl._and(lower_bound, upper_bound, unrelated))

    refutation = find_bounds_refutation(set(abstraction.manager.literal_by_atom_id), abstraction)

    assert refutation is not None
    assert refutation.var == X
    assert refutation.atom_ids == frozenset((_atom_id_of(abstraction, lower_bound),
                                             _atom_id_of(abstraction, upper_bound)))
    assert _atom_id_of(abstraction, unrelated) not in refutation.atom_ids


def test_T18_consistent_bounds_are_not_refuted():
    abstraction = _build_abstraction(dsl._and(_le([(-1, X)], -3), _le([(1, X)], 10), _le([(1, Y)], 4)))

    assert find_bounds_refutation(set(abstraction.manager.literal_by_atom_id), abstraction) is None


def test_T18_a_unit_equality_clashing_with_a_bound_is_a_core():
    single_value = Relation(vars=[X], coefs=[1], rhs=5, predicate_symbol='=')
    upper_bound = _le([(1, X)], 3)
    abstraction = _build_abstraction(dsl._and(single_value, upper_bound))

    refutation = find_bounds_refutation(set(abstraction.manager.literal_by_atom_id), abstraction)

    assert refutation is not None
    assert refutation.atom_ids == frozenset((_atom_id_of(abstraction, single_value),
                                             _atom_id_of(abstraction, upper_bound)))


def test_T18_a_unit_equality_with_no_integer_solution_is_a_single_literal_core():
    unsatisfiable_equality = Relation(vars=[X], coefs=[2], rhs=3, predicate_symbol='=')
    abstraction = _build_abstraction(dsl._and(unsatisfiable_equality, _le([(1, Y)], 4)))

    refutation = find_bounds_refutation(set(abstraction.manager.literal_by_atom_id), abstraction)

    assert refutation is not None
    assert refutation.atom_ids == frozenset((_atom_id_of(abstraction, unsatisfiable_equality),))


def test_T18_congruences_and_multi_variable_relations_are_not_read_as_bounds():
    """ A congruence constrains a residue and a two-variable relation constrains no single variable. """
    abstraction = _build_abstraction(dsl._and(_congruence([(1, X)], 0, 5),
                                              _congruence([(1, X)], 1, 5),
                                              _le([(1, X), (1, Y)], -10),
                                              _le([(-1, X), (-1, Y)], -10)))

    assert find_bounds_refutation(set(abstraction.manager.literal_by_atom_id), abstraction) is None


def test_T18_the_core_is_a_subset_of_the_asserted_literals():
    lower_bound, upper_bound = _le([(-1, X)], -219), _le([(1, X)], 0)
    abstraction = _build_abstraction(dsl._and(lower_bound, upper_bound))

    asserted = {_atom_id_of(abstraction, lower_bound)}
    assert find_bounds_refutation(asserted, abstraction) is None, 'one bound alone is satisfiable'

    asserted.add(_atom_id_of(abstraction, upper_bound))
    refutation = find_bounds_refutation(asserted, abstraction)
    assert refutation is not None and refutation.atom_ids <= asserted


T18_SOURCE = """
(declare-fun x () Int)
(declare-fun z () Int)
(assert (or (and (<= 219 x) (<= x 0) (<= z 3))
            (and (<= 5 x) (<= x 40) (<= z 7))))
(assert (<= 0 z))
(check-sat)
"""


def test_T18_the_verdict_does_not_depend_on_the_bounds_refutation(quiet_solver_config):
    """
    The check refutes an assertion the theory call would have refuted anyway, and blocks a subset of
    what would otherwise be blocked, so the verdict must not move.

    The comparison against the ordinary evaluator goes through the tolerant helper: `T18_SOURCE` has an
    unsatisfiable first disjunct, which is precisely the shape that trips defect P1 in
    `amaya.automatons.NFA.union` on the native backend. The equality of the two DPLL(T) verdicts is
    the property under test and is asserted unconditionally.
    """
    solver_config.dpllt_automata = DpllTAutomataConfig(use_bounds_refutation=True)
    verdict_with_check = _is_sat_according_to_dpllt(T18_SOURCE)

    solver_config.dpllt_automata = DpllTAutomataConfig(use_bounds_refutation=False)
    verdict_without_check = _is_sat_according_to_dpllt(T18_SOURCE)

    assert verdict_with_check == verdict_without_check

    solver_config.dpllt_automata = DpllTAutomataConfig(use_bounds_refutation=True)
    _compare_verdicts_tolerating_shared_evaluator_defects(T18_SOURCE)
