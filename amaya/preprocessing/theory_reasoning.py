from collections import defaultdict
from dataclasses import dataclass, field
from typing import Iterable, cast, overload
import math
import itertools

from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Node,
    ASTp_Node_Base,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Value_Interval,
    Var,
    ast_references_var,
    pprint_formula
)


@dataclass
class Var_Alias:
    """ Represents `elim_var = sum(coef*var for var, coef in zip(vars, coefs)) + const`. """
    vars: list[Var]
    coefs: list[int]
    const: int


@dataclass
class Asserted_Model_Properties:
    equations: list[list[Relation]] = field(default_factory=lambda: [[]])
    bool_atom_values: list[dict[Var, bool]] = field(default_factory=lambda: [{}])
    var_aliases: list[dict[Var, Var_Alias]] = field(default_factory=lambda: [{}])
    var_bounds: list[dict[Var, Value_Interval]] = field(default_factory=lambda: [{}])
    """
    Stack of currently known hard bounds (`X <= C`, `-X <= C`), scoped like `equations`/`var_aliases` -
    one dict per currently open AND/OR frame, pushed/popped alongside them.
    """

    var_uses_excluding_hard_bounds: dict[Var, int] = field(default_factory=dict)
    """
    Number of times each variable occurs in a Relation that is not a hard bound (an equation, or an
    inequality over more than one variable) or in a Congruence, counted once over the whole formula
    before simplification starts. A hard bound on `X` does not count - it is exactly the kind of atom
    the congruence/bounds simplification below may drop together with the congruence it covers, so it
    must not make `X` look "used elsewhere". Computed once per top-level call (see
    `simplify_formula_using_model_properties`), not updated as the tree is rewritten - unlike the
    order-dependent per-branch tracking above, this must reflect the *whole*, original formula, since
    understating a variable's use elsewhere would make the congruence-dropping rule unsound (dropping a
    congruence still needed by an atom the local, in-order scan has not reached yet).
    """

    vars_covered_by_congruence_bounds: set[Var] = field(default_factory=set)
    """
    Variables whose hard bounds were found to cover a congruence's whole period, letting that
    congruence be replaced by True. Consumed by the Relation() case to also drop the (now redundant)
    bound atoms themselves.
    """

    branch_depth: int = 0
    """ How many OR/EQUIV branch boundaries we are currently nested under. """

    negation_depth: int = 0
    """ How many NOTs we are currently nested under. """

    quantifier_scopes: list[tuple[frozenset[Var], int, int, int]] = field(default_factory=list)
    """
    Stack of currently open quantifiers: (their bound vars, branch_depth, negation_depth, stack_depth)
    as they were when we entered that quantifier's body. `stack_depth` is `len(var_aliases)` at that
    point, i.e. the equations/var_aliases frame that is guaranteed to stay alive for the quantifier's
    whole body.
    """

    stack_entry_negation_depths: list[int] = field(default_factory=lambda: [0])
    """
    negation_depth as it was when the corresponding level of `equations`/`var_aliases`/`bool_atom_values`
    was pushed (i.e. when we entered the enclosing AND/OR). An equation encountered at a negation_depth
    different from the top of this stack sits under a NOT (or an odd number of them) relative to its
    enclosing conjunction/disjunction, so it is not implied by that branch and must not be remembered.
    """

    vars_eliminated_via_alias: set[Var] = field(default_factory=set)
    """
    Bound variables whose defining equation was dropped because they were fully substituted away.
    Consumed (and removed from this set) by the AST_Quantifier node that binds them.
    """

    vars_referenced_unsubstituted: set[Var] = field(default_factory=set)
    """
    Variables that appear literally (i.e. with no alias applied - either because none was known yet,
    or none exists) in a Relation/Congruence that has already been fixed into the result tree. AND
    processes its children in a single left-to-right pass, so a later child can derive an alias for a
    variable that an earlier, already-finalized sibling still references raw - that alias must not be
    allowed to drop the variable's binder, or the earlier reference is left dangling with none.
    """

    def insert_stack(self):
        self.equations.append([])
        self.bool_atom_values.append(dict())
        self.var_aliases.append(dict())
        self.var_bounds.append(dict())
        self.stack_entry_negation_depths.append(self.negation_depth)

    def pop_stack(self):
        self.bool_atom_values.pop(-1)
        self.equations.pop(-1)
        self.var_aliases.pop(-1)
        self.var_bounds.pop(-1)
        self.stack_entry_negation_depths.pop(-1)

    def is_unconditionally_true_for_current_stack_frame(self) -> bool:
        """
        True if we are still in a position unconditionally within the innermost open AND/OR branch -
        i.e. no NOT has been crossed since that branch was entered. An equation found here is implied
        by the branch and can safely be remembered (as an alias or verbatim) for later substitution;
        one found under a mismatched negation depth is not implied by anything and must be discarded.
        """
        return self.negation_depth == self.stack_entry_negation_depths[-1]

    def enter_branch(self):
        self.branch_depth += 1

    def exit_branch(self):
        self.branch_depth -= 1

    def enter_negation(self):
        self.negation_depth += 1

    def exit_negation(self):
        self.negation_depth -= 1

    def enter_quantifier_scope(self, bound_vars: tuple[Var, ...]):
        # The topmost frame that already exists when we enter this quantifier - the one that stays
        # alive for its *whole* body (any frame the body itself pushes gets popped before the body
        # is done, so it cannot be used to share facts between the body's own sibling branches).
        self.quantifier_scopes.append((frozenset(bound_vars), self.branch_depth, self.negation_depth, len(self.var_aliases) - 1))

    def exit_quantifier_scope(self):
        self.quantifier_scopes.pop(-1)

    def is_unconditionally_true_for_owning_quantifier(self, var: Var) -> bool:
        """
        True if `var` is bound by a currently open quantifier, and we are still in a position that
        is unconditionally within that quantifier's whole body - no OR/EQUIV branch and no NOT
        crossed since entering it. An equation defining `var` found at such a position can be
        treated as asserted throughout the quantifier's whole body, and can therefore be dropped
        (together with `var`'s binding) once it has been substituted away everywhere else.
        """
        for bound_vars, entry_branch_depth, entry_negation_depth, _entry_stack_depth in reversed(self.quantifier_scopes):
            if var in bound_vars:
                return entry_branch_depth == self.branch_depth and entry_negation_depth == self.negation_depth
        return False

    def find_owning_quantifier_scope_index(self, var: Var) -> int | None:
        """
        Index into `quantifier_scopes` (0 = outermost) of the innermost currently open quantifier
        that binds `var`, or None if `var` is not bound by any currently open quantifier (e.g. it is
        a free/global formula parameter).
        """
        for i in range(len(self.quantifier_scopes) - 1, -1, -1):
            bound_vars, _, _, _ = self.quantifier_scopes[i]
            if var in bound_vars:
                return i
        return None

    def get_own_body_stack_depth(self, scope_index: int) -> int:
        """
        The equations/var_aliases frame that stays alive for the whole body of `quantifier_scopes[scope_index]`.
        That quantifier's body may not itself be an AND/OR (e.g. a bare relation, or another quantifier
        directly) and so may never have pushed its own frame - clamp to the current topmost frame, the
        most conservative (least-promoted) valid target, in that case.
        """
        return min(self.quantifier_scopes[scope_index][3] + 1, len(self.var_aliases) - 1)

    def get_widest_valid_stack_depth(self) -> int:
        """
        The shallowest (outermost) currently-open equations/var_aliases frame that the current
        position is unconditionally still within - i.e. no OR/EQUIV branch and no NOT has been
        crossed since the owning quantifier of that frame was entered. An equation registered at
        this depth (instead of the innermost frame it was actually found in) stays visible to
        sibling conjuncts elsewhere in the same quantifier's body - e.g. a sibling AND branch nested
        under the same quantifier - rather than disappearing once its immediate AND/OR is popped.
        """
        widest_depth = len(self.var_aliases) - 1
        for _bound_vars, entry_branch_depth, entry_negation_depth, entry_stack_depth in reversed(self.quantifier_scopes):
            if entry_branch_depth != self.branch_depth or entry_negation_depth != self.negation_depth:
                break
            widest_depth = entry_stack_depth
        return widest_depth

    def negate_last_level(self):
        last_level = self.bool_atom_values[-1]
        for var, var_value in last_level.items():
            last_level[var] = not var_value

    def assert_equation(self, eq: Relation, depth: int = -1):
        eq.sort_variables()
        self.equations[depth].append(eq)

    def search_similar_eq(self, eq: Relation) -> Relation | None:
        eq_vars = sorted(eq.vars)

        for eq_stack in reversed(self.equations):
            for asserted_eq in eq_stack:
                if asserted_eq.vars == eq_vars:
                    return asserted_eq

    def assert_bool_atom(self, atom: Var, value: bool):
        last_level = self.bool_atom_values[-1]
        last_level[atom] = value

    def get_asserted_values_for_bool_atom(self, atom: Var) -> bool | None:
        """ The value asserted for `atom` at the innermost level that has one, or None if there is none. """
        for level in reversed(self.bool_atom_values):
            # Note: `if atom_value := level.get(atom) is not None` would bind the *comparison's* result,
            # making every recorded atom - including one asserted False - read back as True.
            asserted_value = level.get(atom)
            if asserted_value is not None:
                return asserted_value
        return None

    def pop_bool_atom(self, atom: Var):
        last_level = self.bool_atom_values[-1]
        del last_level[atom]

    def assert_alias(self, var: Var, alias: Var_Alias, depth: int = -1):
        self.var_aliases[depth][var] = alias

    def get_alias(self, var: Var) -> Var_Alias | None:
        for level in reversed(self.var_aliases):
            if var in level:
                return level[var]
        return None

    def assert_hard_bound(self, bound: Relation, depth: int = -1):
        var = bound.vars[0]
        self.var_bounds[depth].setdefault(var, Value_Interval()).apply_assertion(bound)

    def get_hard_bounds(self, var: Var) -> Value_Interval:
        """ Combine the bounds on `var` known at every currently open stack frame into one interval. """
        combined = Value_Interval()
        for level in self.var_bounds:
            interval = level.get(var)
            if interval is None:
                continue
            if interval.lower_limit is not None:
                combined.try_strengthen_lower(interval.lower_limit)
            if interval.upper_limit is not None:
                combined.try_strengthen_upper(interval.upper_limit)
        return combined


def _eliminate_known_info_from_eq(eq1: Relation, eq2: Relation) -> Relation:
    """
    Detects additional information gained by eq2 from the perspective of eq1. In particular,
    we detect whether eq1 and eq2 are the same equation.
    """
    if eq1.vars[0] != eq2.vars[0]:
        return eq2

    lcm = math.lcm(eq1.coefs[0], eq2.coefs[0])

    eq1_multiplier = int(lcm / eq1.coefs[0])
    eq2_multiplier = int(lcm / eq2.coefs[0])

    eq1_multiplied = eq1.multiply_by_num(eq1_multiplier)
    eq2_multiplied = eq2.multiply_by_num(eq2_multiplier)

    return _subtract_equations(eq1_multiplied, eq2_multiplied)


def _subtract_equations(eq: Relation, other_eq: Relation) -> Relation:
    eq_vars: dict[Var, int] = {var: coef for var, coef in zip(eq.vars, eq.coefs)}

    for var, coef in zip(other_eq.vars, other_eq.coefs):
        current_coef = eq_vars.get(var, 0)
        new_coef = current_coef - coef

        if new_coef != 0:
            eq_vars[var] = new_coef
        else:
            del eq_vars[var]

    result_terms_coef_pairs: list[tuple[Var, int]] = sorted(eq_vars.items())
    result_rhs = eq.rhs - other_eq.rhs

    if not result_terms_coef_pairs:
        return Relation(vars=[], coefs=[], rhs=result_rhs, predicate_symbol='=')
    
    result_vars, result_coefs = zip(*result_terms_coef_pairs)

    return Relation(
        vars=cast(list[Var], result_vars),
        coefs=cast(list[int], result_coefs),
        rhs=result_rhs,
        predicate_symbol='='
    )


@overload
def _substitute_known_aliases(relation: Relation, assertions: Asserted_Model_Properties) -> Relation | BoolLiteral: ...

@overload
def _substitute_known_aliases(relation: Congruence, assertions: Asserted_Model_Properties) -> Congruence | BoolLiteral : ...

def _substitute_known_aliases(relation: Relation | Congruence, assertions: Asserted_Model_Properties) -> Relation | Congruence | BoolLiteral:
    """ Replace every variable in `relation` that has a known alias (e.g. x = y - 1) with its alias expression. """
    new_terms: dict[Var, int] = defaultdict(int)
    abs_term = 0
    substituted_anything = False

    for var, coef in zip(relation.vars, relation.coefs):
        alias = assertions.get_alias(var)
        if alias is None:
            new_terms[var] = new_terms[var] + coef
            continue

        substituted_anything = True
        for alias_var, alias_coef in zip(alias.vars, alias.coefs):
            new_terms[alias_var] = new_terms[alias_var] + coef * alias_coef
        abs_term += coef * alias.const

    if not substituted_anything:
        return relation

    sorted_terms = sorted((var, coef) for var, coef in new_terms.items() if coef != 0)
    if isinstance(relation, Congruence):
        sorted_terms = [(var, coef) for var, coef in sorted_terms if (coef % relation.modulus != 0)]
    
    new_vars = [var for var, _ in sorted_terms]
    new_coefs = [coef for _, coef in sorted_terms]
    new_rhs = relation.rhs - abs_term

    if not new_coefs:
        return BoolLiteral(True)

    if isinstance(relation, Relation):
        return Relation(vars=new_vars, coefs=new_coefs, rhs=new_rhs, predicate_symbol=relation.predicate_symbol)
    else:
        # We are dealing with a congruence
        new_rhs = new_rhs % relation.modulus
        return Congruence(vars=new_vars, coefs=new_coefs, rhs=new_rhs, modulus=relation.modulus)


def _try_extract_alias(equation: Relation, assertions: Asserted_Model_Properties) -> tuple[Var, Var_Alias] | None:
    """
    If `equation` has a variable with a unit coefficient, express it as an alias of the remaining terms,
    e.g. `x - y = 1` (x has a unit coefficient) becomes the alias `x = y + 1`.
    """
    unit_coef_vars = [(var, coef) for var, coef in zip(equation.vars, equation.coefs) if abs(coef) == 1]
    if not unit_coef_vars:
        return None

    # Prefer eliminating the variable owned by the most deeply nested currently open quantifier -
    # this guarantees every other variable remaining in the alias expression is bound at an
    # equal-or-wider scope than elim_var, so the expression stays meaningful for as long as
    # elim_var's own binder could have been referenced. Picking an outer-scoped variable instead
    # (e.g. by id, as before) can alias it to an expression that mentions an *inner*-scoped
    # variable; once that inner variable's own (unrelated) binder is later dropped, the alias
    # becomes a dangling reference wherever it still gets substituted in.
    scoped_candidates = [
        (var, coef, scope_index)
        for var, coef in unit_coef_vars
        if (scope_index := assertions.find_owning_quantifier_scope_index(var)) is not None
    ]
    if scoped_candidates:
        elim_var, elim_coef, _ = max(scoped_candidates, key=lambda item: (item[2], item[0].id))
    else:
        # None of the candidates are bound by any currently open quantifier (e.g. they are all
        # free/global formula parameters) - there is no binder at stake, so the original
        # (arbitrary but deterministic) choice is fine.
        elim_var, elim_coef = max(unit_coef_vars, key=lambda var_coef: var_coef[0].id)

    remaining_terms = [(var, coef) for var, coef in zip(equation.vars, equation.coefs) if var != elim_var]

    # elim_coef*elim_var + sum(remaining) = rhs  <=>  elim_var = elim_coef*rhs - elim_coef*sum(remaining)  (elim_coef is +-1)
    alias_vars = [var for var, _coef in remaining_terms]
    alias_coefs = [-elim_coef * coef for _var, coef in remaining_terms]
    alias_const = elim_coef * equation.rhs

    return elim_var, Var_Alias(vars=alias_vars, coefs=alias_coefs, const=alias_const)


def _register_unresolved_equation(equation: Relation, assertions: Asserted_Model_Properties) -> ASTp_Node | None:
    """
    Remember `equation` for future simplifications - either as a variable alias, or verbatim.

    If the eliminated variable is bound by an enclosing quantifier, and `equation` is unconditionally
    true throughout that quantifier's whole body, then the variable has effectively been "asserted"
    by this equation already - the equation itself is therefore redundant (its only remaining job,
    substituting the variable away everywhere else, is handled separately) and can be dropped, which
    this signals by returning BoolLiteral(True); the AST_Quantifier node will drop the now-unused
    binding once this bubbles back up to it. Otherwise, returns None - the caller should keep the
    (possibly already-substituted) equation as-is.
    """
    if not assertions.is_unconditionally_true_for_current_stack_frame():
        # We are nested under a NOT relative to the enclosing AND/OR branch, so `equation` is not
        # implied by that branch - remembering it (as an alias or verbatim) would let it leak into
        # unrelated positions that share the same branch but not the same negation context.
        return None

    # Record at the widest frame this equation is unconditionally valid throughout (not just the
    # innermost AND/OR branch it was found in), so it stays visible to sibling branches nested
    # under the same enclosing quantifier(s) instead of disappearing once its own frame is popped.
    target_depth = assertions.get_widest_valid_stack_depth()

    alias = _try_extract_alias(equation, assertions)
    if alias is None:
        assertions.assert_equation(equation, depth=target_depth)
        return None

    elim_var, var_alias = alias

    # The alias expression can reference other bound variables (e.g. `x = y + z`, all three
    # existentially bound). It must never be promoted past the point where any of those variables'
    # own binder could be dropped - otherwise, once that happens, substituting the alias elsewhere
    # would reintroduce that variable with no binder left anywhere in the formula. Cap the depth to
    # the innermost (most restrictive) such dependency's own body frame.
    for dependency_var in var_alias.vars:
        dependency_scope_index = assertions.find_owning_quantifier_scope_index(dependency_var)
        if dependency_scope_index is None:
            continue
        dependency_body_depth = assertions.get_own_body_stack_depth(dependency_scope_index)
        target_depth = max(target_depth, dependency_body_depth)

    assertions.assert_alias(elim_var, var_alias, depth=target_depth)

    # If elim_var already appears, unsubstituted, in some earlier-processed sibling that has been
    # fixed into the result tree, its binder must stay - dropping it now would leave that earlier
    # reference with no binder anywhere in the formula. The alias itself is still recorded above, so
    # it keeps being applied to substitute elim_var away everywhere it is still *about* to be seen.
    if elim_var in assertions.vars_referenced_unsubstituted:
        return None

    if assertions.is_unconditionally_true_for_owning_quantifier(elim_var):
        assertions.vars_eliminated_via_alias.add(elim_var)
        return BoolLiteral(True)

    return None


def _count_var_uses_excluding_hard_bounds(root_node: ASTp_Node, counts: dict[Var, int]) -> None:
    """ Count, for every variable, how many Relations (other than hard bounds) or Congruences reference it. """
    match root_node:
        case Var() | BoolLiteral():
            pass
        case Relation():
            if root_node.is_hard_bound():
                return
            for var in root_node.vars:
                counts[var] = counts.get(var, 0) + 1
        case Congruence():
            for var in root_node.vars:
                counts[var] = counts.get(var, 0) + 1
        case AST_Connective():
            for child in root_node.children:
                _count_var_uses_excluding_hard_bounds(child, counts)
        case AST_Negation() | AST_Quantifier():
            _count_var_uses_excluding_hard_bounds(root_node.child, counts)
        case _:
            raise ValueError(f'Unhandled node type when counting variable uses: {type(root_node)} :: {root_node}')


def _find_vars_covered_by_hard_bounds(congruence: Congruence, assertions: Asserted_Model_Properties) -> set[Var]:
    """
    Find the subset of `congruence`'s variables that are free enough - not used anywhere else in the
    formula, and hard-bounded over an interval at least as wide as the period their own coefficient
    cycles through modulo `congruence.modulus` - to be picked, independently of everything else, so
    that their term takes on any value in the residue class it can reach.

    If the combined gcd of such variables' coefficients (and the modulus) is 1, they can jointly reach
    *every* residue mod `congruence.modulus`, so the congruence holds no matter what the remaining
    terms add up to, and can be dropped along with its hard bounds. An empty result means no such
    combination was found.
    """
    covering_vars: list[Var] = []
    covering_coefs: list[int] = []

    for var, coef in zip(congruence.vars, congruence.coefs):
        if assertions.var_uses_excluding_hard_bounds.get(var, 0) > 1:
            continue

        bounds = assertions.get_hard_bounds(var)
        if bounds.lower_limit is None or bounds.upper_limit is None:
            continue

        period = congruence.modulus // math.gcd(coef, congruence.modulus)
        if (bounds.upper_limit - bounds.lower_limit + 1) < period:
            continue

        covering_vars.append(var)
        covering_coefs.append(coef)

    if not covering_vars or math.gcd(*covering_coefs, congruence.modulus) != 1:
        return set()

    return set(covering_vars)


def simplify_formula_using_model_properties(root_node: ASTp_Node, assertions: Asserted_Model_Properties) -> ASTp_Node:
    """
    Simplify formula by considering its models.

    Examples:
    AND:                    ---->    AND
       x - y = 0                        x - y = 0
       OR                               OR
          ...                               ...
          NOT x - y = 0                     FALSE

    AND:                    ---->    AND
       x - y = 0                        x - y = 0
       2*y + x + z = 3                  3*x + z = 3     (y is known to equal x, substituted away)
    """
    # Recomputed on every top-level call (never mid-recursion) against the *current* formula, so the
    # congruence/hard-bounds simplification below has an accurate, order-independent answer to "is
    # this variable used anywhere else" - unlike the scope-stacked facts above, this must not miss a
    # use the in-order traversal has not reached yet, nor go stale across repeated top-level calls.
    assertions.var_uses_excluding_hard_bounds.clear()
    _count_var_uses_excluding_hard_bounds(root_node, assertions.var_uses_excluding_hard_bounds)
    return _simplify_formula_using_model_properties(root_node, assertions)


def _simplify_formula_using_model_properties(root_node: ASTp_Node, assertions: Asserted_Model_Properties) -> ASTp_Node:
    match root_node:
        case Var():
            asserted_value = assertions.get_asserted_values_for_bool_atom(root_node)
            if asserted_value is None:
                assertions.assert_bool_atom(root_node, True)
                return root_node
            return BoolLiteral(asserted_value)

        case BoolLiteral():
            return root_node

        case Congruence():
            rewritten_congruence: Congruence | BoolLiteral = _substitute_known_aliases(root_node, assertions)
            if isinstance(rewritten_congruence, BoolLiteral):
                return rewritten_congruence

            # Keep coefficients canonical (in [0, modulus)), whether or not the alias substitution
            # above actually changed anything - substitution combines coefficients (`coef * alias_coef`)
            # without reducing them, so a substituted congruence's coefficients can otherwise end up
            # negative or >= modulus.
            rewritten_congruence = rewritten_congruence.with_coefficients_reduced_mod_modulus()
            if isinstance(rewritten_congruence, BoolLiteral):
                return rewritten_congruence

            # Substituting an alias in can concentrate what used to be several independent
            # variables' worth of "wiggle room" into one coefficient shared by all of them (e.g.
            # x = 4194304*(a+b+c+d) turns a lone `x` coefficient into one shared by a, b, c, d) -
            # gcd(coefs, modulus) can end up not dividing rhs even though it did before the
            # substitution. Catch that here, right after each substitution, instead of leaving it
            # for the backend to discover the hard way by building (and blowing up on) an automaton
            # for an atom that can never be satisfied.
            if rewritten_congruence.is_unsat():
                return BoolLiteral(False)

            covered_vars = _find_vars_covered_by_hard_bounds(rewritten_congruence, assertions)
            if covered_vars:
                # These variables' own hard bounds already guarantee the congruence always holds -
                # the bounds are now redundant too, so the Relation() case drops them on sight.
                assertions.vars_covered_by_congruence_bounds.update(covered_vars)
                return BoolLiteral(True)

            # No alias is known for any variable still left in `rewritten_congruence` (aliases were
            # already substituted above) - fix that in, so a later alias for one of them can no
            # longer be used to drop its binder without leaving this reference dangling.
            assertions.vars_referenced_unsubstituted.update(rewritten_congruence.vars)
            return rewritten_congruence

        case Relation():
            # Replace every variable with a known alias (e.g. x = y - 1) before doing anything else - this
            # also makes the duplicate/implied-equation detection below strictly more effective, since two
            # equations that only differed by an already-known alias will now compare equal.
            substituted = _substitute_known_aliases(root_node, assertions)

            if isinstance(substituted, BoolLiteral):
                return substituted

            is_constant = substituted.is_true_or_false()
            if is_constant is not None:
                return BoolLiteral(is_constant)

            if substituted.predicate_symbol != '=':
                if substituted.is_hard_bound():
                    bound_var = substituted.vars[0]
                    if bound_var in assertions.vars_covered_by_congruence_bounds:
                        return BoolLiteral(True)
                    if assertions.is_unconditionally_true_for_current_stack_frame():
                        # Promoted to the widest frame the bound is unconditionally valid throughout,
                        # same as equations, so it stays visible to sibling branches nested under the
                        # same enclosing quantifier(s) instead of disappearing once its own frame pops.
                        assertions.assert_hard_bound(substituted, depth=assertions.get_widest_valid_stack_depth())

                assertions.vars_referenced_unsubstituted.update(substituted.vars)
                return substituted

            # TODO: This is sketchy, we should have a heuristic that tries to combine similar-enough equations
            #       to obtain implications that should produce smaller automata/prune the formula.
            similar_eq = assertions.search_similar_eq(substituted)
            if not similar_eq:
                absorbed = _register_unresolved_equation(substituted, assertions)
                if absorbed is None:
                    assertions.vars_referenced_unsubstituted.update(substituted.vars)
                return absorbed if absorbed is not None else substituted

            implication = _eliminate_known_info_from_eq(substituted, similar_eq)
            simplified_value = implication.is_true_or_false()

            if simplified_value is None:
                # TODO: Maybe we should keep the simplified relation here instead? For example, if there are less variables, or
                # the coefficients are smaller? Right now we do nothing
                absorbed = _register_unresolved_equation(substituted, assertions)
                if absorbed is None:
                    assertions.vars_referenced_unsubstituted.update(substituted.vars)
                return absorbed if absorbed is not None else substituted

            return BoolLiteral(simplified_value)

        case AST_Connective():
            match root_node.type:
                case Connective_Type.AND:
                    assertions.insert_stack()
                    new_children = tuple(
                        _simplify_formula_using_model_properties(subformula, assertions)
                        for subformula in root_node.children
                    )
                    assertions.pop_stack()

                    # TODO: We should do these simplifications greedily while we are making progress.
                    # assertions.insert_stack()
                    # new_children = tuple(
                    #    _simplify_formula_using_model_properties(subformula, assertions)
                    #    for subformula in new_children
                    # )
                    # assertions.pop_stack()

                case Connective_Type.OR | Connective_Type.EQUIV:
                    new_children = []
                    for subformula in root_node.children:
                        assertions.insert_stack()
                        assertions.enter_branch()
                        new_child = _simplify_formula_using_model_properties(subformula, assertions)
                        assertions.exit_branch()
                        assertions.pop_stack()

                        new_children.append(new_child)
                    new_children = tuple(new_children)
            
            result = AST_Connective(referenced_vars=root_node.referenced_vars, type=root_node.type, children=new_children)

            result = result.simplify_on_anihilators()
            if not isinstance(result, AST_Connective):
                return result

            result = result.remove_idempotent_children()
            if not isinstance(result, AST_Connective):
                return result

            result = result.simplify_on_exclusion_on_the_third()
            return result

        case AST_Negation():
            if isinstance(root_node.child, Var):
                var_value = assertions.get_asserted_values_for_bool_atom(root_node.child)

                if var_value is None:
                    assertions.assert_bool_atom(root_node.child, False)
                    return root_node

                return BoolLiteral(value=not var_value)

            
            assertions.enter_negation()
            new_child = _simplify_formula_using_model_properties(root_node.child, assertions)
            assertions.exit_negation()

            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(value=not new_child.value)

            if isinstance(new_child, Var):
                assertions.assert_bool_atom(new_child, False)

            result = AST_Negation(referenced_vars=root_node.referenced_vars, child=new_child)
            return result

        case AST_Quantifier():
            assertions.enter_quantifier_scope(root_node.bound_vars)
            new_child = _simplify_formula_using_model_properties(root_node.child, assertions)
            assertions.exit_quantifier_scope()

            if isinstance(new_child, BoolLiteral):
                assertions.vars_eliminated_via_alias.difference_update(root_node.bound_vars)
                return new_child

            remaining_bound_vars = tuple(
                var for var in root_node.bound_vars if var not in assertions.vars_eliminated_via_alias
            )
            assertions.vars_eliminated_via_alias.difference_update(root_node.bound_vars)

            if not remaining_bound_vars:
                return new_child

            result = AST_Quantifier(
                referenced_vars=root_node.referenced_vars,
                bound_vars=remaining_bound_vars,
                child=new_child
            )
            return result

    raise ValueError(f'Unhandled node type when simplyfing using model properties: {type(root_node)}')


@dataclass
class Bool_Var_Uses:
    positive: int = 0
    negative: int = 0


@dataclass
class Variable_Use_Info:
    relation_uses: dict[Var, list[Relation]] = field(default_factory=lambda: defaultdict(list))
    congruence_uses: dict[Var, list[Congruence]] = field(default_factory=lambda: defaultdict(list))
    bool_var_uses: dict[Var, Bool_Var_Uses] = field(default_factory=lambda: defaultdict(Bool_Var_Uses)) 

    next_available_relation_id = 0

    def is_var_used_only_once(self, var: Var) -> bool:
        rel_uses = self.relation_uses[var]
        congruence_uses = self.congruence_uses[var]
        return len(rel_uses) + len(congruence_uses) <= 1

    def get_bool_var_desired_value(self, var: Var) -> bool | None:
        var_uses = self.bool_var_uses[var]
        if var_uses.positive > 0 and var_uses.negative == 0:
            return True
        elif var_uses.positive == 0 and var_uses.negative > 0:
            return False
        return None

    def add_int_var_use(self, var: Var, use: Relation): 
        self.relation_uses[var].append(use)

    def add_var_use_in_congruence(self, var: Var, use: Congruence): 
        self.congruence_uses[var].append(use)

    def add_positive_bool_var_use(self, bool_var: Var):
        self.bool_var_uses[bool_var].positive += 1

    def add_negative_bool_var_use(self, bool_var: Var):
        self.bool_var_uses[bool_var].negative += 1

    def ensure_relation_id_is_set(self, relation: Relation | Congruence):
        if relation.id >= 0:
            return

        relation.id = self.next_available_relation_id
        self.next_available_relation_id += 1
        

def scan_variable_use(root_node: ASTp_Node, var_use: Variable_Use_Info):
    match root_node:
        case Var():
            # TODO: Implement polarity tracking
            var_use.add_positive_bool_var_use(root_node)
            var_use.add_negative_bool_var_use(root_node)

        case BoolLiteral():
            pass

        case Congruence():
            var_use.ensure_relation_id_is_set(root_node)
            for var in root_node.vars:
                var_use.add_var_use_in_congruence(var, root_node)

        case Relation():
            var_use.ensure_relation_id_is_set(root_node)
            for var in root_node.vars:
                var_use.add_int_var_use(var, root_node)

        case AST_Connective():
            for child in root_node.children:
                scan_variable_use(child, var_use)

        case AST_Negation() | AST_Quantifier():
            scan_variable_use(root_node.child, var_use)

        case _:
            raise ValueError(f'Unhandled node type when scanning variable use: {type(root_node)} :: {root_node}')


def remove_atoms_satisfied_by_unconstrained_vars(root_node: ASTp_Node,
                                                 var_uses: Variable_Use_Info,
                                                 desired_polarity: bool) -> ASTp_Node:
    match root_node:
        case BoolLiteral():
            return root_node

        case Var():
            desired_value = var_uses.get_bool_var_desired_value(root_node)

            if desired_value is True:
                return BoolLiteral(True)
            elif desired_value is False:
                return BoolLiteral(False)

            return root_node

        case Relation():
            unconstrained_var_coefs = [
                coef for var, coef in zip(root_node.vars, root_node.coefs) if var_uses.is_var_used_only_once(var)
            ]

            if not unconstrained_var_coefs:
                return root_node

            if root_node.predicate_symbol == '=':
                # A variable used nowhere else can absorb any value the relation's other terms take
                # (making the relation trivially true regardless of them) only if it - or, jointly,
                # the unconstrained variables together - can reach every residue, i.e. their combined
                # gcd is 1 (e.g. a lone unconstrained variable needs coefficient +-1; two of them with
                # coefficients 2 and 3 can jointly reach any residue too). A coefficient (or gcd) like
                # 4194304 can only ever make the relation's variable(s) land on a multiple of 4194304,
                # not an arbitrary value - dropping the relation in that case would silently discard a
                # real constraint (e.g. `x = 4194304*y` does NOT mean x is unconstrained).
                if math.gcd(*unconstrained_var_coefs) != 1:
                    return root_node
            # For '<'/'<=', any nonzero coefficient on an otherwise-unconstrained variable already
            # lets it be driven towards +-infinity in the right direction to satisfy the relation
            # regardless of the other terms' value - no gcd condition needed.

            return BoolLiteral(True)  # This relation gives us no information about models

        case Congruence():
            return root_node

        case AST_Connective():
            new_children = tuple(
                remove_atoms_satisfied_by_unconstrained_vars(child, var_uses, desired_polarity)
                for child in root_node.children
            )

            result = AST_Connective(referenced_vars=(), type=root_node.type, children=new_children)
            result = result.simplify_on_anihilators()

            if isinstance(result, BoolLiteral):
                return result

            result = result.remove_idempotent_children()
            return result
                    
        case AST_Quantifier():
            new_child = remove_atoms_satisfied_by_unconstrained_vars(root_node.child, var_uses, desired_polarity)
            kept_vars = tuple(var for var in root_node.bound_vars if ast_references_var(new_child, var))

            if isinstance(new_child, BoolLiteral):
                return new_child
            
            if not kept_vars:
                return new_child

            return AST_Quantifier(referenced_vars=tuple(), bound_vars=kept_vars, child=new_child)                

        case AST_Negation():
            new_polarity = not desired_polarity

            # Perform look-ahead since we are using True to say that a relation
            # gives no information about models (how it restricts the remaining
            # variables). Negating True would give us False, which is not what
            # we want -- we really want to say that anything partial assignment
            # to the remaining variables can be completed to a model (which is
            # definitely not False).
            #
            # Maybe we should introduce a new (temporary) node type for this kind
            # of optimisation. For now, we rely on the fact that we always push negations
            # maximally inwards.
            if isinstance(root_node.child, Relation):
                relation: Relation = root_node.child
                for var in relation.vars:
                    if var_uses.is_var_used_only_once(var):
                        result = BoolLiteral(True)
                        return result

            new_child = remove_atoms_satisfied_by_unconstrained_vars(root_node.child, var_uses, new_polarity)

            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(value=not new_child.value)

            return AST_Negation(referenced_vars=(), child=new_child)

        case _:
            raise ValueError(f'Unhandled node type when removing atoms on unconstrained vars: {root_node}')
