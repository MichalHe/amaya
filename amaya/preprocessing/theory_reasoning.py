from collections import defaultdict
from dataclasses import dataclass, field
from typing import Iterable, cast
import math
import itertools

from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Node,
    ASTp_Node_Base,
    BoolLiteral,
    Connective_Type,
    Relation,
    Var,
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

    branch_depth: int = 0
    """ How many OR/EQUIV branch boundaries we are currently nested under. """

    negation_depth: int = 0
    """ How many NOTs we are currently nested under. """

    quantifier_scopes: list[tuple[frozenset[Var], int, int]] = field(default_factory=list)
    """
    Stack of currently open quantifiers: (their bound vars, branch_depth, negation_depth) as they
    were when we entered that quantifier's body.
    """

    vars_eliminated_via_alias: set[Var] = field(default_factory=set)
    """
    Bound variables whose defining equation was dropped because they were fully substituted away.
    Consumed (and removed from this set) by the AST_Quantifier node that binds them.
    """

    def insert_stack(self):
        self.equations.append([])
        self.bool_atom_values.append(dict())
        self.var_aliases.append(dict())

    def pop_stack(self):
        self.bool_atom_values.pop(-1)
        self.equations.pop(-1)
        self.var_aliases.pop(-1)

    def enter_branch(self):
        self.branch_depth += 1

    def exit_branch(self):
        self.branch_depth -= 1

    def enter_negation(self):
        self.negation_depth += 1

    def exit_negation(self):
        self.negation_depth -= 1

    def enter_quantifier_scope(self, bound_vars: tuple[Var, ...]):
        self.quantifier_scopes.append((frozenset(bound_vars), self.branch_depth, self.negation_depth))

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
        for bound_vars, entry_branch_depth, entry_negation_depth in reversed(self.quantifier_scopes):
            if var in bound_vars:
                return entry_branch_depth == self.branch_depth and entry_negation_depth == self.negation_depth
        return False

    def negate_last_level(self):
        last_level = self.bool_atom_values[-1]
        for var, var_value in last_level.items():
            last_level[var] = not var_value

    def assert_equation(self, eq: Relation):
        eq.sort_variables()
        self.equations[-1].append(eq)

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
        for level in reversed(self.bool_atom_values):
            if atom_value := level.get(atom) is not None:
                return atom_value

    def pop_bool_atom(self, atom: Var):
        last_level = self.bool_atom_values[-1]
        del last_level[atom]

    def assert_alias(self, var: Var, alias: Var_Alias):
        self.var_aliases[-1][var] = alias

    def get_alias(self, var: Var) -> Var_Alias | None:
        for level in reversed(self.var_aliases):
            if var in level:
                return level[var]
        return None


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


def _substitute_known_aliases(relation: Relation, assertions: Asserted_Model_Properties) -> Relation:
    """ Replace every variable in `relation` that has a known alias (e.g. x = y - 1) with its alias expression. """
    new_terms: dict[Var, int] = {}
    const_shift = 0
    substituted_anything = False

    for var, coef in zip(relation.vars, relation.coefs):
        alias = assertions.get_alias(var)
        if alias is None:
            new_terms[var] = new_terms.get(var, 0) + coef
            continue

        substituted_anything = True
        for alias_var, alias_coef in zip(alias.vars, alias.coefs):
            new_terms[alias_var] = new_terms.get(alias_var, 0) + coef * alias_coef
        const_shift += coef * alias.const

    if not substituted_anything:
        return relation

    sorted_terms = sorted((var, coef) for var, coef in new_terms.items() if coef != 0)
    new_vars = [var for var, _ in sorted_terms]
    new_coefs = [coef for _, coef in sorted_terms]
    new_rhs = relation.rhs - const_shift

    return Relation(vars=new_vars, coefs=new_coefs, rhs=new_rhs, predicate_symbol=relation.predicate_symbol)


def _try_extract_alias(equation: Relation) -> tuple[Var, Var_Alias] | None:
    """
    If `equation` has a variable with a unit coefficient, express it as an alias of the remaining terms,
    e.g. `x - y = 1` (x has a unit coefficient) becomes the alias `x = y + 1`.
    """
    unit_coef_vars = [(var, coef) for var, coef in zip(equation.vars, equation.coefs) if abs(coef) == 1]
    if not unit_coef_vars:
        return None

    # Prefer eliminating the variable with the largest id, keeping lower-id variables as canonical.
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
    alias = _try_extract_alias(equation)
    if alias is None:
        assertions.assert_equation(equation)
        return None

    elim_var, var_alias = alias
    assertions.assert_alias(elim_var, var_alias)

    if assertions.is_unconditionally_true_for_owning_quantifier(elim_var):
        assertions.vars_eliminated_via_alias.add(elim_var)
        return BoolLiteral(True)

    return None


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
    match root_node:
        case Var():
            asserted_value = assertions.get_asserted_values_for_bool_atom(root_node)
            if asserted_value is None:
                assertions.assert_bool_atom(root_node, True)
                return root_node
            return BoolLiteral(asserted_value)

        case BoolLiteral():
            return root_node
                       
        case Relation():
            # Replace every variable with a known alias (e.g. x = y - 1) before doing anything else - this
            # also makes the duplicate/implied-equation detection below strictly more effective, since two
            # equations that only differed by an already-known alias will now compare equal.
            substituted = _substitute_known_aliases(root_node, assertions)

            is_constant = substituted.is_true_or_false()
            if is_constant is not None:
                return BoolLiteral(is_constant)

            if substituted.predicate_symbol != '=':
                return substituted

            # TODO: This is sketchy, we should have a heuristic that tries to combine similar-enough equations
            #       to obtain implications that should produce smaller automata/prune the formula.
            similar_eq = assertions.search_similar_eq(substituted)
            if not similar_eq:
                absorbed = _register_unresolved_equation(substituted, assertions)
                return absorbed if absorbed is not None else substituted

            implication = _eliminate_known_info_from_eq(substituted, similar_eq)
            simplified_value = implication.is_true_or_false()

            if simplified_value is None:
                # TODO: Maybe we should keep the simplified relation here instead? For example, if there are less variables, or
                # the coefficients are smaller? Right now we do nothing
                absorbed = _register_unresolved_equation(substituted, assertions)
                return absorbed if absorbed is not None else substituted

            return BoolLiteral(simplified_value)

        case AST_Connective():
            match root_node.type:
                case Connective_Type.AND:
                    assertions.insert_stack()
                    new_children = tuple(
                        simplify_formula_using_model_properties(subformula, assertions)
                        for subformula in root_node.children
                    )
                    assertions.pop_stack()

                    # TODO: We should do these simplifications greedily while we are making progress.
                    # assertions.insert_stack()
                    # new_children = tuple(
                    #    simplify_formula_using_model_properties(subformula, assertions)
                    #    for subformula in new_children
                    # )
                    # assertions.pop_stack()

                case Connective_Type.OR | Connective_Type.EQUIV:
                    new_children = []
                    for subformula in root_node.children:
                        assertions.insert_stack()
                        assertions.enter_branch()
                        new_child = simplify_formula_using_model_properties(subformula, assertions)
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

                if not var_value:
                    assertions.assert_bool_atom(root_node.child, False)
                    return root_node

                return BoolLiteral(value=var_value)

            
            assertions.enter_negation()
            new_child = simplify_formula_using_model_properties(root_node.child, assertions)
            assertions.exit_negation()

            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(value=not new_child.value)

            if isinstance(new_child, Var):
                assertions.assert_bool_atom(new_child, False)

            result = AST_Negation(referenced_vars=root_node.referenced_vars, child=new_child)
            return result

        case AST_Quantifier():
            assertions.enter_quantifier_scope(root_node.bound_vars)
            new_child = simplify_formula_using_model_properties(root_node.child, assertions)
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
    bool_var_uses: dict[Var, Bool_Var_Uses] = field(default_factory=lambda: defaultdict(Bool_Var_Uses)) 

    next_available_relation_id = 0

    def is_var_used_only_once(self, var: Var) -> bool:
        var_uses = self.relation_uses[var]
        return len(var_uses) <= 1

    def delete_all_relatations_containing_to_a_var(self, var: Var):
        """
        Delete all stored relations that contain a var.
        """
        relation_ids_to_delete_from_other_vars = list(rel.id for rel in self.relation_uses[var])

        assert all(_id != -1 for _id in relation_ids_to_delete_from_other_vars)

        del self.relation_uses[var]

        for var in self.relation_uses:
            var_relations = self.relation_uses[var]
            var_relations = [rel for rel in var_relations if rel.id not in relation_ids_to_delete_from_other_vars]
            self.relation_uses[var] = var_relations

    def get_bool_var_desired_value(self, var: Var) -> bool | None:
        var_uses = self.bool_var_uses[var]
        if var_uses.positive > 0 and var_uses.negative == 0:
            return True
        elif var_uses.positive == 0 and var_uses.negative > 0:
            return False
        return None

    def add_int_var_use(self, var: Var, use: Relation): 
        self.relation_uses[var].append(use)

    def add_positive_bool_var_use(self, bool_var: Var):
        self.bool_var_uses[bool_var].positive += 1

    def add_negative_bool_var_use(self, bool_var: Var):
        self.bool_var_uses[bool_var].negative += 1

    def ensure_relation_id_is_set(self, relation: Relation):
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
            for var in root_node.vars:
                if var_uses.is_var_used_only_once(var):
                    var_uses.delete_all_relatations_containing_to_a_var(var)
                    result = BoolLiteral(True)  # This relation gives us no information about models
                    return result
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
            kept_vars = tuple(var for var in root_node.bound_vars if not var_uses.is_var_used_only_once(var))
            new_child = remove_atoms_satisfied_by_unconstrained_vars(root_node.child, var_uses, desired_polarity)

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
                        var_uses.delete_all_relatations_containing_to_a_var(var)
                        result = BoolLiteral(True)
                        return result

            new_child = remove_atoms_satisfied_by_unconstrained_vars(root_node.child, var_uses, new_polarity)

            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(value=not new_child.value)

            return AST_Negation(referenced_vars=(), child=new_child)

        case _:
            raise ValueError(f'Unhandled node type when removing atoms on unconstrained vars: {root_node}')
