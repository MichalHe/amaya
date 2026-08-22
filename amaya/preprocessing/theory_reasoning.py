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
class Asserted_Model_Properties:
    equations: list[list[Relation]] = field(default_factory=lambda: [[]])
    bool_atom_values: list[dict[Var, bool]] = field(default_factory=lambda: [{}])

    def insert_stack(self):
        self.equations.append([])
        self.bool_atom_values.append(dict())

    def pop_stack(self):
        self.bool_atom_values.pop(-1)
        self.equations.pop(-1)

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


def simplify_formula_using_model_properties(root_node: ASTp_Node, assertions: Asserted_Model_Properties) -> ASTp_Node:
    """
    Simplify formula by considering its models. 

    Examples:
    AND:                    ---->    AND
       x - y = 0                        x - y = 0
       OR                               OR
          ...                               ...
          NOT x - y = 0                     FALSE
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
            if root_node.predicate_symbol != '=':
                return root_node

            # TODO: This is sketchy, we should have a heuristic that tries to combine similar-enough equations
            #       to obtain implications that should produce smaller automata/prune the formula.
            similar_eq = assertions.search_similar_eq(root_node)
            if not similar_eq:
                assertions.assert_equation(root_node)
                return root_node

            implication = _eliminate_known_info_from_eq(root_node, similar_eq)
            simplified_value = implication.is_true_or_false()

            if simplified_value is None:
                # TODO: Maybe we should keep the simplified relation here instead? For example, if there are less variables, or
                # the coefficients are smaller? Right now we do nothing
                assertions.assert_equation(root_node)
                return root_node

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
                        new_child = simplify_formula_using_model_properties(subformula, assertions)
                        assertions.pop_stack()

                        new_children.append(new_child)
                    new_children = tuple(new_children)

            result = AST_Connective(referenced_vars=root_node.referenced_vars, type=root_node.type, children=new_children)
            result = result.simplify_on_anihilators()
            if not isinstance(result, AST_Connective):
                return result
            result = result.remove_idempotent_children()
            return result

        case AST_Negation():
            # TODO: We are missing assertion barriers here
            new_child = simplify_formula_using_model_properties(root_node.child, assertions)
            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(value=not new_child.value)

            if isinstance(new_child, Var):
                assertions.assert_bool_atom(new_child, False)

            result = AST_Negation(referenced_vars=root_node.referenced_vars, child=new_child)
            return result

        case AST_Quantifier():
            new_child = simplify_formula_using_model_properties(root_node.child, assertions)
            if isinstance(new_child, BoolLiteral):
                return new_child

            result = AST_Quantifier(
                referenced_vars=root_node.referenced_vars,
                bound_vars=root_node.bound_vars,
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
