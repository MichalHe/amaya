from dataclasses import dataclass, field
from typing import cast

from amaya.relations_structures import AST_Connective, AST_Negation, ASTp_Node, BoolLiteral, Connective_Type, Relation, Var


@dataclass
class Asserted_Model_Properties:
    equations: list[Relation] = field(default_factory=list)
    bool_atom_values: list[dict[Var, bool]] = field(default_factory=lambda: [{}])

    def insert_stack(self):
        self.bool_atom_values.append(dict())

    def pop_stack(self):
        self.bool_atom_values.pop(-1)

    def negate_last_level(self):
        last_level = self.bool_atom_values[-1]
        for var, var_value in last_level.items():
            last_level[var] = not var_value

    def assert_equation(self, eq: Relation):
        eq.sort_variables()
        self.equations.append(eq)

    def pop_eq(self, count: int):
        for _ in range(count):
            self.equations.pop(-1)

    def search_similar_eq(self, eq: Relation) -> Relation | None:
        eq_vars = sorted(eq.vars)

        for asserted_eq in self.equations:
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
                       
        case Relation():
            if root_node.predicate_symbol != '=':
                return root_node

            # TODO: This is sketchy, we should have a heuristic that tries to combine similar-enough equations
            #       to obtain implications that should produce smaller automata/prune the formula.
            similar_eq = assertions.search_similar_eq(root_node)
            if not similar_eq:
                assertions.assert_equation(root_node)
                return root_node

            implication = _subtract_equations(root_node, similar_eq)
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
                    new_children = tuple(
                        simplify_formula_using_model_properties(subformula, assertions)
                        for subformula in root_node.children
                    )
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
            new_child = simplify_formula_using_model_properties(root_node.child, assertions)
            if isinstance(new_child, BoolLiteral):
                return BoolLiteral(value=not new_child.value)

            if isinstance(new_child, Var):
                assertions.assert_bool_atom(new_child, False)

            result = AST_Negation(referenced_vars=root_node.referenced_vars, child=new_child)
            return result

    raise ValueError(f'Unhandled node type when simplyfing using model properties: {type(root_node)}')

