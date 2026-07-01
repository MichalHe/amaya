from amaya.preprocessing.theory_reasoning import Asserted_Model_Properties, simplify_formula_using_model_properties
from amaya.relations_structures import AST_Connective, AST_Negation, BoolLiteral, Connective_Type, Relation, Var


def test_simple_bool_simplification():
    formula = AST_Connective(
        referenced_vars=(),
        type=Connective_Type.AND,
        children=(
            Var(id=1),
            AST_Negation(referenced_vars=(), child=Var(id=1))
        )
    )

    assertions = Asserted_Model_Properties()
    simplified_formula = simplify_formula_using_model_properties(formula, assertions)

    expected_result = BoolLiteral(False)

    assert simplified_formula == expected_result


def test_simple_arith_simplification():
    formula = AST_Connective(
        referenced_vars=(),
        type=Connective_Type.AND,
        children=(
            Relation(vars=[Var(1), Var(2)], coefs=[1, -1], rhs=0, predicate_symbol='='),
            AST_Negation(
                referenced_vars=(),
                child=Relation(vars=[Var(1), Var(2)], coefs=[1, -1], rhs=0, predicate_symbol='=')
            )
        )
    )

    assertions = Asserted_Model_Properties()
    simplified_formula = simplify_formula_using_model_properties(formula, assertions)

    expected_result = BoolLiteral(False)

    assert simplified_formula == expected_result


def test_simple_bool_simplification_2():
    formula = AST_Connective(
        referenced_vars=(),
        type=Connective_Type.AND,
        children=(
            Var(id=1),
            AST_Connective(
                referenced_vars=(),
                type=Connective_Type.OR,
                children=(
                    AST_Negation(referenced_vars=(), child=Var(1)),
                    Var(2),
                )
            )
        )
    )

    assertions = Asserted_Model_Properties()
    simplified_formula = simplify_formula_using_model_properties(formula, assertions)

    expected_result = AST_Connective(
        referenced_vars=(),
        type=Connective_Type.AND,
        children=(Var(1), Var(2))
    )

    assert simplified_formula == expected_result

