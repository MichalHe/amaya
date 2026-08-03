from amaya.preprocessing.theory_reasoning import Asserted_Model_Properties, Variable_Use_Info, remove_atoms_satisfied_by_unconstrained_vars, scan_variable_use, simplify_formula_using_model_properties
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    BoolLiteral,
    Connective_Type,
    Relation,
    Var,
    pprint_formula
)
from amaya import dsl


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
    formula = dsl._and(
        Var(id=1),
        dsl._or(
            dsl._neg( Var(1) ),
            Var(2),
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


def test_real_simplification():
    """
    Fragment to simplify from a real formula 
    """

    '''
    and
       +1.Var(id=1) -1.Var(id=2) = 0                              
       exists (Var(id=3))                                  
            and                                            
               or                                          
                  and                                      
                     Var(id=4)                             
                     NOT                                   
                        -1.Var(id=1) +1.Var(id=2) = 0    
                  -1.Var(id=5) +1.Var(id=6) = 0            
               exists (Var(id=29))                         
                    NOT
                        -1.Var(id=5) +1.Var(id=6) = 0            

                    |
             (theory reasoning)
                    |
                    V
   and
       +1.Var(id=1) -1.Var(id=2) = 0                              
       exists (Var(id=3))                                  
            and                                            
               or                                          
                  and                                      
                     Var(id=4)                             
                     NOT                                   
                        TRUE
                  -1.Var(id=5) +1.Var(id=6) = 0            
               exists (Var(id=29))                         
                    NOT
                        -1.Var(id=5) +1.Var(id=6) = 0            

                    |
             (Bool reasoning)
                    |
                    V

    and
       +1.Var(id=1) -1.Var(id=2) = 0                              
       exists (Var(id=3))                                  
            and                                            
              -1.Var(id=5) +1.Var(id=6) = 0            
               exists (Var(id=29))                         
                    NOT
                        -1.Var(id=5) +1.Var(id=6) = 0          
                    |
             (Repeat the same (T+Bool reasoning))
                    |
                    V

    and
       +1.Var(id=1) -1.Var(id=2) = 0                              
       exists (Var(id=3))                                  
           FALSE


    '''

    eq_1 = dsl._eq([(1, Var(id=1)), (-1, Var(id=2))], 0) 
    eq_2 = dsl._eq([(1, Var(id=5)), (-1, Var(id=6))], 0)

    formula = dsl._and(
        eq_1,
        dsl._exists(
            (Var(id=3), ),
            dsl._and(
                dsl._or(
                    dsl._and(
                        Var(id=4),
                        dsl._neg( eq_1 )
                    ),
                    eq_2
                ),
                dsl._exists(
                    (Var(id=7), ),
                    dsl._neg(eq_2)
                )
            )
        )
    )

    assertions = Asserted_Model_Properties()
    simplified_formula = simplify_formula_using_model_properties(formula, assertions)
    pprint_formula(simplified_formula)
    # TODO: write assertions


def test_simplify_on_asserted_bools():
    '''
    and
        Var(id=22)
        NOT
            Var(id=22)
            |
            |
            V
    FALSE
    '''
    formula = dsl._and(
        Var(id=1),
        dsl._neg(Var(id=1))
    )
    assertions = Asserted_Model_Properties()
    simplified_formula = simplify_formula_using_model_properties(formula, assertions)

    expected_formula = BoolLiteral(False)

    assert simplified_formula == expected_formula


def test_model_assertions_leakage():
    """
    Check whether assertion stacks are inserted correctly. 
    """
    pass  # TODO


def test_simplify_on_unconstrained_vars():
    '''
    exists (Var(id=1))
        and
           -1.Var(id=2) +1.Var(id=1) = 0
          or
             Var(id=3)
             NOT
                -1.Var(id=4) +1.Var(id=2) = 0
             NOT
                Var(id=3)
             -1.Var(id=4) = 0
                      |
                      |
                      V

      or
         Var(id=3)
         NOT
            -1.Var(id=4) +1.Var(id=2) = 0
         NOT
            Var(id=3)
         -1.Var(id=4) = 0
    '''

    formula = dsl._exists(
        ( Var(id=1), ),
        dsl._and(
            dsl._eq([ (-1, Var(2)), (1, Var(1)) ], 1),
            dsl._or(
                Var(3),
                dsl._eq([ (-1, Var(4)), (1, Var(2)) ], 1),
                dsl._neg( Var(3) ),
                dsl._eq([ (-1, Var(4)) ], 0),
            )
        )
    )

    var_use_info = Variable_Use_Info()
    scan_variable_use(formula, var_use_info)

    assert len(var_use_info.relation_uses[Var(1)]) == 1
    assert len(var_use_info.relation_uses[Var(2)]) == 2

    result = remove_atoms_satisfied_by_unconstrained_vars(formula, var_use_info, desired_polarity=True)

    expected_result = dsl._or(
        Var(3),
        dsl._eq([ (-1, Var(4)), (1, Var(2)) ], 1),
        dsl._neg( Var(3) ),
        dsl._eq([ (-1, Var(4)) ], 0),
    )

    pprint_formula(result)

    assert result == expected_result
