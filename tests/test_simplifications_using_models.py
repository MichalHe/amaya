from amaya.preprocessing.theory_reasoning import Asserted_Model_Properties, Variable_Use_Info, remove_atoms_satisfied_by_unconstrained_vars, scan_variable_use, simplify_formula_using_model_properties
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    BoolLiteral,
    Congruence,
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


def test_alias_substitution_replaces_equals_by_equals():
    '''
    and                              and
       x - y = 0                        x - y = 0
       2y + x + z = 3      ---->        3x + z = 3     (y is known to equal x, substituted away)
    '''
    x, y, z = Var(1), Var(2), Var(3)

    eq_alias = dsl._eq([(1, x), (-1, y)], 0)                 # x - y = 0  =>  x = y
    atom = dsl._eq([(1, x), (2, y), (1, z)], 3)               # 2y + x + z = 3

    formula = dsl._and(eq_alias, atom)

    assertions = Asserted_Model_Properties()
    result = simplify_formula_using_model_properties(formula, assertions)

    expected_atom = Relation(vars=[x, z], coefs=[3, 1], rhs=3, predicate_symbol='=')
    expected_result = dsl._and(eq_alias, expected_atom)

    assert result == expected_result


def test_alias_substitution_applies_to_inequalities_too():
    '''
    and                              and
       x - y = 0                        x - y = 0
       x + 2y <= 9         ---->        3x <= 9
    '''
    x, y = Var(1), Var(2)

    eq_alias = dsl._eq([(1, x), (-1, y)], 0)
    inequality = Relation(vars=[x, y], coefs=[1, 2], rhs=9, predicate_symbol='<=')

    formula = dsl._and(eq_alias, inequality)

    assertions = Asserted_Model_Properties()
    result = simplify_formula_using_model_properties(formula, assertions)

    expected_inequality = Relation(vars=[x], coefs=[3], rhs=9, predicate_symbol='<=')
    expected_result = dsl._and(eq_alias, expected_inequality)

    assert result == expected_result


def test_alias_substitution_collapses_atom_that_becomes_a_tautology():
    '''
    and                              and
       x - y = 0                        x - y = 0
       2x - 2y = 0         ---->        TRUE           (already implied once y is substituted by x)
    '''
    x, y = Var(1), Var(2)

    eq_alias = dsl._eq([(1, x), (-1, y)], 0)
    redundant_atom = Relation(vars=[x, y], coefs=[2, -2], rhs=0, predicate_symbol='=')

    formula = dsl._and(eq_alias, redundant_atom)

    assertions = Asserted_Model_Properties()
    result = simplify_formula_using_model_properties(formula, assertions)

    # The AND's idempotent-children cleanup drops the resulting TRUE, leaving just the alias equation.
    assert result == eq_alias


def test_alias_substitution_does_not_leak_across_or_branches():
    '''
    or                                or
       and                               and
          x - y = 0                         x - y = 0
          2y + x + z = 3                    3x + z = 3
       2y + x + z = 3      ---->         2y + x + z = 3   (unchanged - the alias from the other branch
                                                             must not leak into this sibling branch)
    '''
    x, y, z = Var(1), Var(2), Var(3)

    eq_alias = dsl._eq([(1, x), (-1, y)], 0)
    atom = dsl._eq([(1, x), (2, y), (1, z)], 3)

    formula = dsl._or(
        dsl._and(eq_alias, atom),
        atom,
    )

    assertions = Asserted_Model_Properties()
    result = simplify_formula_using_model_properties(formula, assertions)

    expected_substituted_atom = Relation(vars=[x, z], coefs=[3, 1], rhs=3, predicate_symbol='=')
    expected_result = dsl._or(
        dsl._and(eq_alias, expected_substituted_atom),
        atom,
    )

    assert result == expected_result


def test_simplification_fragment_with_negated_shared_vars():
    '''
    Fragment reproducing a real formula shape: two equations over disjoint-looking variable pairs
    (Var(23)-Var(47) and Var(24)-Var(48)) both sit negated as siblings of one OR, nested inside
    NOT/AND/OR/exists layers that never establish a "similar equation" match for either of them -
    which is exactly the condition under which _register_unresolved_equation tries to turn a negated
    equation into an alias.

    not
       exists (Var(id=48))
          and
             -1.Var(id=47) +1.Var(id=48) = 0
             exists (Var(id=44))
                and
                   -1.Var(id=43) +1.Var(id=44) = 0
                   exists (Var(id=39))
                      and
                         -1.Var(id=38) +1.Var(id=39) = 0
                         or
                            NOT
                               +1.Var(id=15) -1.Var(id=16) = 0
                            and
                               Var(id=34)
                               or
                                  NOT
                                     +1.Var(id=23) -1.Var(id=47) = 0
                                  NOT
                                     +1.Var(id=24) -1.Var(id=48) = 0
    '''
    eq_47_48 = dsl._eq([(-1, Var(47)), (1, Var(48))], 0)
    eq_43_44 = dsl._eq([(-1, Var(43)), (1, Var(44))], 0)
    eq_38_39 = dsl._eq([(-1, Var(38)), (1, Var(39))], 0)
    eq_15_16 = dsl._eq([(1, Var(15)), (-1, Var(16))], 0)
    eq_23_47 = dsl._eq([(1, Var(23)), (-1, Var(47))], 0)
    eq_24_48 = dsl._eq([(1, Var(24)), (-1, Var(48))], 0)

    formula = dsl._neg(
        dsl._exists(
            (Var(48),),
            dsl._and(
                eq_47_48,
                dsl._exists(
                    (Var(44),),
                    dsl._and(
                        eq_43_44,
                        dsl._exists(
                            (Var(39),),
                            dsl._and(
                                eq_38_39,
                                dsl._or(
                                    dsl._neg(eq_15_16),
                                    dsl._and(
                                        Var(34),
                                        dsl._or(
                                            dsl._neg(eq_23_47),
                                            dsl._neg(eq_24_48),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )

    assertions = Asserted_Model_Properties()
    result = simplify_formula_using_model_properties(formula, assertions)
    pprint_formula(result)

    # V48, V44, V39 are each fully aliased away (V48=V47, V44=V43, V39=V38) and their now-unused
    # binders dropped - the substitution correctly reaches eq_24_48, which turns into an equation
    # over V47 (not V48). None of eq_15_16, eq_23_47 or the substituted eq_24_47 get turned into
    # aliases themselves: each sits under a NOT relative to the AND/OR branch it was found in, so
    # `_register_unresolved_equation` must leave them as plain (negated) relations.
    eq_24_47 = dsl._eq([(1, Var(24)), (-1, Var(47))], 0)
    expected_result = dsl._neg(
        dsl._or(
            dsl._neg(eq_15_16),
            dsl._and(
                Var(34),
                dsl._or(
                    dsl._neg(eq_23_47),
                    dsl._neg(eq_24_47),
                ),
            ),
        ),
    )

    assert result == expected_result


def test_asserted_bool_atom_values_are_read_back_faithfully():
    """
    Regression: `get_asserted_values_for_bool_atom` used to be written as
    `if atom_value := level.get(atom) is not None`, which binds the result of the *comparison* - so
    every recorded atom, including one asserted False, read back as True.
    """
    assertions = Asserted_Model_Properties()
    asserted_true, asserted_false, never_asserted = Var(id=1), Var(id=2), Var(id=3)

    assertions.assert_bool_atom(asserted_true, True)
    assertions.assert_bool_atom(asserted_false, False)

    assert assertions.get_asserted_values_for_bool_atom(asserted_true) is True
    assert assertions.get_asserted_values_for_bool_atom(asserted_false) is False
    assert assertions.get_asserted_values_for_bool_atom(never_asserted) is None


def test_asserted_bool_atom_values_are_scoped_innermost_first():
    assertions = Asserted_Model_Properties()
    atom = Var(id=1)

    assertions.assert_bool_atom(atom, False)
    assertions.insert_stack()
    assertions.assert_bool_atom(atom, True)

    assert assertions.get_asserted_values_for_bool_atom(atom) is True

    assertions.pop_stack()
    assert assertions.get_asserted_values_for_bool_atom(atom) is False


def test_congruence_is_unsat_gcd_check():
    """
    `4194304*x = 1048576 (mod 2**32)` has no solution: every value the left-hand side can take is a
    multiple of gcd(4194304, 2**32) = 4194304, but 1048576 is not - regression for the real
    formula (jain_7_..._i_11.smt2, see PROGRESS.md) where a wide substituted congruence like this
    slipped past preprocessing and blew up automaton construction instead of being recognised as
    unsatisfiable up front.
    """
    unsat_congruence = Congruence(vars=[Var(1)], coefs=[4194304], rhs=1048576, modulus=2**32)
    assert unsat_congruence.is_unsat()

    sat_congruence = Congruence(vars=[Var(1)], coefs=[1], rhs=1048576, modulus=2**32)
    assert not sat_congruence.is_unsat()

    # No variables at all - solvability collapses to a plain rhs % modulus check.
    assert Congruence(vars=[], coefs=[], rhs=1, modulus=4).is_unsat()
    assert not Congruence(vars=[], coefs=[], rhs=4, modulus=4).is_unsat()


def test_simplify_formula_using_model_properties_detects_unsat_congruence_after_substitution():
    """
    Regression for the same case as `test_congruence_is_unsat_gcd_check`, exercised through the
    actual pass: substituting a known alias into a congruence can turn a satisfiable congruence
    into an unsatisfiable one (e.g. `x` aliased to `4194304*y` turns `1*x = 1048576 (mod 2**32)`,
    trivially satisfiable, into the unsatisfiable congruence above) - this must be caught right
    after the substitution, not left for the backend to discover by exhausting memory on an
    automaton for an atom that can never hold.
    """
    x, y = Var(1), Var(2)
    formula = AST_Connective(
        referenced_vars=(x, y),
        type=Connective_Type.AND,
        children=(
            Relation(vars=[x, y], coefs=[1, -4194304], rhs=0, predicate_symbol='='),
            Congruence(vars=[x], coefs=[1], rhs=1048576, modulus=2**32),
        ),
    )

    assertions = Asserted_Model_Properties()
    simplified_formula = simplify_formula_using_model_properties(formula, assertions)

    assert simplified_formula == BoolLiteral(False)
