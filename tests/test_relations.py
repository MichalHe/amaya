from amaya.relations_structures import (
    DivTerm,
    ModuloTerm,
    Relation,
)

from amaya.preprocessing.prenexing import (
    BoundVar,
    Quantifier,
    QuantifierPolarity,
    VariableRenamingInfo,
)


def test_relation_variable_renaming():
    mod_terms = [
        ModuloTerm(variable_coeficients=(1, 2), variables=('x', 'w'), modulo=11, constant=0),
        ModuloTerm(variable_coeficients=(1, 2), variables=('y', 'v'), modulo=12, constant=1)
    ]

    div_terms = [
        DivTerm(variable_coeficients=(1, 2), variables=('x', 'y'), constant=0, divisor=10)
    ]

    relation = Relation(variable_names=['x', 'y', 'z', 'w'],
                        variable_coeficients=[1, 2, 3, 4],
                        modulo_terms=mod_terms,
                        modulo_term_coeficients=[1, 2],
                        div_terms=div_terms,
                        div_term_coeficients=[1],
                        absolute_part=0,
                        operation='<')
    
    quantifier1 = Quantifier(QuantifierPolarity.EXISTS, 
                             (BoundVar(name='x', type='Int'), BoundVar(name='y', type='Int')))
    quantifier2 = Quantifier(QuantifierPolarity.FORALL, 
                             (BoundVar(name='x', type='Int'), BoundVar(name='z', type='Int')))

    renaming = {'x': VariableRenamingInfo(old_name='x', new_name='A',
                                          conflicting_quantifiers=(quantifier1, quantifier2))}
    relation.rename_variables(renaming)

    assert relation.variable_names == ['A', 'w', 'y', 'z']
    assert relation.variable_coeficients == [1, 4, 2, 3]


    expected_mod_terms = [
        ModuloTerm(variable_coeficients=(1, 2), variables=('A', 'w'), modulo=11, constant=0),
        ModuloTerm(variable_coeficients=(1, 2), variables=('y', 'v'), modulo=12, constant=1),
    ]
    assert relation.modulo_terms == expected_mod_terms

    expected_div_terms = [
        DivTerm(variable_coeficients=(1, 2), variables=('A', 'y'), constant=0, divisor=10)
    ]
    assert relation.div_terms == expected_div_terms
