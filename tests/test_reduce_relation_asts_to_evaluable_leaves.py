from amaya.preprocessing import reduce_relation_asts_to_evaluable_leaves
from amaya.relations_structures import (
    Relation,
    ModuloTerm
)


def test_no_modulos():
    ast = ['assert', ['not', ['=', 'x', 10]]]

    resulting_ast = reduce_relation_asts_to_evaluable_leaves(ast, set())

    exp_relation = Relation.new_lin_relation(variable_names=['x'], variable_coeficients=[1],
                                             absolute_part=10, operation='=')

    assert ['assert', ['not', exp_relation]] == resulting_ast


def test_with_modulo_special():
    ast = ['assert', ['not', ['=', ['mod', 'x', 10], 0]]]

    resulting_ast = reduce_relation_asts_to_evaluable_leaves(ast, set())

    modulo_term = ModuloTerm(variables=('x',), variable_coeficients=(1,), modulo=10, constant=0)

    exp_relation = Relation.new_congruence_relation(modulo_terms=[modulo_term], modulo_term_coeficients=[1],
                                                    absolute_part=0)

    assert ['assert', ['not', exp_relation]] == resulting_ast


def test_with_modulo_replacement():
    ast = ['assert', ['not', ['=', ['+', ['mod', 'y', 10], 'x'], 0]]]

    resulting_ast = reduce_relation_asts_to_evaluable_leaves(ast, set())

    orig_relation = Relation.new_lin_relation(variable_names=['ModVar0', 'x'], variable_coeficients=[1, 1],
                                              absolute_part=0,  operation='=')
    
    congruence_modulo = ModuloTerm(variables=('ModVar0', 'y'), variable_coeficients=(-1, 1), constant=0, modulo=10)
    congruence = Relation.new_congruence_relation(modulo_terms=[congruence_modulo], modulo_term_coeficients=[1],
                                                  absolute_part=0)

    reminder_lower_bound = Relation.new_lin_relation(variable_names=['ModVar0'], variable_coeficients=[-1],
                                                     absolute_part=0, operation='<=')

    reminder_upper_bound = Relation.new_lin_relation(variable_names=['ModVar0'], variable_coeficients=[1],
                                                     absolute_part=9, operation='<=')

    expected_ast = [
            'assert', 
            ['not', 
                ['exists', 
                    [['ModVar0', 'Int']], 
                    ['and', orig_relation, congruence, reminder_lower_bound, reminder_upper_bound]]]]
    
    relations = resulting_ast[1][1][2][1:]
    expected_relations = expected_ast[1][1][2][1:]

    assert relations[0] == expected_relations[0]
