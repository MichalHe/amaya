from preprocessing import reduce_relation_asts_to_evaluable_leaves
from relations_structures import Relation, ModuloTerm


def test_no_modulos():
    ast = ['assert', ['not', ['=', 'x', 10]]]

    resulting_ast = reduce_relation_asts_to_evaluable_leaves(ast)

    exp_relation = Relation(variable_names=['x'],
                            variable_coeficients=[1],
                            modulo_terms=[],
                            modulo_term_coeficients=[],
                            absolute_part=10,
                            operation='=')

    assert ['assert', ['not', exp_relation]] == resulting_ast


def test_with_modulo_special():
    ast = ['assert', ['not', ['=', ['mod', 'x', 10], 0]]]

    resulting_ast = reduce_relation_asts_to_evaluable_leaves(ast)

    modulo_term = ModuloTerm(variables=('x',), variable_coeficients=(1,), modulo=10, constant=0)

    exp_relation = Relation(variable_names=[],
                            variable_coeficients=[],
                            modulo_terms=[modulo_term],
                            modulo_term_coeficients=[1],
                            absolute_part=0,
                            operation='=')

    assert ['assert', ['not', exp_relation]] == resulting_ast


def test_with_modulo_replacement():
    ast = ['assert', ['not', ['=', ['+', ['mod', 'y', 10], 'x'], 0]]]

    resulting_ast = reduce_relation_asts_to_evaluable_leaves(ast)

    orig_relation = Relation(variable_names=['x', 'Mod_0_Var'],
                             variable_coeficients=[1, 1],
                             modulo_terms=[],
                             modulo_term_coeficients=[],
                             absolute_part=0,
                             operation='=')
    
    congruence_modulo = ModuloTerm(variables=('Mod_0_Var', 'y'), variable_coeficients=(-1, 1), constant=0, modulo=10)
    congruence = Relation(variable_names=[], variable_coeficients=[],
                          modulo_terms=[congruence_modulo], modulo_term_coeficients=[1],
                          absolute_part=0,
                          operation='=')

    reminder_lower_bound = Relation(variable_names=['Mod_0_Var'], variable_coeficients=[-1],
                                    modulo_terms=[], modulo_term_coeficients=[],
                                    absolute_part=0, operation='<=')

    reminder_upper_bound = Relation(variable_names=['Mod_0_Var'], variable_coeficients=[1],
                                    modulo_terms=[], modulo_term_coeficients=[],
                                    absolute_part=9, operation='<=')

    expected_ast = [
            'assert', 
            ['not', 
                ['exists', 
                    [['Mod_0_Var', 'Int']], 
                    ['and', orig_relation, congruence, reminder_lower_bound, reminder_upper_bound]]]]
    
    relations = resulting_ast[1][1][2][1:]
    expected_relations = expected_ast[1][1][2][1:]

    assert relations[0] == expected_relations[0]
