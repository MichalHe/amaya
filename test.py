from ast_relations import extract_relation
from presburger_algorithms import build_nfa_from_inequality
from automatons import LSBF_Alphabet, NFA
from parse import (
    build_syntax_tree,
    lex,
)


expr_ast = ['+',
            'x',
            ['*',
             '10',
             ['mod', 'y', 5]]]
ineq = ['<=',
        ['mod', 'y', 5],
        '0']

formula = '(<= (+ x (* 10 (mod y 5))) 0)'
atomic_formula = '(<= (mod (+ (* 8 x) (* 4 K1) (* 2 K2) K3 (* 8 y) (* 8 z)) 4294967296) 4)'
tokens = lex(formula)
ast = build_syntax_tree(tokens)

print(ast)

relation = extract_relation(ast[0])
relation_variables = [('x', 1), ('y', 2), ('z', 3), ('K1', 4), ('K2', 5), ('K3', 6)]
alphabet = LSBF_Alphabet.from_variable_names(['x', 'y', 'z', 'K1', 'K2', 'K3'])
nfa = build_nfa_from_inequality(relation, relation_variables, alphabet, NFA, embed_metadata=True)

print(len(nfa.states))

# nfa = build_nfa_from_inequality(_ineq, [('y', 1)], alphabet, NFA, embed_metadata=True)
