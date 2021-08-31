from ast_relations import extract_relation
from presburger_algorithms import build_nfa_from_linear_equality
from automatons import LSBF_Alphabet, NFA
from parse import (
    build_syntax_tree,
    lex,
)


formula = '(= x 0)'
tokens = lex(formula)
ast = build_syntax_tree(tokens)

print(ast)

relation = extract_relation(ast[0])
relation_variables = [('x', 1)]
alphabet = LSBF_Alphabet.from_variable_names(['x'])
nfa = build_nfa_from_linear_equality(relation, relation_variables, alphabet, NFA)

print(len(nfa.states))

# nfa = build_nfa_from_inequality(_ineq, [('y', 1)], alphabet, NFA, embed_metadata=True)
