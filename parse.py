from typing import List, Any

source_text = '''
(set-info :category "industrial")
(set-info :status unsat)
(assert (not (exists ((?X Int)) (<= 2 ?X))))
(check-sat)
(exit)
'''

formulas = []


def lex(source: str) -> List[str]:
    # Prepare source
    source = source.replace('(', '( ').replace(')', ' )')
    tokens = source.split()
    return tokens


def build_syntax_tree(tokens: List[str]):
    stack: List[Any] = []
    depth = -1
    for token in tokens:
        if token == '(':
            depth += 1
            stack.append([])
        elif token == ')':
            depth -= 1
            if depth >= 0:
                list_finished = stack.pop()
                stack[-1].append(list_finished)
        else:
            stack[-1].append(token)
    return stack


def filter_asserts(ast):
    # TODO: Remove this
    _asserts = []
    for top_level_expr in ast:
        if top_level_expr[0] == 'assert':
            _asserts.append(top_level_expr)
    return _asserts


def get_formula(_assert):
    return _assert[1]


tokens = lex(source_text)
asserts = filter_asserts(build_syntax_tree(tokens))
formulas = list(map(get_formula, asserts))

# nfa = NFA(
#     initial_state=0,
#     final_states=set((3,)),
#     states=set((0, 1, 2, 3)),
#     transitions={
#         0: {'A': set((1,))},
#         1: {
#             'A': set((3, 2)),
#             'B': set((0, 1))
#         },
#         2: {'A': set((3,))},
#         3: {'A': set((3,))}
#     },
#     alphabet=('A', 'B')
# )
#
# print(nfa)
# print(NFAtoDFA(nfa))
