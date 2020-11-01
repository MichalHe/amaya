from typing import List, Any


def lex(source: str) -> List[str]:
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

# ["assert" ["not" ["exists" [BINDERS] TERM]]


def expand_multivariable_bindings(assertion_tree):
    if assertion_tree[0] in ['exists', 'forall']:
        binding_type, bindings, term = assertion_tree
        assert len(bindings) > 0

        if len(bindings) >= 2:
            # We are dealing with multivariable exits
            # ["exists" [x Type, y Type, ...] TERM]]
            leftmost_binding = bindings[0]
            tail = bindings[1:]

            # Prepare substatement
            substmt = [binding_type, tail, term]

            # Update tree
            assertion_tree[1] = [leftmost_binding]
            assertion_tree[2] = substmt

    if assertion_tree[0] in ['exists', 'not', 'forall', 'assert']:
        expand_multivariable_bindings(assertion_tree[-1])


def replace_forall_with_exists(assertion_tree):
    if assertion_tree[0] == 'forall':
        forall_kw, binders, stmt = assertion_tree

        not_stmt = ['not', stmt]
        exists = ['exists', binders, not_stmt]

        assertion_tree[0] = 'not'
        assertion_tree[1] = exists
        assertion_tree.pop(-1)

    if assertion_tree[0] in ['exists', 'not', 'forall', 'assert']:
        replace_forall_with_exists(assertion_tree[-1])


def remove_multiple_negations(assertion_tree):
    pass


def get_formula(_assert):
    return _assert[1]
