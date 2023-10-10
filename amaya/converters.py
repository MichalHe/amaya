from amaya.relations_structures import AST_NaryNode, AST_Node, Relation, Var, ast_get_binding_list


def var_into_varname(var: Var) -> str:
    return f'x{var.id}'


def _write_ast_in_lash(ast: AST_Node) -> str:
    if isinstance(ast, str):
        return ast

    if isinstance(ast, Relation):
        relation: Relation = ast
        coef_var_pairs = list(zip(relation.coefs, relation.vars))
        tokens = [str(coef_var_pairs[0][0]), '*', var_into_varname(coef_var_pairs[0][1])]
        for coef, var in coef_var_pairs[1:]:
            sign = '+' if coef > 0 else '-'
            tokens.extend((sign, str(coef), '*', var_into_varname(var)))
        tokens.append(relation.predicate_symbol)
        tokens.append(str(relation.rhs))
        return ' '.join(tokens)

    assert isinstance(ast, list), f'Unsupported AST node: {ast}'
    node_type: str = ast[0]  # type: ignore
    if node_type == 'and':
        subformulae = ['(' + _write_ast_in_lash(subformula) + ')' for subformula in ast[1:]]

        formula = subformulae[0]
        for subformula in subformulae[1:]:
            formula = f'({formula} AND {subformula})'

        return formula
    elif node_type == 'or':
        subformulae = ['(' + _write_ast_in_lash(subformula) + ')' for subformula in ast[1:]]
        return ' OR '.join(subformulae)
    elif node_type == 'exists':
        binding_list = ast_get_binding_list(ast)
        var_list = [var_into_varname(var) for var in binding_list]  # type: ignore
        exists_chain_head = ''.join([f'EXISTS ({var}: ' for var in var_list])
        exists_chain_tail = ''.join([')'] * len(var_list))

        subformula = _write_ast_in_lash(ast[2])
        return f'{exists_chain_head} ({subformula}) {exists_chain_tail}'
    elif node_type == 'not':
        subformula = _write_ast_in_lash(ast[1])
        return f'NOT ({subformula})'

    assert False, ast
    return ''

def write_ast_in_lash(ast: AST_Node) -> str:
    return _write_ast_in_lash(ast)
