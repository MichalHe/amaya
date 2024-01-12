from collections.abc import Iterable
from typing import List, Tuple
from amaya.preprocessing.eval import VarInfo
from amaya.relations_structures import(
    AST_Connective,
    AST_NaryNode,
    AST_Negation,
    AST_Node,
    AST_Quantifier,
    ASTp_Node,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    ast_get_binding_list
)


def var_into_var_name(var: Var) -> str:
    return f'X{var.id}'


def _write_ast_in_lash(root: ASTp_Node, params: Iterable[Tuple[Var, VarInfo]]) -> str:
    def fmt_term(term: Tuple[int, Var], include_sign:bool = False):
        coef, var = term
        if include_sign:
            return f'{coef}*{var_into_var_name(var)}'
        return f'{abs(coef)}*x{var_into_var_name(var)}'

    match root:
        case str():
            return root
        case Relation(): # Convert into: C1*X1 + C2*X2 ... <= RHS
            lin_terms = list(root.linear_terms())
            if not lin_terms:
                return f'0 {root.predicate_symbol} {root.rhs}'

            first_term = lin_terms[0]
            terms = [fmt_term(first_term, include_sign=True)]
            for coef, var in lin_terms[1:]:
                sign = '+' if coef >= 0 else '-'
                terms.append(sign)
                terms.append(fmt_term((coef, var), include_sign=False))
            lhs_str = ' '.join(terms)
            return f'{lhs_str} {root.predicate_symbol} {root.rhs}'
        case AST_Connective(): # LASH does not support N-ary ANDs
            connective_type_to_symbol = {
                Connective_Type.AND: 'AND',
                Connective_Type.OR: 'OR'
            }
            connective_symbol = connective_type_to_symbol[root.type]
            subformulae = ['(' + _write_ast_in_lash(subformula, params) + ')' for subformula in root.children[1:]]
            formula = subformulae[0]
            for subformula in subformulae[1:]:
                formula = f'({formula} {connective_symbol} {subformula})'
            return formula
        case AST_Quantifier():
            bound_vars = [var_into_var_name(var) for var in root.bound_vars]
            exists_chain_head = ''.join([f'EXISTS ({var}: ' for var in bound_vars])
            exists_chain_tail = ''.join([')'] * len(bound_vars))

            subformula = _write_ast_in_lash(root.child, params)
            return f'{exists_chain_head} ({subformula}) {exists_chain_tail}'
        case AST_Negation():
            subformula = _write_ast_in_lash(root.child, params)
            return f'NOT ({subformula})'
        case _:
            raise ValueError(f'Unhandled node type when converting ASTp into LASH: {type(root)}')


def write_ast_in_lash(ast: ASTp_Node, params: Iterable[Tuple[Var, VarInfo]]) -> str:
    return _write_ast_in_lash(ast, params)


def _write_ast_in_smt2(root: ASTp_Node, depth: int) -> str:
    def generate_str_for_terms(atom: Relation | Congruence):
        terms = []
        for coef, var in atom.linear_terms():
            coef_str = str(coef) if coef >= 0 else f'(- {abs(coef)})'
            terms.append(f'(* {coef_str} x{var.id})')
        terms_str = ' '.join(terms)
        return f'(+ {terms_str})'

    def prefix_with_depth(what: str) -> str:
        return '  '*depth + what

    match root:
        case Relation():
            term_str = generate_str_for_terms(root)
            return prefix_with_depth(f'({root.predicate_symbol} {term_str} {root.rhs})')
        case Congruence():
            term_str = generate_str_for_terms(root)
            return prefix_with_depth(f'(= (mod {term_str} {root.modulus}) {root.rhs})')
        case AST_Connective():
            connective_type_to_symbol = {
                Connective_Type.AND: 'and',
                Connective_Type.OR: 'or',
                Connective_Type.EQUIV: '=',
            }
            connective_symbol = connective_type_to_symbol[root.type]
            serialized_children = []
            for child in root.children:
                serialized_children.append(_write_ast_in_smt2(child, depth+1) + '\n')
            head = prefix_with_depth(f'({connective_symbol}\n')
            tail = prefix_with_depth(f')')
            return ''.join([head] + serialized_children + [tail])
        case AST_Negation():
            serialized_child = _write_ast_in_smt2(root.child, depth+1) + '\n'
            head = prefix_with_depth('(not\n')
            tail = prefix_with_depth(f')')
            return ''.join([head, serialized_child, tail])
        case AST_Quantifier():
            binding_list = ' '.join(f'(x{var.id} Int)' for var in root.bound_vars)
            binding_str = f'({binding_list})'
            serialized_child = _write_ast_in_smt2(root.child, depth+1) + '\n'
            head = prefix_with_depth(f'(exists {binding_str}\n')
            tail = prefix_with_depth(f')')
            return ''.join([head, serialized_child, tail])
        case _:
            raise ValueError(f'Unhandled node while converting ASTp into SMT2: {type(root)}')


def write_ast_in_smt2(ast: ASTp_Node, global_variables: Iterable[Tuple[Var, VarInfo]]) -> str:
    preamble = (
        '(set-logic LIA)\n'
    )

    formula_params = ''.join(f'(declare-fun x{param.id} () {param_info.type.into_smt2_sort()})\n' for param, param_info in global_variables)

    head = '(assert\n'
    serialized_tree =  _write_ast_in_smt2(ast, 1) + '\n'
    tail = ')\n'
    check_sat = '(check-sat)\n'
    return ''.join((preamble, formula_params, head, serialized_tree, tail, check_sat))
