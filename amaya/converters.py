from collections.abc import Iterable
import functools
from typing import Callable, Dict, List, Tuple
import sys

from amaya.preprocessing.eval import VarInfo
from amaya.relations_structures import(
    AST_Connective,
    AST_NaryNode,
    AST_Negation,
    AST_Node,
    AST_Quantifier,
    ASTp_Node,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
    ast_get_binding_list
)


def var_into_var_name(var: Var) -> str:
    return f'X{var.id}'


def _write_ast_in_lash(root: ASTp_Node, params: Iterable[Tuple[Var, VarInfo]]) -> str:
    def fmt_term(term: Tuple[int, Var], include_sign:bool = False):
        coef, var = term
        if include_sign:
            return f'{coef}*{var_into_var_name(var)}'
        return f'{abs(coef)}*{var_into_var_name(var)}'

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
            if root.type == Connective_Type.EQUIV:
                assert len(root.children) == 2
                left_child = '(' + _write_ast_in_lash(root.children[0], params) + ')'
                right_child = '(' + _write_ast_in_lash(root.children[1], params) + ')'
                return f'({left_child} AND {right_child}) OR ((NOT {left_child}) AND (NOT {right_child}))'

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
        case BoolLiteral():
            if root.value:
                return 'X = X'
            else:
                return 'NOT (X = X)'
        case Var():
            return f'-1*{var_into_var_name(root)} <= 0'  # When the Boolean variable is positive, it is True; when negative; False
        case _:
            raise ValueError(f'Unhandled node type when converting ASTp into LASH: {type(root)}')


def write_ast_in_lash(ast: ASTp_Node, params: Iterable[Tuple[Var, VarInfo]], var_table: Dict[Var, VarInfo]) -> str:
    return _write_ast_in_lash(ast, params)


def _write_ast_in_smt2(root: ASTp_Node,
                       depth: int,
                       var_table: Dict[Var, VarInfo],
                       var_formatter: Callable[[Var, Dict[Var, VarInfo]], str]) -> str:

    _write_subtree = functools.partial(_write_ast_in_smt2, depth=depth+1, var_table=var_table, var_formatter=var_formatter)

    def generate_str_for_terms(atom: Relation | Congruence):
        terms = []
        for coef, var in atom.linear_terms():
            coef_str = str(coef) if coef >= 0 else f'(- {abs(coef)})'
            terms.append(f'(* {coef_str} {var_formatter(var, var_table)})')
        if len(terms) == 1:
            return terms[0]
        terms_str = ' '.join(terms)
        return f'(+ {terms_str})'

    def prefix_with_depth(what: str) -> str:
        return '  '*depth + what

    match root:
        case Relation():
            term_str = generate_str_for_terms(root)
            rhs = f'(- {abs(root.rhs)})' if root.rhs < 0 else f'{root.rhs}'
            return prefix_with_depth(f'({root.predicate_symbol} {term_str} {rhs})')
        case Congruence():
            term_str = generate_str_for_terms(root)
            rhs = f'(- {abs(root.rhs)})' if root.rhs < 0 else f'{root.rhs}'
            return prefix_with_depth(f'(= (mod {term_str} {root.modulus}) {rhs})')
        case AST_Connective():
            connective_type_to_symbol = {
                Connective_Type.AND: 'and',
                Connective_Type.OR: 'or',
                Connective_Type.EQUIV: '=',
            }
            connective_symbol = connective_type_to_symbol[root.type]
            serialized_children = []
            for child in root.children:
                serialized_children.append(_write_subtree(child) + '\n')
            head = prefix_with_depth(f'({connective_symbol}\n')
            tail = prefix_with_depth(f')')
            return ''.join([head] + serialized_children + [tail])
        case AST_Negation():
            serialized_child = _write_subtree(root.child) + '\n'
            head = prefix_with_depth('(not\n')
            tail = prefix_with_depth(f')')
            return ''.join([head, serialized_child, tail])
        case AST_Quantifier():
            def make_smt2_sort(var: Var) -> str:
                var_type_to_sort_map = {
                    VariableType.INT: 'Int',
                    VariableType.BOOL: 'Bool'
                }
                return var_type_to_sort_map[var_table[var].type]

            binding_list = ' '.join(f'({var_formatter(var, var_table)} {make_smt2_sort(var)})' for var in root.bound_vars)
            binding_str = f'({binding_list})'
            serialized_child = _write_subtree(root.child) + '\n'
            head = prefix_with_depth(f'(exists {binding_str}\n')
            tail = prefix_with_depth(f')')
            return ''.join([head, serialized_child, tail])
        case Var():
            return prefix_with_depth(var_formatter(root, var_table))
        case BoolLiteral():
            smt_text = 'true' if root.value else 'false'
            return prefix_with_depth(smt_text)
        case _:
            raise ValueError(f'Unhandled node while converting ASTp into SMT2: {type(root)}')


def write_ast_in_smt2(ast: ASTp_Node,
                      global_variables: Iterable[Tuple[Var, VarInfo]],
                      var_table: Dict[Var, VarInfo]) -> str:
    preamble = (
        '(set-logic LIA)\n'
    )

    def var_formatter(var: Var, var_table: Dict[Var, VarInfo]):
        return var_table[var].name

    formula_params = ''.join(f'(declare-fun {var_formatter(param, var_table)} () {param_info.type.into_smt2_sort()})\n' for param, param_info in global_variables)

    head = '(assert\n'
    serialized_tree = _write_ast_in_smt2(ast, 1, var_table, var_formatter=var_formatter) + '\n'
    tail = ')\n'
    check_sat = '(check-sat)\n'
    return ''.join((preamble, formula_params, head, serialized_tree, tail, check_sat))


def _rename_vars(root: ASTp_Node, substitution: Dict[Var, Var]) -> ASTp_Node:
    match root:
        case Relation():
            vars = [substitution.get(var, var) for var in root.vars]
            return Relation(vars=vars, coefs=root.coefs, rhs=root.rhs, predicate_symbol=root.predicate_symbol)
        case Congruence():
            vars = [substitution.get(var, var) for var in root.vars]
            return Congruence(vars=vars, coefs=root.coefs, rhs=root.rhs, modulus=root.modulus)
        case Var():
            return substitution.get(root, root)
        case AST_Connective():
            substituted_children = (_rename_vars(child, substitution) for child in root.children)
            return root.replace_children(tuple(substituted_children))
        case AST_Quantifier():
            substituted_child = _rename_vars(root.child, substitution)
            return AST_Quantifier(referenced_vars=root.referenced_vars, bound_vars=root.bound_vars, child=substituted_child)
        case AST_Negation():
            substituted_child = _rename_vars(root.child, substitution)
            return AST_Negation(referenced_vars=root.referenced_vars, child=substituted_child)
        case _:
            raise ValueError('Unhandled AST node while performing variable substitution.')


def generate_optimization_problem(input_formula: ASTp_Node, var_table: Dict[Var, VarInfo], params: List[Var]) -> ASTp_Node:
    """
    Given a formula PHI(x, y, ...) return its optimization variant requiring the model values to be largest among models.

    The optimization variant (result) has the following form:
        PHI(x, y, ...) AND (FORALL (x', y', ...) (=> PHI(x', y', ...) (<= (x', y', ...) (x, y, ...) )))
    """
    if not params:
        # There is nothing to optimize if the formula has no free variables
        return input_formula

    var_count = len(var_table)
    comment = f'Primed version of {0} to represent values of other models in optimization problem.'
    substitution: Dict[Var, Var] = {}
    for param_idx, param in enumerate(params):
        param_idx += 1  # Make sure that we are not overriding variables when param_idx=0
        param_info = var_table[param]
        assert param_info.type == VariableType.INT, 'Conversion into an optimization problem supported only for formulae with purely integer parameters.'
        primed_param = Var(id=var_count+param_idx)
        var_table[primed_param] = VarInfo(name=f'{param_info.name}_primed', type=param_info.type, comment=comment.format(param_info.name))
        substitution[param] = primed_param

    if isinstance(input_formula, (AST_Quantifier, AST_Connective, AST_Negation)):
        referenced_vars = input_formula.referenced_vars
    elif isinstance(input_formula, (Congruence, Relation)):
        referenced_vars = tuple(input_formula.vars)
    else:
        referenced_vars = tuple()

    primed_referenced_vars = tuple(substitution.get(var, var) for var in referenced_vars)
    input_property_for_primed_params = _rename_vars(input_formula, substitution)
    negated_input_property = AST_Negation(referenced_vars=primed_referenced_vars, child=input_property_for_primed_params)

    primed_params_smaller_atoms: List[Relation] = []
    for param, primed_param in substitution.items():
        atom = Relation(vars=[param, primed_param], coefs=[-1, 1], rhs=0, predicate_symbol='<=')
        primed_params_smaller_atoms.append(atom)

    all_primed_params_smaller = AST_Connective(referenced_vars=tuple(substitution.keys()) + tuple(substitution.values()),
                                               type=Connective_Type.AND,
                                               children=tuple(primed_params_smaller_atoms))

    rewritten_implication = AST_Connective(referenced_vars=tuple(), type=Connective_Type.OR, children=(negated_input_property, all_primed_params_smaller))

    # Rewrite the universal quantifier as NOT(EXISTS(NOT PHI))
    negated_implication = AST_Negation(referenced_vars=tuple(), child=rewritten_implication)
    existential_quantifier = AST_Quantifier(referenced_vars=referenced_vars,
                                            bound_vars=tuple(substitution.values()),
                                            child=negated_implication)
    optimality_constraint = AST_Negation(referenced_vars=tuple(), child=existential_quantifier)

    return AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND, children=(input_formula, optimality_constraint))
