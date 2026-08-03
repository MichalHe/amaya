"""
Set of constructors to help constructing formula ASTs
"""

from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Node,
    Connective_Type,
    Relation,
    Var
)


def _and(*children: ASTp_Node, referenced_vars: tuple[Var, ...] = tuple()) -> AST_Connective:
    result = AST_Connective(
        referenced_vars=referenced_vars,
        type=Connective_Type.AND,
        children=children
    )
    return result


def _or(*children: ASTp_Node, referenced_vars: tuple[Var, ...] = tuple()) -> AST_Connective:
    result = AST_Connective(
        referenced_vars=referenced_vars,
        type=Connective_Type.OR,
        children=children
    )
    return result


def _exists(bound_vars: tuple[Var, ...], child: ASTp_Node, referenced_vars: tuple[Var, ...] = ()) -> AST_Quantifier:
    return AST_Quantifier(
        referenced_vars=referenced_vars,
        bound_vars=bound_vars,
        child=child
    )


def _neg(child: ASTp_Node, referenced_vars: tuple[Var, ...] = ()) -> ASTp_Node:
    return AST_Negation(referenced_vars=referenced_vars, child=child)


def _eq(var_coef_pairs: list[tuple[int, Var]], rhs: int) -> Relation:
    var_coef_pairs = sorted(var_coef_pairs, key=lambda var_coef_pair: var_coef_pair[1])
    coefs, vars = zip(*var_coef_pairs)
    
    return Relation(vars=list(vars), coefs=list(coefs), rhs=rhs, predicate_symbol='=')
