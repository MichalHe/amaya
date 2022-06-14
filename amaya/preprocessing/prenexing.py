from dataclasses import dataclass
from enum import IntEnum
from typing import (
    List,
    Tuple,
)

from amaya.ast_definitions import AST_Node, AST_NaryNode
from amaya.preprocessing import ast_iter_subtrees

class QuantifierPolarity(IntEnum):
    EXISTS = 0
    FORALL = 1


@dataclass
class BoundVar:
    name: str
    type: str


@dataclass
class Quantifier:
    polarity: QuantifierPolarity
    bound_variables: Tuple[BoundVar]


@dataclass
class PrenexingContext:
    quantifiers: List[Quantifier]


def _convert_formula_to_pnf(ast: AST_Node, context: PrenexingContext):
    if not isinstance(ast, list):
        return ast

    node_type = ast[0]

    if node_type == 'not':
        quantifier_count_seen_before = len(context.quantifiers)
        subformula = _convert_formula_to_pnf(ast[1], context)
        # Invert quantifier polarities - only in the subformula
        for quantifier in context.quantifiers[quantifier_count_seen_before:]:
            quantifier.polarity = 1 - quantifier.polarity
        return ['not', subformula]
    elif node_type == 'exists':
        node_bound_vars = ast[1]
        bound_vars = tuple((var_name, var_type) for var_name, var_type in node_bound_vars)
        context.quantifiers.append(
            Quantifier(polarity=QuantifierPolarity.EXISTS, bound_variables=bound_vars)
        )
        return _convert_formula_to_pnf(ast[2], context)
    elif node_type == 'forall':
        node_bound_vars = ast[1]
        bound_vars = tuple((var_name, var_type) for var_name, var_type in node_bound_vars)
        context.quantifiers.append(
            Quantifier(polarity=QuantifierPolarity.FORALL, bound_variables=bound_vars)
        )
        return _convert_formula_to_pnf(ast[2], context)
    else:
        formula = [node_type]
        for subformula in ast[1:]:
            formula.append(_convert_formula_to_pnf(subformula, context))
        return formula


def convert_formula_to_pnf(formula: AST_Node):
    ctx = PrenexingContext(quantifiers=[])
    
    formula_without_quantifiers = _convert_formula_to_pnf(formula, ctx)
    
    pnf = formula_without_quantifiers
    for quantifier in reversed(ctx.quantifiers):
        qnode_type = 'exists' if quantifier.polarity == QuantifierPolarity.EXISTS else 'forall'
        bound_vars = [[var, type] for var, type in quantifier.bound_variables]
        pnf = [qnode_type, bound_vars, pnf]  # Add a quantifier block
    return pnf
