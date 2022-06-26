from dataclasses import (
    dataclass,
    field,
)
from enum import IntEnum
from typing import (
    Dict,
    List,
    Tuple,
)

from amaya.ast_definitions import AST_Node, AST_NaryNode
from amaya.relations_structures import Relation

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
class VariableRenamingInfo:
    old_name: str
    new_name: str
    conflicting_quantifiers: Tuple[Quantifier, Quantifier]


@dataclass
class PrenexingContext:
    quantifiers: List[Tuple[Quantifier, Dict[str, VariableRenamingInfo]]] = field(default_factory=list)
    """All encountered quantifiers, including variable renaming info, that will be moved before the matrix in PNF."""
    quantifiers_above: List[Tuple[Quantifier, Dict[str, VariableRenamingInfo]]] = field(default_factory=list)
    """Quantifiers above the current node and including the variable renames introduced with that them."""
    variable_renaming_map: Dict[str, str] = field(default_factory=dict)
    """Maps old variable names to new ones in the current context. Gets updated with every quantifier"""
    variable_renaming_info: Dict[str, int] = field(default_factory=dict)
    """Tracks how many times was a variable renamed in order to generate an unique name."""


def _convert_formula_to_pnf(ast: AST_Node, context: PrenexingContext):
    if isinstance(ast, str):
        # Standalone variable - rename it if quantifier naming conflict detected
        var: str = ast
        return context.variable_renaming_map[var].new_name if var in context.variable_renaming_map else var
    elif isinstance(ast, Relation):
        # Possibly rename variable in atom due to variable name collisions between two quantifiers
        relation: Relation = ast
        relation.rename_variables(context.variable_renaming_map)
        return relation

    node_type = ast[0]

    if node_type == 'not':
        quantifier_count_seen_before = len(context.quantifiers)
        subformula = _convert_formula_to_pnf(ast[1], context)
        # Invert quantifier polarities - only in the subformula
        for quantifier, dummy_renaming_info in context.quantifiers[quantifier_count_seen_before:]:
            quantifier.polarity = 1 - quantifier.polarity
        return ['not', subformula]
    elif node_type in {'exists', 'forall'}:
        node_bound_vars = ast[1]
        newly_bound_vars = tuple((var_name, var_type) for var_name, var_type in node_bound_vars)

        quantifier_polarity = QuantifierPolarity.EXISTS if node_type == 'exists' else QuantifierPolarity.FORALL
        current_quantifier = Quantifier(polarity=quantifier_polarity, bound_variables=newly_bound_vars)

        # Check whether the variable is bound by any quantifier above in the AST, if yes, rename vars
        variable_renaming_map_for_current_quantifier: Dict[str, VariableRenamingInfo] = {}
        newly_bound_var_set = set(var_type_pair[0] for var_type_pair in newly_bound_vars)
        for quantifier_above, renaming_introduced_with_quantifier_above in context.quantifiers:
            bound_var_set = set(var[0] for var in quantifier_above.bound_variables)
            vars_bound_by_both_quantifiers = newly_bound_var_set.intersection(bound_var_set)

            for var in vars_bound_by_both_quantifiers:
                if var in variable_renaming_map_for_current_quantifier:
                    continue  # We don't want to rename the same variable multiple times

                # Rename the variable
                var_renaming_count = context.variable_renaming_info.get(var, 1)
                new_name = f'{var}-{var_renaming_count}'
                variable_renaming_map_for_current_quantifier[var] = VariableRenamingInfo(
                    old_name=var, new_name=new_name, conflicting_quantifiers=(current_quantifier, quantifier_above)
                )

        # Collect quantifiers so they can be placed before the matrix
        context.quantifiers.append((current_quantifier, variable_renaming_map_for_current_quantifier))

        # We have compared the current quantifiers to all above - update the renaming map
        renaming_map_difference = {}
        for var, ranaming_info in variable_renaming_map_for_current_quantifier.items():
            # Use None to mark an entry for removal
            old_value = context.variable_renaming_map[var] if var in context.variable_renaming_map else None
            renaming_map_difference[var] = old_value
        context.variable_renaming_map.update(variable_renaming_map_for_current_quantifier)

        # Push the quantifier with the renaming it introduced
        context.quantifiers_above.append((current_quantifier, variable_renaming_map_for_current_quantifier))

        # Do the nested call
        quantifier_free_subtree = _convert_formula_to_pnf(ast[2], context)

        # Pop the current quantifier - restore the renaming context
        context.quantifiers_above.pop(-1)
        for var, old_value in renaming_map_difference.items():
            if old_value:
                context.variable_renaming_map[var] = old_value
            else:
                del context.variable_renaming_map[var]

        return quantifier_free_subtree
    else:
        formula = [node_type]
        for subformula in ast[1:]:
            formula.append(_convert_formula_to_pnf(subformula, context))
        return formula


def convert_formula_to_pnf(formula: AST_Node):
    ctx = PrenexingContext(quantifiers=[])

    formula_without_quantifiers = _convert_formula_to_pnf(formula, ctx)

    pnf = formula_without_quantifiers
    for quantifier, variable_renaming_info in reversed(ctx.quantifiers):
        qnode_type = 'exists' if quantifier.polarity == QuantifierPolarity.EXISTS else 'forall'
        bound_vars = [
            [variable_renaming_info[var].new_name if var in variable_renaming_info else var,
             type] for var, type in quantifier.bound_variables
        ]
        # assert False, variable_renaming_info
        pnf = [qnode_type, bound_vars, pnf]  # Add a quantifier block
    return pnf
