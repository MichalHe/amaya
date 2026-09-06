from dataclasses import dataclass, field
import functools
import operator
from typing import Hashable

from amaya.solver_core import EvaluationContext
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Node,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
)

import pysat.formula
import dd.autoref
from dd.autoref import BDD


def make_atom_name_for_bool_var(var: Var) -> str:
    """
    Name of the `pysat` atom standing for a free Bool variable.

    Bool vars and abstracted theory atoms are numbered independently (both start at small integers),
    so their names *must* live in disjoint namespaces - otherwise `Var(3)` and the fourth abstracted
    relation would silently become one and the same `pysat.formula.Atom`, since atoms are interned by
    name. Note that `Atom` takes a *single* object as its name (a tuple would be unpacked into
    several constructor arguments and rejected), hence the string encoding.
    """
    return f'var:{var.id}'


def make_atom_name_for_theory_atom(atom_id: int) -> str:
    """ Name of the `pysat` atom standing for an abstracted theory atom. See `make_atom_name_for_bool_var`. """
    return f'atom:{atom_id}'


def compute_atom_abstraction_key(node: ASTp_Node) -> Hashable:
    """
    A hashable stand-in for `node`, used to recognize a theory atom the abstraction has already seen.

    `Relation`/`Congruence` are plain (mutable) dataclasses that are unhashable - `Relation` defines
    `__eq__` by hand, which sets `__hash__` to None - so they cannot be dict keys directly, and giving
    them a structural `__hash__` would be a trap, since preprocessing rewrites them in place. Hence a
    tuple built out of their fields here.

    Structural keys are used only for atoms whose meaning is fully determined by their own fields. For
    `Relation`/`Congruence` that holds because preprocessing disambiguates variables, so two atoms with
    equal `Var` ids really are the same atom no matter where they sit in the tree.
    Quantified subformulae are keyed on object identity instead: two structurally identical quantifiers
    may bind different variables in different scopes, and merging atoms that do *not* denote the same
    thing over-constrains the abstraction, which can turn a satisfiable formula into a spurious UNSAT.
    Keying them apart can only weaken the abstraction (more freedom, more theory calls), never break it.
    For the same reason, never key an atom on a De Bruijn encoding, under which `exists x. x > 0` and an
    unrelated `exists y. y > 0` in a different scope look identical.
    """
    match node:
        case Relation():
            return ('rel', node.predicate_symbol, tuple(node.vars), tuple(node.coefs), node.rhs)
        case Congruence():
            return ('congruence', tuple(node.vars), tuple(node.coefs), node.rhs, node.modulus)
        case _:
            return ('subformula', id(node))


@dataclass
class Theory_Abstraction_Manager:
    abstrations: dict[Hashable, int] = field(default_factory=dict)

    def get_id_for_atom(self, atom: ASTp_Node) -> int:
        abstraction_key = compute_atom_abstraction_key(atom)

        atom_id = self.abstrations.get(abstraction_key)
        if atom_id is not None:
            return atom_id

        atom_id = len(self.abstrations)
        self.abstrations[abstraction_key] = atom_id

        return atom_id


def convert_to_sat_formula(root_node: ASTp_Node,
                           ctx: EvaluationContext,
                           abstraction_manager: Theory_Abstraction_Manager) -> pysat.formula.Formula:
   
    match root_node:
        case Var():
            return pysat.formula.Atom(make_atom_name_for_bool_var(root_node))
        case Relation():
            atom_id = abstraction_manager.get_id_for_atom(root_node)
            return pysat.formula.Atom(make_atom_name_for_theory_atom(atom_id))
        case AST_Connective():
            subformulae = (
                convert_to_sat_formula(child, ctx, abstraction_manager)
                for child in root_node.children
            )
            match root_node.type:
                case Connective_Type.AND:
                    return pysat.formula.And(*subformulae)
                case Connective_Type.OR:
                    return pysat.formula.Or(*subformulae)
                case Connective_Type.EQUIV:
                    return pysat.formula.Equals(*subformulae)
        case AST_Negation():
            subformula = convert_to_sat_formula(root_node.child, ctx, abstraction_manager)
            return pysat.formula.Neg(subformula)

    raise ValueError(f'Unhandled formula type when converting to SAT: {type(root_node)}')


def construct_bdd_with_models_of_bool_formula(
    root_node: ASTp_Node,
    ctx: EvaluationContext,
    bdd_manager: BDD
) -> dd.autoref.Function:

    match root_node:
        case Var():
            assert ctx.var_table[root_node].type == VariableType.BOOL
            fn = bdd_manager.var(str(root_node.id))
            return fn
        case AST_Connective():
            subformulae = (
                construct_bdd_with_models_of_bool_formula(child, ctx, bdd_manager)
                for child in root_node.children
            )
            match root_node.type:
                case Connective_Type.AND:
                    return functools.reduce(operator.and_, subformulae)
                case Connective_Type.OR:
                    return functools.reduce(operator.or_, subformulae)
                case Connective_Type.EQUIV:
                    return functools.reduce(dd.autoref.Function.equiv, subformulae)
        case AST_Negation():
            subformula = construct_bdd_with_models_of_bool_formula(root_node.child, ctx, bdd_manager)
            return ~ subformula

    raise ValueError(f'Unhandled formula type when constructing a BDD representing all solutions of a formula: {type(root_node)}')
