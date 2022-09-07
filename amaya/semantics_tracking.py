from __future__ import annotations
from dataclasses import dataclass
import enum
from typing import (
    Dict,
    Set,
    Tuple,
    Union,
)

from amaya.relations_structures import Relation


class AH_AtomType(enum.IntEnum):
    PRESBURGER_EQ  = 1
    PRESBURGER_LE  = 2
    PRESBURGER_CONGRUENCE  = 3
    BOOL = 4
    TRIVIAL  = 5
    CUSTOM = 6


@dataclass
class AH_Atom:
    atom_type: AH_AtomType
    atom: Optional[Relation]
    special_state: Optional[int] = None
    """Holds the final state of the atom's NFA when solving over integers as the state does not tie to the original atom."""


@dataclass
class AH_Negation:
    child: AH_Node


@dataclass
class AH_Projection:
    child: AH_Node
    states_added_in_pad_closure: Set[int]


@dataclass
class AH_Determinization:
    child: AH_Node
    state_labels: Optional[Dict[int, Set[int]]] = None


@dataclass
class AH_Minimization:
    child: AH_Node
    state_labels: Optional[Dict[int, Set[int]]] = None


@dataclass
class AH_Intersection:
    children: Tuple[AH_Node, ...]
    state_labels: Optional[Dict[int, Tuple[int]]] = None


@dataclass
class AH_Union:
    children: Tuple[AH_Node, ...]
    state_labels: Optional[Dict[int, Tuple[int, int]]] = None
    """Maps states in the union automaton to the index of child the state originates from and the corresponding state."""


AH_Node = Union[AH_Atom, AH_Union, AH_Intersection, AH_Projection, AH_Negation, AH_Determinization, AH_Minimization]
AH_UnaryNodes = (AH_Projection, AH_Negation, AH_Determinization, AH_Minimization)


def construct_flattened_intersection_semantics(intersection_products: Dict[int, Tuple[int, int]],
                                               left_operand: AH_Node,
                                               right_operand: AH_Node) -> AH_Intersection:

    # Check if at least one of the operands comes from intersection, so we can flatten the labels
    if isinstance(left_operand, AH_Intersection) or isinstance(right_operand, AH_Intersection):
        left_flatten_children = left_operand.children if isinstance(left_operand, AH_Intersection) else (left_operand,)
        right_flatten_children = right_operand.children if isinstance(right_operand, AH_Intersection) else (right_operand,)
        flattened_children = (*left_flatten_children, *right_flatten_children)
        resulting_intersection_semantics = AH_Intersection(children=flattened_children)

        flattened_state_labels = {}
        for intersection_state_id, intersection_product_state in intersection_products.items():
            left_state_id, right_state_id = intersection_product_state

            left_flattened_semantics = left_operand.state_labels[left_state_id] if isinstance(left_operand, AH_Intersection) else (left_state_id,)
            right_flattened_semantics = right_operand.state_labels[right_state_id] if isinstance(right_operand, AH_Intersection) else (right_state_id,)
            flattened_state_tuple = (*left_flattened_semantics, *right_flattened_semantics)

            flattened_state_labels[intersection_state_id] = flattened_state_tuple
        resulting_intersection_semantics.state_labels = flattened_state_labels

        return resulting_intersection_semantics

    return AH_Intersection(children=(left_operand, right_operand), state_labels=intersection_products)
