from __future__ import annotations
from dataclasses import dataclass
from enum import IntEnum
from typing import (
    Callable,
    Dict,
    List,
    Union,
)

from amaya.ast_relations import Relation


AST_Leaf = Union[str, Relation]
AST_NaryNode = List[Union[AST_Leaf, 'AST_NaryNode']]
AST_Node = Union[AST_Leaf, AST_NaryNode]


@dataclass
class NodeEncounteredHandlerStatus:
    should_reevaluate_result: bool
    is_result_atomic: bool
    do_not_descend_further: bool = False


NodeEncounteredHandler = Callable[[AST_NaryNode, bool, Dict], NodeEncounteredHandlerStatus]

class VariableType(IntEnum):
    INT = 1
    BOOL = 2
    UNSET = 3

    @staticmethod
    def from_smt_type_string(type_str: str) -> VariableType:
        m = {
            'Bool': VariableType.BOOL,
            'Int': VariableType.INT,
        }
        return m[type_str]


@dataclass
class FunctionSymbol:
    name: str
    arity: int
    args: List[Tuple[str, VariableType]]
    return_type: VariableType
