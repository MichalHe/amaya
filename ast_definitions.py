from dataclasses import dataclass
from typing import Union, List, Callable, Dict

from ast_relations import Relation


AST_Leaf = Union[str, Relation]
AST_NaryNode = List[Union[AST_Leaf, 'AST_NaryNode']]
AST_Node = Union[AST_Leaf, AST_NaryNode]


@dataclass
class NodeEncounteredHandlerStatus:
    should_reevaluate_result: bool
    is_result_atomic: bool
    do_not_descend_further: bool = False


NodeEncounteredHandler = Callable[[AST_NaryNode, bool, Dict], NodeEncounteredHandlerStatus]
