from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import List, Optional


class ParsingOperation(Enum):
    BUILD_NFA_FROM_INEQ = 'build_nfa_from_ineq'
    BUILD_NFA_FROM_SHARP_INEQ = 'build_nfa_from_sharp_ineq'
    BUILD_NFA_FROM_EQ = 'build_nfa_from_eq'
    BUILD_NFA_FROM_CONGRUENCE = 'build_nfa_from_congruence'
    BUILD_NFA_FROM_RELATION = 'build_nfa_from_relation'  # We don't know the relation type, or we do not care.
    LAZY_CONSTRUCT = 'lazy'
    NFA_UNION = 'union'
    NFA_PROJECTION = 'projection'
    NFA_COMPLEMENT = 'complement'
    NFA_DETERMINIZE = 'determinize'
    NFA_INTERSECT = 'intersection'
    BUILD_DFA_FROM_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_SHARP_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_EQ = 'build_dfa_from_ineq'
    MINIMIZE = 'minimization'


@dataclass
class AutomatonInfo:
    size: int
    automaton_id: int

    @staticmethod
    def from_automaton(automaton: Optional[NFA]) -> Optional[AutomatonInfo]:
        if not automaton:
            return None
        return AutomatonInfo(size=len(automaton.states), automaton_id=automaton.operation_id)


@dataclass
class OperationStartEntry:
    op_type: ParsingOperation
    operand1: Optional[AutomatonInfo]
    operand2: Optional[AutomatonInfo]
    start_ns: int


@dataclass
class StatPoint:
    operation: ParsingOperation
    operand1: Optional[AutomatonInfo]  # build_nfa_from_atom does not have to have inputs
    operand2: Optional[AutomatonInfo]
    output: AutomatonInfo
    operation_id: int
    runtime_ns: int


@dataclass
class RunStats:
    max_automaton_size: int = 0
    trace: List[StatPoint] = field(default_factory=list)
