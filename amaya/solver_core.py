from __future__ import annotations
from dataclasses import dataclass
import time
from typing import (
    List,
    Dict,
    Callable,
    Optional,
)
import sys

from amaya.automatons import (
    LSBF_Alphabet,
    NFA,
)
from amaya import logger
from amaya.config import (
    BackendType,
    solver_config,
)
from amaya.preprocessing.eval import VarInfo
from amaya.relations_structures import (
    Var,
)
from amaya.stats import (
    ParsingOperation,
    AutomatonInfo,
    OperationStartEntry,
    StatPoint,
    RunStats
)


@dataclass
class IntrospectionData:
    automaton: NFA
    operation_id: int
    operation: ParsingOperation


IntrospectHandle = Callable[[IntrospectionData], None]


class EvaluationContext:
    def __init__(self,
                 emit_introspect: Optional[IntrospectHandle] = None,
                 alphabet: Optional[LSBF_Alphabet] = None,
                 var_table: Dict[Var, VarInfo] = {}):
        if emit_introspect:
            self.introspect_handle = emit_introspect
        else:
            self.introspect_handle = lambda _: None

        # Evaluation stats
        self.collect_stats = True
        self.stats = RunStats()
        self.pending_operations_stack: List[OperationStartEntry] = []
        self.operations_performed: int = 0

        self.var_table = var_table

        # Lazy load MTBDD automata module if needed
        self.automata_cls = NFA
        if solver_config.backend_type == BackendType.MTBDD:
            from amaya.mtbdd_automatons import MTBDD_NFA
            self.automata_cls = MTBDD_NFA

        self.alphabet = alphabet

    def get_alphabet(self) -> LSBF_Alphabet:
        if self.alphabet is None:
            raise ValueError('Requesting the overall alphabet from the evaluation context when None has been set.')
        return self.alphabet

    def stats_operation_starts(self, operation: ParsingOperation, input1: Optional[NFA], input2: Optional[NFA]):
        """Notify the context that an operation has started (statistics tracking)."""
        start = time.time_ns() if solver_config.track_operation_runtime else 0

        operand1_info = AutomatonInfo.from_automaton(input1)
        operand2_info = AutomatonInfo.from_automaton(input2)
        startpoint = OperationStartEntry(op_type=operation, operand1=operand1_info, operand2=operand2_info, start_ns=start)

        self.pending_operations_stack.append(startpoint)

    def stats_operation_ends(self, output: NFA) -> int:
        """
        Notify the context that an operation ended an a automaton has been produced.

        Returns:
            ID of the finished operation.
        """

        self.stats.max_automaton_size = max(self.stats.max_automaton_size, len(output.states))

        op_start = self.pending_operations_stack.pop(-1)  # Operation starting point

        operation_id = self.operations_performed
        output.operation_id = operation_id
        self.operations_performed += 1

        if self.introspect_handle:
            introspect_data = IntrospectionData(automaton=output, operation_id=operation_id, operation=op_start.op_type)
            self.introspect_handle(introspect_data)

        runtime = (time.time_ns() - op_start.start_ns) if solver_config.track_operation_runtime else 0
        output_info = AutomatonInfo.from_automaton(output)
        assert output_info
        stat = StatPoint(operation=op_start.op_type,
                         operand1=op_start.operand1,
                         operand2=op_start.operand2,
                         output=output_info,
                         operation_id=operation_id,
                         runtime_ns=runtime)

        logger.info(f"Operation finished: {stat}")
        self.stats.trace.append(stat)

        if solver_config.max_allowed_states is not None:
            if len(output.states) > solver_config.max_allowed_states:
                info = 'Manipulated automaton is larger then the configured hard limit: %d > %d'
                logger.critical(info, len(output.states), solver_config.max_allowed_states)
                sys.exit(f'Automaton size limit exceeded: {len(output.states)}/{solver_config.max_allowed_states}')

        return operation_id

    def get_automaton_class_for_current_backend(self):
        return self.automata_cls
