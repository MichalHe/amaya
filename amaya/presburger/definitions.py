from __future__ import annotations
from dataclasses import dataclass
from typing import (
    Callable,
    Optional,
    Tuple,
    Union,
)

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonType,
    NFA
)
from amaya.relations_structures import Relation
from amaya.utils import vector_dot


# TODO: Make automata not be generic anymore (hardcode ints)
DFA_AlphabetSymbolType = Tuple[int, ...]
DFA_AutomatonStateType = int

NFA_AlphabetSymbolType = Tuple[int, ...]
NFA_AutomatonStateType = int

AutomatonConstructor = Callable[[LSBF_Alphabet, AutomatonType], NFA]


@dataclass(frozen=True)
class ModuloTermStateComponent(object):
    value: int
    modulo: int
    variable_coefficients: Tuple[int, ...]

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[ModuloTermStateComponent]:
        dot = vector_dot(self.variable_coefficients, alphabet_symbol)

        if self.modulo % 2 == 0:
            if dot % 2 == 0:
                return ModuloTermStateComponent(
                    value=dot//2,
                    modulo=self.modulo//2,
                    variable_coefficients=self.variable_coefficients
                )
            else:
                return None

        difference = self.value - dot
        next_value = difference // 2 if difference % 2 == 0 else (difference + self.modulo) // 2
        next_value = next_value % self.modulo
        return ModuloTermStateComponent(
            value=next_value,
            modulo=self.modulo,
            variable_coefficients=self.variable_coefficients
        )

    def __str__(self) -> str:
        return f'{self.value} (mod {self.modulo})'

    def __repr__(self) -> str:
        return f'c={self.value}'


class AliasStore(object):
    def __init__(self):
        self.data: Dict[ModuloTermStateComponent, int] = {}
        self.counter = 0

    def get_alias_for_state(self, state: ModuloTermStateComponent):
        if state in self.data:
            return self.data[state]
        else:
            alias = self.counter
            self.data[state] = alias
            self.counter += 1
            return alias
