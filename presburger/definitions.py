from __future__ import annotations
from dataclasses import dataclass
from typing import (
    Callable,
    Optional,
    Tuple,
    Union,
)

from alphabet import LSBF_Alphabet
from automatons import (
    AutomatonType,
    NFA
)
from relations_structures import Relation
from utils import vector_dot


# TODO: Make automata not be generic anymore (hardcode ints)
DFA_AlphabetSymbolType = Tuple[int, ...]
DFA_AutomatonStateType = int

NFA_AlphabetSymbolType = Tuple[int, ...]
NFA_AutomatonStateType = int

AutomatonConstructor = Callable[[LSBF_Alphabet, AutomatonType], NFA]


def can_build_modulo_automaton(relation: Relation) -> Union[bool, str]:
    """
    Asserts that the relation has `(a.x mod C) = K` form, and thus, a modulo automaton can be constructed for it.

    The equality must contain only 1 modulo term and no other freestanding variable terms.

    :param relation: Relation for which a modulo automaton wants to be constructed.
    :returns: True if the relation has correct form, otherwise a string containing information about what is wrong with its structure.
    """
    
    correct_form_conditions_with_reasons = (
        ('The relation contains wrong number of modulo terms', len(relation.modulo_terms) == 1),
        ('The relation contains wrong number of modulo terms', len(relation.modulo_term_coeficients) == 1),
        ('The relation contains other than modulo terms', not relation.variable_names),
        ('The relation contains other than modulo terms', not relation.variable_coeficients),
        ('The relation does not check for equality of reminders', relation.operation == '='),
    )

    for reason, condition in correct_form_conditions_with_reasons:
        if not condition:
            return reason
    return True


@dataclass(frozen=True)
class ModuloTermStateComponent(object):
    value: int
    modulo: int
    variable_coeficients: Tuple[int, ...]

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[ModuloTermStateComponent]:
        dot = vector_dot(self.variable_coeficients, alphabet_symbol)

        if self.modulo % 2 == 0:
            if dot % 2 == 0:
                return ModuloTermStateComponent(
                    value=dot//2,
                    modulo=self.modulo//2,
                    variable_coeficients=self.variable_coeficients
                )
            else:
                return None

        difference = self.value - dot
        next_value = difference // 2 if difference % 2 == 0 else (difference + self.modulo) // 2
        next_value = next_value % self.modulo
        return ModuloTermStateComponent(
            value=next_value,
            modulo=self.modulo,
            variable_coeficients=self.variable_coeficients
        )

    def __str__(self) -> str:
        return f'{self.value} (mod {self.modulo})'


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
