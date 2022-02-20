from typing import (
    Callable,
    Tuple,
)

from alphabet import LSBF_Alphabet
from automatons import (
    AutomatonType,
    NFA
)

# TODO: Make automata not be generic anymore (hardcode ints)
DFA_AlphabetSymbolType = Tuple[int, ...]
DFA_AutomatonStateType = int

NFA_AlphabetSymbolType = Tuple[int, ...]
NFA_AutomatonStateType = int

AutomatonConstructor = Callable[[LSBF_Alphabet, AutomatonType], NFA]
