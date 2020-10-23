from typing import (
    Set,
    Dict,
    Tuple,
    Union,
    Mapping,
    Optional,
    List,
    Iterable,
    Generator,

    TypeVar
)

import functools

Symbol = Tuple[Union[str, int], ...]
# State = Union[str, int]
State = TypeVar('State')
T = TypeVar('T')
Transitions = Dict[State, Dict[State, Set[Symbol]]]


def symbols_intersect(symbol_a: Symbol, symbol_b: Symbol) -> bool:
    for bit_a, bit_b in zip(symbol_a, symbol_b):
        if not bit_a == bit_b:
            if bit_a == '*' or bit_b == '*':
                continue
            else:
                return False
    return True


def get_transition_target(t: Transitions, origin: State, via: Symbol) -> Tuple[State, ...]:
    dest: List[State] = []
    if origin not in t:
        return tuple()

    s = t[origin]
    for d in s:
        for sym in s[d]:
            if symbols_intersect(sym, via):
                dest.append(d)
    return tuple(dest)


def make_transitions_copy(t: Transitions) -> Transitions:
    t_copy: Transitions = {}
    for s in t:
        t_copy[s] = {}
        for d in t[s]:
            t_copy[s][d] = set(t[s][d])
    return t_copy


def update_transition_fn_with(t_dst: Transitions, t_src: Transitions) -> None:
    for s in t_src:
        if s not in t_dst:
            t_dst[s] = {}

        for d in t_src[s]:
            if d not in t_dst[s]:
                t_dst[s][d] = set(t_src[s][d])
            else:
                t_dst[s][d] = t_dst[s][d].union(t_src[s][d])


def insert_into_transition_fn(t: Transitions, origin: State, via: Symbol, dest: State) -> None:
    if origin not in t:
        t[origin] = {}

    if dest not in t[origin]:
        t[origin][dest] = set()

    t[origin][dest].add(via)


def unite_transitions(t1: Transitions, t2: Transitions):
    unified_t: Transitions = make_transitions_copy(t1)
    update_transition_fn_with(unified_t, t2)
    return unified_t


def do_projection_on_symbol(pos: int, symbol: Symbol) -> Symbol:
    return symbol[:pos] + ('*', ) + symbol[pos + 1:]


def do_projection(t1: Transitions, pos: int) -> Transitions:
    resulting_transitions: Transitions = {}
    symbol_projection_func = functools.partial(do_projection_on_symbol, pos)
    for origin in t1:
        resulting_transitions[origin] = {}
        for dest in t1[origin]:
            resulting_transitions[origin][dest] = set(map(symbol_projection_func, t1[origin][dest]))
    return resulting_transitions


def translate_transition_fn_states(t: Transitions[State], translation: Mapping[State, T]) -> Transitions[T]:
    translated_transitions: Transitions = {}
    for origin in t:
        translated_origin = translation[origin]
        translated_transitions[translated_origin] = {}
        for dest in t[origin]:
            translated_dest = translation[dest]
            translated_transitions[translated_origin][translated_dest] = set(t[origin][dest])

    return translated_transitions


def calculate_variable_bit_position(variable_names: Iterable[str], var: str) -> Optional[int]:
    for pos, alphabet_var_name in enumerate(variable_names):
        if alphabet_var_name == var:
            return pos
    return None


def iter_transition_fn(t: Transitions[State]) -> Generator[Tuple[State, Symbol, State], None, None]:
    for origin in t:
        for dest in t[origin]:
            for sym in t[origin][dest]:
                yield (origin, sym, dest)
