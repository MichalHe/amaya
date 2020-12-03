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
import utils

Symbol = Tuple[Union[str, int], ...]
# State = Union[str, int]
State = TypeVar('State')
T = TypeVar('T')
Transitions = Dict[State, Dict[State, Set[Symbol]]]
VariableNames = List[str]


# Create united alphabet
# Function for extending to new alphabet
# already implemented unite_transitions


def unite_alphabets(alphabet1: VariableNames, alphabet2: VariableNames) -> VariableNames:
    return list(sorted(set(alphabet1 + alphabet2)))


def get_indices_of_missing_variables(variables: VariableNames, variables_subset: VariableNames) -> List[int]:
    missing_variables_indices: List[int] = []

    if not len(variables_subset):
        return [i for i in range(len(variables))]

    has_more_new_variables = False
    last_examined_new_variable: int = None

    vi = 0  # Variables index
    for i, var in enumerate(variables):
        if not var == variables_subset[vi]:
            missing_variables_indices.append(i)
        else:
            vi += 1

        if vi == len(variables_subset):
            has_more_new_variables = True
            last_examined_new_variable = i
            break

    if has_more_new_variables:
        for i in range(last_examined_new_variable + 1, len(variables)):
            missing_variables_indices.append(i)

    return missing_variables_indices


def extend_symbol_on_index(symbol: Tuple[int, ...], missing_index: int) -> Tuple[int]:
    if missing_index >= len(symbol):
        return symbol + ('*', )
    elif missing_index == 0:
        return ('*', ) + symbol
    else:
        return symbol[:missing_index] + ('*', ) + symbol[missing_index:]


def extend_symbol_with_missing_indices(symbol: Tuple[int, ...], missing_indices: List[int]):
    patched_symbol = symbol
    for missing_index in missing_indices:
        patched_symbol = extend_symbol_on_index(patched_symbol, missing_index)
    return patched_symbol


def extend_transitions_to_new_alphabet_symbols(old_variables: VariableNames, new_variables: VariableNames, t: Transitions) -> Transitions:
    missing_indices = get_indices_of_missing_variables(old_variables, new_variables)
    extended_transitions = make_transitions_copy(t)

    for origin in t:
        for dest in t[origin]:
            extended_transitions[origin][dest] = set(map(lambda old_symbol: extend_symbol_with_missing_indices(old_symbol, missing_indices), t[origin][dest]))

    return extended_transitions


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


def get_word_from_dfs_results(t: Transitions[State],
                              traversal_history: Dict[State, State],
                              last_state: State,
                              initial_states: Set[State]) -> List[Symbol]:

    backtrack_state_path_to_origin = []
    state = last_state

    added_initial_state = False
    while not added_initial_state:
        backtrack_state_path_to_origin.append(state)
        if state in initial_states:
            added_initial_state = True
        else:
            state = traversal_history[state]

    path = list(reversed(backtrack_state_path_to_origin))
    used_word = []

    for i in range(len(path) - 1):
        origin = path[i]
        dest = path[i + 1]
        symbol = tuple(t[origin][dest])[0]
        used_word.append(symbol)

    return used_word


def iterate_over_active_variables(all_variables: Tuple[str], active_variables: Set[str]):
    ordered_active_vars = list(sorted(active_variables))
    missing_variables_indices = get_indices_of_missing_variables(all_variables, ordered_active_vars)

    for symbol_cnt in range(2**len(active_variables)):
        valid_bitsubtuple = utils.number_to_bit_tuple(symbol_cnt, tuple_size=len(active_variables))
        mv_index = 0  # Missing variables iterating index
        vv_index = 0  # Valid variables iterating index
        bits_remaining = 0

        symbol = []
        for bit_index in range(len(all_variables)):
            if mv_index == len(missing_variables_indices):
                bits_remaining = len(all_variables) - bit_index
                break
            if vv_index == len(valid_bitsubtuple):
                bits_remaining = len(all_variables) - bit_index
                break

            if bit_index == missing_variables_indices[mv_index]:
                symbol.append('*')
                mv_index += 1
            else:
                symbol.append(valid_bitsubtuple[vv_index])
                vv_index += 1

        if bits_remaining > 0:
            if mv_index == len(missing_variables_indices):
                # We need to fill in the rest of valid bits
                for i in range(vv_index, len(valid_bitsubtuple)):
                    symbol.append(valid_bitsubtuple[i])
            if vv_index == len(valid_bitsubtuple):
                # We need to fill the rest with *
                for i in range(bits_remaining):
                    symbol.append('*')

        yield tuple(symbol)


def make_rotate_transition_function(t: Transitions[State]) -> Transitions[State]:
    rotated_transitions: Transitions[State] = {}

    for origin in t:
        for destination in t[origin]:
            if destination not in rotated_transitions:
                rotated_transitions[destination] = {}

            rotated_transitions[destination][origin] = set(t[origin][destination])

    return rotated_transitions


def remove_all_transitions_that_contain_states(t: Transitions[State], states: Set[State]) -> Transitions[State]:
    purged_transitions: Transitions[State] = {}
    for origin in t:
        if origin not in states:
            for destination in t[origin]:
                if destination not in states:
                    if origin not in purged_transitions:
                        purged_transitions[origin] = {}

                    purged_transitions[origin][destination] = set(t[origin][destination])
    return purged_transitions
