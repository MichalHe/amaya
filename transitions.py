from __future__ import annotations
import collections
from typing import (
    Set,
    Dict,
    Any,
    Tuple,
    Union,
    Mapping,
    Optional,
    List,
    Iterable,
    Generator,
    TypeVar,
    Generic
)
import functools
import utils
from dd.autoref import BDD

Symbol = Tuple[Union[str, int], ...]
# State = Union[str, int]
State = TypeVar('State')
T = TypeVar('T')
Transitions = Dict[State, Dict[State, Set[Symbol]]]
VariableNames = Tuple[str, ...]


def unite_alphabets(alphabet1: VariableNames, alphabet2: VariableNames) -> VariableNames:
    return list(sorted(set(alphabet1).union(set(alphabet2))))


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


def extend_symbol_on_index(symbol: Tuple[int, ...], missing_index: int) -> Tuple[Union[int, str], ...]:
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
    missing_indices = get_indices_of_missing_variables(new_variables, old_variables)
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


def iterate_over_active_variables(all_variables: Tuple[str, ...], active_variables: Set[str]):
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


def collect_all_outgoing_symbols_from_state(t: Transitions[State],
                                            origin: State) -> List[Symbol]:
    if origin not in t:
        return []

    out_symbols: List[Symbol] = []
    for dest in t[origin]:
        for symbol in t[origin][dest]:
            out_symbols.append(symbol)
    return out_symbols


def constuct_bdd_from_transition_symbols(s: Set[Symbol], variable_names: List[str], bdd_manager: BDD) -> BDD:
    if not s:
        return None

    def convert_symbol_to_formula(symbol: Symbol) -> str:
        formula_parts = []
        for i, bit in enumerate(symbol):
            if bit == 0:
                formula_parts.append(f'~{variable_names[i]}')
            elif bit == 1:
                formula_parts.append(f'{variable_names[i]}')

        if not formula_parts:
            return 'True'

        return '&'.join(formula_parts)

    exprs: List[BDD] = []

    for symbol in s:
        formula = convert_symbol_to_formula(symbol)
        expr = bdd_manager.add_expr(formula)
        exprs.append(expr)

    return functools.reduce(lambda e0, e1: e0 | e1, exprs)


def get_symbols_intersection(s0: List[Symbol], s1: List[Symbol],
                             variable_names: Tuple[str],
                             bdd_manager: BDD,
                             compress_result: bool = False
                             ) -> List[Symbol]:
    bdd0 = constuct_bdd_from_transition_symbols(s0, variable_names, bdd_manager)
    bdd1 = constuct_bdd_from_transition_symbols(s1, variable_names, bdd_manager)

    if bdd0 is None or bdd1 is None:
        return []

    intersection = bdd0 & bdd1

    symbols = []
    if compress_result:
        for model_eval in bdd_manager.pick_iter(intersection):
            symbol = []
            for vn in variable_names:
                if vn in model_eval:
                    symbol.append(int(model_eval[vn]))
                else:
                    symbol.append('*')

            # symbol = tuple(map(lambda var_name: int(model_eval[var_name]), variable_names))
            symbols.append(tuple(symbol))
    else:
        for model_eval in bdd_manager.pick_iter(intersection, care_vars=variable_names):
            symbol = tuple(map(lambda var_name: int(model_eval[var_name]), variable_names))
            symbols.append(symbol)

    return symbols

def get_bdd_transition_function(t: Transitions[State], var_names: List[str], bdd_manager: BDD) -> Dict[State, Dict[State, BDD]]:
    bdd_t: Dict[State, Dict[State, BDD]] = {}

    for origin in t:
        bdd_t[origin] = {}
        for dest in t[origin]:
            bdd_t[origin][dest] = constuct_bdd_from_transition_symbols(t[origin][dest], var_names, bdd_manager)


BDD_TransitionFn = Dict[State, Dict[State, BDD]]


def construct_transition_fn_to_bddtfn(t: Transitions[State],
                                      var_names: List[str],
                                      bdd_manager: BDD) -> BDD_TransitionFn:
    new_t: BDD_TransitionFn = {}
    for source in t:
        new_t[source] = {}
        for dest in t[source]:
            transition_bdd = constuct_bdd_from_transition_symbols(t[source][dest], var_names, bdd_manager)
            new_t[source][dest] = transition_bdd
    return new_t


StateType = TypeVar('StateType')

class SparseTransitionFunctionBase(Generic[StateType]):
    def __init__(self):
        self.data: Dict[Any, Dict[Any, Set[Symbol]]] = dict()

    def get_symbols_between_states(self, origin, dest) -> Set:
        if origin not in self.data:
            return set()
        if dest not in self.data[origin]:
            return set()
        
        return set(self.data[origin][dest])

    def state_has_post(self, state) -> bool:
        '''Checks whether there is some state reachable from given state.'''
        return state in self.data

    def is_in_state_post(self, origin, state) -> bool:
        '''Checks whether the given state is a direct successor to origin (is in its post set)'''
        if origin not in self.data:
            return False
        return (state in self.data[origin])

    def get_states_with_post_containing(self, state) -> Set:
        states = set()
        for origin in self.data:
            for dest in self.data[origin]:
                if dest == state:
                    states.add(origin)
        return states


class SparseSimpleTransitionFunction(SparseTransitionFunctionBase[StateType]):
    def __init__(self):
        super().__init__()

    def get_transition_target(self, source: StateType, symbol: Symbol) -> List[StateType]:
        if source not in self.data:
            return list()

        out_states: Set[StateType] = set()
        for dest in self.data[source]:
            for t_symbol in self.data[source][dest]:
                if symbols_intersect(t_symbol, symbol):
                    out_states.add(dest)
                    break  # Stop checking symbols, continue with next dest

        return list(out_states)

    def insert_transition(self, source: StateType, symbol: Symbol, dest: StateType):
        if source not in self.data:
            self.data[source] = {}

        if dest not in self.data[source]:
            self.data[source][dest] = set()  # Represent empty relation structure

        self.data[source][dest].add(symbol)

    def rename_states(self, mapping: Dict):
        renamed_data: Dict = {}

        for origin in self.data:
            r_origin = mapping[origin]
            renamed_data[r_origin] = {}

            for dest in self.data[origin]:
                r_dest = mapping[dest]
                renamed_data[r_origin][r_dest] = self.data[origin][dest]

        self.data = renamed_data

    def copy(self) -> SparseSimpleTransitionFunction:
        copy_data: Dict[StateType, Dict[StateType, Set]] = {}

        for source in self.data:
            copy_data[source] = {}
            for dest in self.data[source]:
                copy_data[source][dest] = set(self.data[source][dest])

        copy: SparseSimpleTransitionFunction = SparseSimpleTransitionFunction()
        copy.data = copy_data

        return copy

    @staticmethod
    def union_of(t0: SparseSimpleTransitionFunction, t1: SparseSimpleTransitionFunction) -> SparseSimpleTransitionFunction:
        union = t0.copy()

        for source in t1.data:
            if source not in union.data:
                # We can copy the rest right away
                union.data[source] = {}
                for dest in t1.data[source]:
                    union.data[source][dest] = t1.data[source][dest]
            else:
                # Source is present in union
                for dest in t1.data[source]:
                    if dest in union.data[source]:
                        # We need to unite the BDDs -- we can get from source to dest either via BDD#0 **or** BDD#1
                        union.data[source][dest] = union.data[source][dest].union(t1.data[source][dest])
                    else:
                        union.data[source][dest] = set(t1.data[source][dest])

        return union

    def extend_to_new_alphabet_symbols(self, new_variables, old_variables):
        missing_indices = get_indices_of_missing_variables(new_variables, old_variables)

        for origin in self.data:
            for dest in self.data[origin]:
                self.data[origin][dest] = set(
                    map(
                        lambda old_symbol: extend_symbol_with_missing_indices(
                            old_symbol, missing_indices),  # type: ignore
                        self.data[origin][dest]))

    def complete_with_trap_state(self, alphabet, states: List, trap_state: Any = 'TRAP') -> bool:
        trap_state_present: bool = False

        # This is basically the whole alphabet, with nonactive symbols compacted.
        alphabet_active_symbols = set(iterate_over_active_variables(alphabet.variable_names, alphabet.active_variables))

        for origin in states:
            out_symbols = set()
            if origin in self.data:
                for dest in self.data[origin]:
                    out_symbols.update(self.data[origin][dest])

            missing_symbols = alphabet_active_symbols - out_symbols

            if missing_symbols and not trap_state_present:
                universal_symbol = tuple(['*' for v in alphabet.variable_names])
                self.insert_transition(trap_state, universal_symbol, trap_state)
                trap_state_present = True

            for missing_symbol in missing_symbols:
                # WARN: Mutating dictionary while iterating over it.
                self.insert_transition(origin, missing_symbol, trap_state)
        return trap_state_present

    def project_bit_away(self, bit_pos: int):
        def do_projection_on_symbol(pos: int, symbol: Symbol) -> Symbol:
            return symbol[:pos] + ('*', ) + symbol[pos + 1:]

        symbol_projection_func = functools.partial(do_projection_on_symbol, bit_pos)
        for origin in self.data:
            for dest in self.data[origin]:
                self.data[origin][dest] = set(map(symbol_projection_func, self.data[origin][dest]))

    def iter(self) -> Generator[Tuple[StateType, Symbol, StateType], None, None]:
        for origin in self.data:
            for dest in self.data[origin]:
                for sym in self.data[origin][dest]:
                    yield (origin, sym, dest)

    def remove_nonfinishing_states(self, states: Set, final_states: Set) -> Set:
        '''BFS on rotated transitions'''
        rotated_transitions = make_rotate_transition_function(self.data)

        queue = collections.deque(final_states)
        reachable_states = set()

        while queue:
            current_state = queue.popleft()
            reachable_states.add(current_state)

            # We might be processing a state that is terminal
            if current_state not in rotated_transitions:
                continue

            for reachable_state in rotated_transitions[current_state]:
                if reachable_state not in reachable_states:
                    queue.append(reachable_state)

        unreachable_states = states - reachable_states
        if unreachable_states:
            self.data = remove_all_transitions_that_contain_states(self.data, unreachable_states)

        return reachable_states

    def calculate_path_from_dfs_traversal_history(self, traversal_history, current_state, initial_states: Set):
        return get_word_from_dfs_results(self.data,
                                         traversal_history, current_state,
                                         initial_states)



class SparseBDDTransitionFunction(SparseTransitionFunctionBase[StateType]):
    def __init__(self, manager: BDD, alphabet):
        self.data: Dict[Any, Dict[Any, BDD]] = dict()
        self.alphabet = alphabet
        self.manager = manager

    def get_transition_target(self, source: StateType, symbol: Symbol) -> List[StateType]:
        if source not in self.data:
            return list()

        out_states: Set[StateType] = set()

        for dest in self.data[source]:
            bdd_expr = self.data[source][dest]
            cube = self.get_cube_from_symbol(symbol)
            subst_expr = self.manager.let(cube, bdd_expr)

            if not self.manager.to_expr(subst_expr) == 'FALSE':
                out_states.add(dest)

        return list(out_states)

    def get_cube_from_symbol(self, symbol) -> Dict:
        variable_names = self.alphabet.variable_names
        cube = dict()
        for bit, var in zip(symbol, variable_names):
            if bit == 0:
                cube[var] = False
            elif bit == 1:
                cube[var] = True
        return cube

    def insert_transition(self, source: StateType, symbol: Symbol, dest: StateType):
        if source not in self.data:
            self.data[source] = {}

        if dest not in self.data[source]:
            self.data[source][dest] = self.manager.add_expr('FALSE')  # Represent empty relation structure

        cube = self.get_cube_from_symbol(symbol)
        new_transition_expr = self.manager.cube(cube)

        self.data[source][dest] = self.manager.apply('or', self.data[source][dest], new_transition_expr)
    
    def _write_transition_bdd(self, source: StateType, bdd: Any, dest: StateType):
        if source not in self.data:
            self.data[source] = {}
        self.data[source][dest] = bdd

    def rename_states(self, mapping: Dict):
        renamed_data: Dict = {}

        for origin in self.data:
            r_origin = mapping[origin]
            renamed_data[r_origin] = {}

            for dest in self.data[origin]:
                r_dest = mapping[dest]
                renamed_data[r_origin][r_dest] = self.data[origin][dest]

        self.data = renamed_data

    def copy(self) -> SparseBDDTransitionFunction:
        copy_data: Dict[StateType, Dict[StateType, BDD]] = {}

        for source in self.data:
            copy_data[source] = {}
            for dest in self.data[source]:
                copy_data[source][dest] = self.data[source][dest]

        copy = SparseBDDTransitionFunction(self.manager, self.alphabet)  # type: SparseBDDTransitionFunction[Any]
        copy.data = copy_data

        return copy

    @staticmethod
    def union_of(t0: SparseBDDTransitionFunction, t1: SparseBDDTransitionFunction) -> SparseBDDTransitionFunction:
        union = t0.copy()

        for source in t1.data:
            if source not in union.data:
                # We can copy it right away
                union.data[source] = {}
                for dest in t1.data[source]:
                    union.data[source][dest] = t1.data[source][dest]
            else:
                # Source is present in union
                for dest in t1.data[source]:
                    if dest in union.data[source]:
                        # We need to unite the BDDs -- we can get from source to dest either via BDD#0 **or** BDD#1
                        union.data[source][dest] = union.manager.apply('or', union.data[source][dest], t1.data[source][dest])
                    else:
                        union.data[source][dest] = t1.data[source][dest]

        return union

    def _iter_compact_models(self, bdd):
        var_names = self.alphabet.variable_names
        for model in self.manager.pick_iter(bdd):
            symbol = []
            for v_name in var_names:
                bit = model.get(v_name, '*')
                bit = int(bit) if type(bit) == bool else bit
                symbol.append(bit)
            yield tuple(symbol)

    def iter(self) -> Generator[Tuple[StateType, Symbol, StateType], None, None]:
        for source in self.data:
            for dest in self.data[source]:
                bdd = self.data[source][dest]
                yield from self._iter_compact_models(bdd)

    def complete_with_trap_state(self, alphabet, states: List, trap_state: Any = 'TRAP') -> bool:
        trap_state_present: bool = False

        for origin in states:
            out_bdd = self.manager.add_expr('FALSE')
            if origin in self.data:
                for dest in self.data[origin]:
                    out_bdd = self.manager.apply('or', out_bdd, self.data[origin][dest])
            
            out_bdd_complement = self.manager.apply('not', out_bdd)
            is_complement_empty = self.manager.to_expr(out_bdd_complement) == 'FALSE'

            if not is_complement_empty and not trap_state_present:
                universal_symbol = self.manager.add_expr('TRUE')
                self._write_transition_bdd(trap_state, universal_symbol, trap_state)
                trap_state_present = True

            if not is_complement_empty:
                # WARN: Mutating dictionary while iterating over it.
                self._write_transition_bdd(origin, out_bdd_complement, trap_state)
        return trap_state_present