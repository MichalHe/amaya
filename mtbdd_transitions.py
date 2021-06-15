from __future__ import annotations
import ctypes as ct
from typing import Dict, Any, Set, Tuple, Union, List, Iterable, Optional
from collections import defaultdict

mtbdd_wrapper = ct.CDLL('./amaya-mtbdd.so')
mtbdd_wrapper.init_machinery()

c_side_state_type = ct.c_int64

mtbdd_wrapper.amaya_mtbdd_build_single_terminal.argtypes = (
    ct.c_uint32,             # Automaton ID
    ct.POINTER(ct.c_uint8),  # Transitions symbols [symbol0_bit0, ... symbol0_bitN, symbol1_bit0 ...]
    ct.c_uint32,             # Symbol count
    ct.c_uint32,             # Variable count
    ct.POINTER(c_side_state_type),  # Terminal testination set
    ct.c_uint32              # Destination set size
)
mtbdd_wrapper.amaya_mtbdd_build_single_terminal.restype = ct.c_ulong  # MTBDD

mtbdd_wrapper.amaya_mtbdd_get_transition_target.argtypes = (
    ct.c_ulong,
    ct.POINTER(ct.c_uint8),
    ct.c_uint32,
    ct.POINTER(ct.c_uint32)
)
mtbdd_wrapper.amaya_mtbdd_get_transition_target.restype = ct.POINTER(c_side_state_type)

mtbdd_wrapper.amaya_mtbdd_rename_states.argtypes = (
    ct.POINTER(ct.c_ulong),  # MTBDD roots
    ct.c_uint32,             # root_count
    ct.POINTER(c_side_state_type),  # Mappings [old_name1, new_name1, ...]
    ct.c_uint32,             # Mapping size
)
mtbdd_wrapper.amaya_mtbdd_rename_states.restype = ct.POINTER(ct.c_ulong)

mtbdd_wrapper.amaya_project_variables_away.argtypes = (
    ct.c_ulong,
    ct.POINTER(ct.c_uint32),
    ct.c_uint32
)

mtbdd_wrapper.amaya_mtbdd_get_leaves.argtypes = (
    ct.c_ulong,
    ct.POINTER(ct.POINTER((ct.c_uint32))),  # Leaf sizes
    ct.POINTER(ct.c_uint32),                # Leaf count
    ct.POINTER(ct.POINTER(ct.c_voidp))      # Leaf transition destination sets, void***
)
mtbdd_wrapper.amaya_mtbdd_get_leaves.restype = ct.POINTER(c_side_state_type)  # Pointer to array containing the states

mtbdd_wrapper.amaya_unite_mtbdds.argtypes = (
    ct.c_ulong,  # MTBDD a
    ct.c_ulong,  # MTBDD b
    ct.c_uint32  # Resulting Automaton ID
)
mtbdd_wrapper.amaya_unite_mtbdds.restype = ct.c_ulong

mtbdd_wrapper.amaya_mtbdd_get_state_post.argtypes = (
    ct.c_ulong,  # MTBDD m
    ct.POINTER(ct.c_uint32),  # MTBDD result array size
)
mtbdd_wrapper.amaya_mtbdd_get_state_post.restype = ct.POINTER(c_side_state_type)

mtbdd_wrapper.amaya_mtbdd_do_pad_closure.argtypes = (
    c_side_state_type,                  # Left state
    ct.c_ulong,                         # MTBDD left
    c_side_state_type,                  # Right state
    ct.c_ulong,                         # MTBDD right
    ct.POINTER(c_side_state_type),      # Array with final states.
    ct.c_uint32                         # Number of final states
)
mtbdd_wrapper.amaya_mtbdd_do_pad_closure.restype = ct.c_bool

mtbdd_wrapper.amaya_mtbdd_get_transitions.argtypes = (
    ct.c_ulong,                                     # MTBDD root
    ct.POINTER(ct.c_uint32),                        # Array with variables.
    ct.c_uint32,                                    # Size of array with variables
    ct.POINTER(ct.c_uint32),                        # OUT, number of transitions
    ct.POINTER(ct.POINTER(c_side_state_type)),      # OUT Pointer to array containing destinations states
    ct.POINTER(ct.POINTER(ct.c_uint32)),            # OUT Pointer to array containing sizes of serialized destinations states
)
mtbdd_wrapper.amaya_mtbdd_get_transitions.restype = ct.POINTER(ct.c_uint8)

mtbdd_wrapper.amaya_mtbdd_change_automaton_id_for_leaves.argtypes = (
    ct.POINTER(ct.c_ulong),               # Array of mtbdd roots.
    ct.c_uint32,                          # Roots cnt.
    ct.c_uint32                           # New automaton ID.
)

mtbdd_wrapper.amaya_mtbdd_intersection.argtypes = (
    ct.c_ulong,     # MTBDD 1
    ct.c_ulong,     # MTBDD 2
    ct.c_uint32,    # automaton id

    ct.POINTER(ct.POINTER(c_side_state_type)),   # New discoveries made during intersection
    ct.POINTER(ct.c_uint32),                     # New discoveries size.
)
mtbdd_wrapper.amaya_mtbdd_intersection.restype = ct.c_ulong

mtbdd_wrapper.amaya_replace_leaf_contents_with.argtypes = (
    ct.c_voidp,                          # Leaf pointer
    ct.POINTER(c_side_state_type),       # New contents
    ct.c_uint32                          # Content length
)

mtbdd_wrapper.amaya_begin_intersection.argtypes = (
    ct.c_bool,                      # Is early pruning ON?
    ct.POINTER(c_side_state_type),  # Final states
    ct.c_uint32                     # Final states cnt
)
mtbdd_wrapper.amaya_end_intersection.argtypes = ()

mtbdd_wrapper.amaya_update_intersection_state.argtypes = (
    ct.POINTER(c_side_state_type),     # Metastates [m0_0, m0_1, m1_0, m1_1 ...]
    ct.POINTER(c_side_state_type),     # Metastate names
    ct.c_uint32,                       # automaton id
)

mtbdd_wrapper.amaya_set_debugging.argtypes = (ct.c_bool, )

mtbdd_wrapper.amaya_rename_metastates_to_int.argtypes = (
    ct.POINTER(ct.c_ulong),   # The mtbdd roots that were located during determinization
    ct.c_uint32,              # The number of mtbdd roots
    c_side_state_type,        # The number from which the numbering will start
    ct.c_uint32,              # The ID of the resulting automaton
    ct.POINTER(ct.POINTER(ct.c_uint32)),  # OUT Metastates sizes
    ct.POINTER(ct.c_uint32)   # OUT Metastates count
)
mtbdd_wrapper.amaya_rename_metastates_to_int.restype = ct.POINTER(c_side_state_type)

mtbdd_wrapper.amaya_complete_mtbdd_with_trapstate.argtypes = (
    ct.c_ulong,                 # The MTBDD
    ct.c_uint32,                # Automaton ID
    c_side_state_type,          # The trapstate ID
    ct.POINTER(ct.c_bool)       # OUT - Information about whether the operator did add a transition to a trapstate somewhere
)

mtbdd_wrapper.amaya_complete_mtbdd_with_trapstate.restype = ct.c_long

mtbdd_wrapper.amaya_get_state_post_with_some_transition.argtypes = (
    ct.c_ulong,                 # The mtbdd
    ct.POINTER(ct.c_uint32),    # An array with variables
    ct.c_uint32,                # The number of used variables.
    ct.POINTER(ct.POINTER(ct.c_uint8)),  # OUT Symbols for the reachable states
    ct.POINTER(ct.c_uint32)              # OUT The number of located states
)
mtbdd_wrapper.amaya_get_state_post_with_some_transition.restype = ct.POINTER(c_side_state_type)

mtbdd_wrapper.amaya_remove_states_from_transitions.argtypes = (
    ct.POINTER(ct.c_ulong),
    ct.c_uint32,
    ct.POINTER(c_side_state_type),
    ct.c_uint32
)
mtbdd_wrapper.amaya_remove_states_from_transitions.restype = ct.POINTER(ct.c_ulong)

# mtbdd_wrapper.amaya_print_dot.argtypes = (
#     ct.c_ulong,
#     ct.c_int32
# )


mtbdd_false = ct.c_ulong.in_dll(mtbdd_wrapper, 'w_mtbdd_false')
MTBDD = ct.c_ulong
Symbol = Tuple[Union[str, int], ...]

# Required functions:
# -> get_symbols_between_states?
# -> state_has_post?
# -> is_in_state_post?
# -> get_states_with_post_containig

# Needs implementation:
# -> complete_with_trap_state?
# -> remove_nonfinishing_states?

# cannot/will not:
# -> copy :: () -> cannot

# Done functions:
# -> project_bit_away --> project_variable_away
# -> union_of
# -> iter
# -> insert_transition
# -> get_transition_target :: (source_state, symbol) -> List[state]
# -> rename_states :: (state_mapping)


class MTBDDTransitionFn():
    def __init__(self, alphabet_variables: List[int], automaton_id: int):
        self.mtbdds: Dict[Any, MTBDD] = {}
        self.post_cache = dict()
        self.is_post_cache_valid = False
        self.alphabet_variables = alphabet_variables
        self.automaton_id = automaton_id

        self.debug_cnt = 0

    def insert_transition(self,
                          source: Any,
                          symbol: Symbol,
                          dest: int):
        assert type(dest) == int
        assert type(source) == int

        if source not in self.mtbdds:
            current_mtbdd = mtbdd_false
            self.mtbdds[source] = current_mtbdd
        else:
            current_mtbdd = self.mtbdds[source]

        cube_size, cube = self.convert_symbol_to_mtbdd_cube(symbol)

        # Destination:
        dest_state = (c_side_state_type * 1)()
        dest_state[0] = dest

        # Construct cube from destination state
        mtbdd_new = mtbdd_wrapper.amaya_mtbdd_build_single_terminal(
            ct.c_uint32(self.automaton_id),
            ct.cast(cube, ct.POINTER(ct.c_uint8)),      # Transition symbols, 2d array
            ct.c_uint32(1),                             # Transitions symbols count
            cube_size,                                  # Variables count
            ct.cast(dest_state, ct.POINTER(c_side_state_type)),  # Set of the terminal states
            ct.c_uint32(1),                             # Destination set size
        )
        # @DeleteMe
        resulting_mtbdd = mtbdd_wrapper.amaya_unite_mtbdds(mtbdd_new, current_mtbdd, self.automaton_id)
        self.mtbdds[source] = resulting_mtbdd

    @staticmethod
    def write_mtbdd_dot_to_file(m, filename):
        '''Writes the dot representation of given MTBDD m to the file.'''
        output_f = open(filename, 'w')
        fd = output_f.fileno()

        mtbdd_wrapper.amaya_print_dot(
            m,  # The mtbdd to be printed out
            fd  # File descriptor
        )

        output_f.close()  # The C side does not close the file descriptor

    def convert_symbol_to_mtbdd_cube(self, symbol: Symbol):
        cube = (ct.c_uint8 * len(symbol) * 1)()
        for i, bit in enumerate(symbol):
            if bit == '*':
                cube[0][i] = ct.c_uint8(2)
            else:
                cube[0][i] = ct.c_uint8(int(bit))

        cube_size = ct.c_uint32(len(symbol))

        return cube_size, cube

    def get_transition_target(self, source, symbol):
        '''Retrieve the set of states that lead from `source` via `symbol`.'''
        if source not in self.mtbdds:
            return set()
        mtbdd = self.mtbdds[source]

        cs, c = self.convert_symbol_to_mtbdd_cube(symbol)
        result_size = ct.c_uint32(0)
        result = mtbdd_wrapper.amaya_mtbdd_get_transition_target(
            mtbdd,
            ct.cast(c, ct.POINTER(ct.c_uint8)),      # Cube
            cs,     # Cube size
            ct.byref(result_size)
        )

        dest_ = []
        for i in range(int(result_size.value)):
            dest_.append(result[i])

        mtbdd_wrapper.amaya_do_free(result)
        return set(dest_)

    def rename_states(self, mappings: Dict[int, int]):
        '''Renames all states referenced within stored mtbdds with the
        provided mapping.

        Requires all referenced states to be present in the mapping.
        '''
        flat_mapping_size = 2*len(mappings)
        arr = (c_side_state_type * flat_mapping_size)()

        for i, mapping in enumerate(mappings.items()):
            old, new = mapping
            arr[2*i] = c_side_state_type(old)
            arr[2*i + 1] = c_side_state_type(new)

        mapping_ptr = ct.cast(arr, ct.POINTER(c_side_state_type))
        mapping_size = ct.c_uint32(len(mappings))

        mtbdd_roots = (ct.c_ulong * len(self.mtbdds))()
        for i, origin_state in enumerate(self.mtbdds):
            mtbdd_roots[i] = self.mtbdds[origin_state]
        root_cnt = ct.c_uint32(len(self.mtbdds))

        renamed_mtbdds = mtbdd_wrapper.amaya_mtbdd_rename_states(
            ct.cast(mtbdd_roots, ct.POINTER(ct.c_ulong)),
            root_cnt,
            mapping_ptr,
            mapping_size
        )

        # We still need to replace the actual origin states within self.mtbdds
        new_mtbdds = dict()
        for i, state_old_mtbdd_pair in enumerate(self.mtbdds.items()):
            state, _ = state_old_mtbdd_pair
            new_mtbdds[mappings[state]] = renamed_mtbdds[i]
        self.mtbdds = new_mtbdds

    def project_variable_away(self, variable: int):
        '''Projects away the variable with given number from every MTBDD stored
        within this transition function.

        Not sure what happens when trying to project a variable that is not
        present.'''
        assert variable > 0, 'MTBDD variables are numbered via ints from 1 up'

        variables = (ct.c_uint32 * 1)(variable)
        for state in self.mtbdds:
            mtbdd = self.mtbdds[state]
            new_mtbdd = mtbdd_wrapper.amaya_project_variables_away(
                mtbdd,
                variables,
                ct.c_uint32(1)
            )
            self.mtbdds[state] = new_mtbdd

    @staticmethod
    def get_mtbdd_leaves(mtbdd: MTBDD,
                         fetch_leaf_tds_ptrs_into: List = None) -> List[List[int]]:
        ''' Internal procedure. '''
        leaf_sizes = ct.POINTER(ct.c_uint32)()
        leaf_cnt = ct.c_uint32()
        leaf_tds_arr = ct.POINTER(ct.c_voidp)()  # NULL pointer

        leaf_tds_arr_ = ct.byref(leaf_tds_arr) if fetch_leaf_tds_ptrs_into is not None else ct.POINTER(ct.POINTER(ct.c_voidp))()
        leaf_contents = mtbdd_wrapper.amaya_mtbdd_get_leaves(
            mtbdd,
            ct.byref(leaf_sizes),
            ct.byref(leaf_cnt),
            leaf_tds_arr_
        )

        state_i = 0
        leaves = []
        for i in range(leaf_cnt.value):
            leaf = []
            for j in range(leaf_sizes[i]):
                state = leaf_contents[state_i]
                state_i += 1
                leaf.append(state)
            leaves.append(leaf)

        if fetch_leaf_tds_ptrs_into is not None:
            for i in range(leaf_cnt.value):
                fetch_leaf_tds_ptrs_into.append(leaf_tds_arr[i])
            mtbdd_wrapper.amaya_do_free(leaf_tds_arr)

        mtbdd_wrapper.amaya_do_free(leaf_sizes)
        mtbdd_wrapper.amaya_do_free(leaf_contents)

        return leaves

    def get_union_mtbdd_for_states(self, states: List[int], resulting_automaton_id: int) -> MTBDD:
        '''Does what name suggests.'''
        resulting_mtbdd = mtbdd_false
        for state in states:
            if state not in self.mtbdds:
                continue
            mtbdd = self.mtbdds[state]
            resulting_mtbdd = mtbdd_wrapper.amaya_unite_mtbdds(
                mtbdd,
                resulting_mtbdd,
                resulting_automaton_id)
        if resulting_mtbdd == mtbdd_false:
            return None
        return resulting_mtbdd

    def get_state_post(self, state: int) -> List[int]:
        mtbdd = self.mtbdds.get(state, None)
        if mtbdd is None:
            return []
        result_size = ct.c_uint32()
        state_post_arr = mtbdd_wrapper.amaya_mtbdd_get_state_post(mtbdd, ct.byref(result_size))

        result = []
        for i in range(result_size.value):
            result.append(state_post_arr[i])
        return result

    def get_state_pre(self, state: int, initial_states: Iterable[int]) -> List[int]:
        if not self.is_post_cache_valid:
            self.post_cache = self.build_automaton_adjacency_matrix(initial_states)

        # Use the post cache to calculate state pre.
        state_pre = set()
        for s in self.post_cache:
            s_post = self.post_cache[s]
            if state in s_post:
                state_pre.add(s)
        return list(state_pre)

    def build_automaton_adjacency_matrix(self, initial_states: Iterable[int]) -> Dict[int, Set[int]]:
        '''Builds the image of the transition function with the information
        about transition symbols left out.'''

        morph_map = {}
        work_queue = list(initial_states)
        while work_queue:
            state = work_queue.pop(-1)
            state_post = set(self.get_state_post(state))
            if not state_post:
                # state is terminal
                continue
            morph_map[state] = state_post
            for new_state in state_post:
                # Check whether the state is not scheduled/processed already
                if new_state not in work_queue and new_state not in morph_map:
                    work_queue.append(new_state)
        return morph_map

    @staticmethod
    def reverse_adjacency_matrix(adjacency_matrix: Dict[int, Set[int]]) -> Dict[int, Set[int]]:
        reversed_adjacency_matrix: Dict[int, Set[int]] = defaultdict(set)
        for origin_state in adjacency_matrix:
            for destination_state in adjacency_matrix[origin_state]:
                reversed_adjacency_matrix[destination_state].add(origin_state)
        return reversed_adjacency_matrix

    def do_pad_closure(self, initial_states: Iterable[int], final_states: List[int]):
        '''Performs padding closure on the underlying automatic structure.'''
        # Initialize the working queue with all states, that have some final
        # state in their Post
        adjacency_matrix = self.build_automaton_adjacency_matrix(initial_states)
        reversed_adjacency_matrix = MTBDDTransitionFn.reverse_adjacency_matrix(adjacency_matrix)

        # We dont wanna start with final states directly, instead start with their
        # predecesors
        final_states_predecesors: Set[int] = set()
        for fs in final_states:
            final_states_predecesors.update(reversed_adjacency_matrix[fs])
        work_queue = list(final_states_predecesors)

        while work_queue:
            state = work_queue.pop()
            state_pre_list = reversed_adjacency_matrix[state]
            for pre_state in state_pre_list:
                # print(f'Applying PC on: {pre_state} ---> {state}')
                had_pc_effect = self._do_pad_closure_single(pre_state, state, final_states)

                if had_pc_effect:
                    if pre_state not in work_queue:
                        work_queue.append(pre_state)

    def _do_pad_closure_single(self, left_state: int, right_state: int, final_states: List[int]) -> bool:
        '''(left_state) --A--> (right_state) --B--> final_states'''
        left_mtbdd = self.mtbdds.get(left_state, None)
        right_mtbdd = self.mtbdds.get(right_state, None)

        c_left_state = c_side_state_type(left_state)
        c_right_state = c_side_state_type(right_state)

        if left_mtbdd is None or right_mtbdd is None:
            return  # We need a pair of mtbdds to perform padding closure.

        # Convert the set into C array
        final_states_arr = (c_side_state_type * len(final_states))(*list(final_states))
        final_states_cnt = ct.c_uint32(len(final_states))

        was_modified = mtbdd_wrapper.amaya_mtbdd_do_pad_closure(
            c_left_state,
            left_mtbdd,
            c_right_state,
            right_mtbdd,
            final_states_arr,
            final_states_cnt
        )

        return bool(was_modified)

    def iter_single_state(self, state: int, variables: Optional[List[int]] = None):
        '''Iterates over all transitions that originate in the given `state`.
        The transitions are yielded in their compressed form - the don't care bits
        carry the value `*`.
        '''
        if variables is None:
            variables = self.alphabet_variables

        mtbdd = self.mtbdds.get(state, None)
        if mtbdd is None:
            return

        _vars = (ct.c_uint32 * len(variables))(*variables)

        transition_dest_states = ct.POINTER(c_side_state_type)()
        transition_dest_states_sizes = ct.POINTER(ct.c_uint32)()
        transition_count = ct.c_uint32()

        symbols = mtbdd_wrapper.amaya_mtbdd_get_transitions(
            mtbdd,
            ct.cast(_vars, ct.POINTER(ct.c_uint32)),
            ct.c_uint32(len(variables)),
            ct.byref(transition_count),
            ct.byref(transition_dest_states),
            ct.byref(transition_dest_states_sizes)
        )

        s_length = len(variables)
        i = 0

        # ti stands for the current transition index
        for ti in range(transition_count.value):
            symbol = []
            for s in range(s_length):
                symbol.append(symbols[s_length*ti + s])

            dest = []
            dest_size = transition_dest_states_sizes[ti]
            for _ in range(dest_size):
                dest.append(transition_dest_states[i])
                i += 1

            for dest_state in dest:
                yield (state, tuple(symbol), dest_state)

        mtbdd_wrapper.amaya_do_free(transition_dest_states)
        mtbdd_wrapper.amaya_do_free(transition_dest_states_sizes)
        mtbdd_wrapper.amaya_do_free(symbols)

    def iter_compressed(self, variables: Optional[List[int]] = None):
        for origin in self.mtbdds:
            yield from self.iter_single_state(origin)

    def iter(self, variables: Optional[List[int]] = None):
        '''Iterates over all transitions stored within this transition function.
        The transitions are yielded in form of (Origin, Symbol, Destination), where:
            - Origin is the origin for the transitions,
            - Symbol is **uncompressed** transition symbol e.g. (1, 0, 0) for alphabet of 3 vars,
            - Destination is a **single** destination state.
        '''
        for origin in self.mtbdds:
            for compact_symbol in self.iter_single_state(origin):
                yield from MTBDDTransitionFn._iter_unpack_transition(compact_symbol)

    @staticmethod
    def _iter_unpack_transition(transition):
        '''Expands the compact represenation of some transitions symbols.

        Example:
            (S, (2, 0, 1), D) --- expands into --->>> (S, (0, 0, 1), D), (S, (1, 0, 1), D)
        Note:
            The bit value 2 represents don't care bit.
        '''
        stack = [tuple()]
        origin_state, compressed_symbol, destination_state = transition
        while stack:
            cs = stack.pop(-1)
            i = len(cs)
            while i != len(compressed_symbol):
                if compressed_symbol[i] == 2:
                    stack.append(cs + (1,))  # Do the high branch later
                    cs = cs + (0,)
                else:
                    cs += (compressed_symbol[i],)
                i += 1
            yield (origin_state, cs, destination_state)

    def get_intersection_for_states(self, states: Iterable[int]):
        '''Calculates a MTBDD that contains only transitions present
        in every transition function of the given states.'''

        intersect_start = 0
        # Locate first of the states that has some transitions stored.
        for state in states:
            if state in self.mtbdds:
                break
            else:
                intersect_start += 1

        if intersect_start == len(states):
            return mtbdd_false

        intersect_mtbdd = self.mtbdds[states[intersect_start]]
        for i in range(intersect_start + 1, len(states)):
            state = states[i]
            if state not in self.mtbdds:
                continue

            curr_mtbdd = self.mtbdds[state]
            print(curr_mtbdd)
            intersect_mtbdd = mtbdd_wrapper.amaya_mtbdd_intersection(
                intersect_mtbdd,
                curr_mtbdd
            )

        return intersect_mtbdd

    @staticmethod
    def compute_mtbdd_intersect(mtbdd1: MTBDD,
                                mtbdd2: MTBDD,
                                result_id: int,
                                generated_metastates: Optional[Dict[int, Tuple[int, int]]] = None) -> MTBDD:
        '''Computes the intersection MTBDD for given MTBDDs'''

        discovered_states_arr = ct.POINTER(c_side_state_type)()
        discovered_states_cnt = ct.c_uint32()

        intersect_mtbdd = mtbdd_wrapper.amaya_mtbdd_intersection(
            mtbdd1,
            mtbdd2,
            ct.c_uint32(result_id),
            ct.byref(discovered_states_arr),
            ct.byref(discovered_states_cnt)
        )

        if generated_metastates is not None:
            for i in range(discovered_states_cnt.value):
                meta_left = discovered_states_arr[3*i]
                meta_right = discovered_states_arr[3*i + 1]
                state = discovered_states_arr[3*i + 2]
                generated_metastates[state] = (meta_left, meta_right)

        if discovered_states_cnt.value > 0:
            mtbdd_wrapper.amaya_do_free(discovered_states_arr)

        return intersect_mtbdd

    @staticmethod
    def union_of(mtfn0: MTBDDTransitionFn,
                 mtfn1: MTBDDTransitionFn,
                 new_automaton_id: int) -> MTBDDTransitionFn:
        '''Creates a new MTBDD transition function that contains transitions
        from both transition functions.'''

        assert mtfn0.alphabet_variables == mtfn1.alphabet_variables, \
            'MTBBDs require to have the same set of variables.'

        resulting_mtbdds: Dict[int, MTBDD] = dict()
        resulting_mtbdds.update(mtfn0.mtbdds)
        for s1, m1 in mtfn1.mtbdds.items():
            assert s1 not in resulting_mtbdds, \
                f'The union should be calculated on states that have been renamed first. {s1} in {resulting_mtbdds}'
            resulting_mtbdds[s1] = m1

        union_tfn = MTBDDTransitionFn(mtfn0.alphabet_variables, new_automaton_id)
        union_tfn.mtbdds = resulting_mtbdds

        # We need to propagate the new automaton down to mtbdd leaves
        union_tfn.change_automaton_ids_for_leaves(new_automaton_id)
        return union_tfn

    @staticmethod
    def replace_leaf_contents_with(leaf_ptr, contents: List[int]):
        contents_size = ct.c_uint32(len(contents))
        contents_arr = (c_side_state_type * len(contents))()
        for i, x in enumerate(contents):
            contents_arr[i] = c_side_state_type(x)

        mtbdd_wrapper.amaya_replace_leaf_contents_with(
            leaf_ptr,
            ct.cast(contents_arr, ct.POINTER(c_side_state_type)),
            contents_size
        )

    @staticmethod
    def begin_intersection(prune: Tuple[bool, Iterable[int]] = (False, [])):
        '''Informs the C side that global state for the intersection should be prepared.
        Params:
            prune - The pruning configuration - tuple of two items:
                0th - (bool) - is pruninig on?
                1th - (List[int]) - List of final states that when detected will not be generated.

                This pruning should be used with great care - only when no determinization
                was performed (or other procedure that manipulates which states are final),
                as it relies on the property that the final state in presburger NFA (over \\Z)
                has no states in its Post set.
        Returns:
            None
        '''
        should_prune, states = prune
        _should_prune = ct.c_bool(should_prune)
        _states = (c_side_state_type * len(states))(*states)
        _states_cnt = ct.c_uint32(len(states))
        mtbdd_wrapper.amaya_begin_intersection(
            _should_prune,
            ct.cast(_states, ct.POINTER(c_side_state_type)),
            _states_cnt)

    @staticmethod
    def update_intersection_state(state_update: Dict[int, Tuple[int, int]]):
        size = len(state_update)

        metastates_arr = (c_side_state_type * (2*size))()
        metastates_names = (c_side_state_type * size)()
        cnt = ct.c_uint32(size)

        for i, mapping in enumerate(state_update.items()):
            state, metastate = mapping
            metastates_arr[2*i] = c_side_state_type(metastate[0])
            metastates_arr[2*i + 1] = c_side_state_type(metastate[1])
            metastates_names[i] = c_side_state_type(state)

        mtbdd_wrapper.amaya_update_intersection_state(
            ct.cast(metastates_arr, ct.POINTER(c_side_state_type)),
            ct.cast(metastates_names, ct.POINTER(c_side_state_type)),
            cnt
        )

    @staticmethod
    def end_intersection():
        mtbdd_wrapper.amaya_end_intersection()

    @staticmethod
    def rename_metastates_after_determinization(mtbdds: Iterable[MTBDD],
                                                resulting_automaton_id: int,
                                                start_numbering_from: int = 0) -> Dict[Tuple[int, ...], int]:
        in_mtbdds = (ct.c_ulong * len(mtbdds))()
        for i, mtbdd in enumerate(mtbdds):
            in_mtbdds[i] = mtbdd
        in_mtbdd_cnt = ct.c_uint32(len(mtbdds))
        in_res_automaton_id = ct.c_uint32(resulting_automaton_id)
        in_start_numbering_from = c_side_state_type(start_numbering_from)

        out_metastates_sizes = ct.POINTER(ct.c_uint32)()
        out_metastates_cnt = ct.c_uint32()

        out_metastates_serialized = mtbdd_wrapper.amaya_rename_metastates_to_int(
            ct.cast(in_mtbdds, ct.POINTER(ct.c_ulong)),
            in_mtbdd_cnt,
            in_start_numbering_from,
            in_res_automaton_id,
            ct.byref(out_metastates_sizes),
            ct.byref(out_metastates_cnt),
        )
        mapping = {}
        metastates_cnt = out_metastates_cnt.value
        metastates_serialized_i = 0
        _start_from = start_numbering_from
        for i in range(metastates_cnt):
            metastate = []
            metastate_size = out_metastates_sizes[i]
            for j in range(metastate_size):
                metastate.append(out_metastates_serialized[metastates_serialized_i])
                metastates_serialized_i += 1

            mapping[tuple(metastate)] = _start_from
            _start_from += 1

        mtbdd_wrapper.amaya_do_free(out_metastates_serialized)
        mtbdd_wrapper.amaya_do_free(out_metastates_sizes)

        return mapping

    @staticmethod
    def complete_mtbdd_with_trapstate(mtbdd: ct.c_long, automaton_id: int, trapstate_id: int) -> Tuple[ct.c_long, bool]:
        '''Wrapper call.

        Add a transition to the given trapstate for every alphabet symbol
        for which the given mtbdd does not have any (valid) transition.

        Returns the mtbdd resulting from the completion (might be unchanged if the
        mtbdd already was complete) and the information about whether the operation
        did indeed modify the mtbdd somehow.
        '''
        _aid = ct.c_uint32(automaton_id)
        _trapstate = c_side_state_type(trapstate_id)
        _had_effect = ct.c_bool()

        mtbdd = mtbdd_wrapper.amaya_complete_mtbdd_with_trapstate(mtbdd, _aid, _trapstate, ct.byref(_had_effect))
        return (mtbdd, _had_effect)

    @staticmethod
    def set_debugging(debug_on: bool):
        '''Enables debug output of the C side.'''
        _debug_on = ct.c_bool(debug_on)
        mtbdd_wrapper.amaya_set_debugging(_debug_on)

    def get_state_post_with_some_symbol(self, state: int) -> List[Tuple[int, Tuple[Union[int, str], ...]]]:
        if state not in self.mtbdds:
            return []
        mtbdd = self.mtbdds[state]
        return self.get_state_post_with_some_symbol_from_its_mtbdd(mtbdd, self.alphabet_variables)

    @staticmethod
    def get_state_post_with_some_symbol_from_its_mtbdd(mtbdd: ct.c_ulong,
                                                       variables: List[int]) -> List[Tuple[int, Tuple[Union[int, str], ...]]]:
        '''Retrieves the state post set including an examplatory symbol from its mtbdd.'''
        _variables = (ct.c_uint32 * len(variables))(*variables)
        _variable_cnt = ct.c_uint32(len(variables))

        _out_transition_symbols = ct.POINTER(ct.c_uint8)()
        _out_state_cnt = ct.c_uint32()

        _out_states = mtbdd_wrapper.amaya_get_state_post_with_some_transition(
            mtbdd,
            _variables,
            _variable_cnt,
            ct.byref(_out_transition_symbols),
            ct.byref(_out_state_cnt),
        )

        state_transition_symbol_pairs = []
        next_transition_symbol_bit_i = 0
        for i in range(_out_state_cnt.value):
            state = _out_states[i]

            transition_symbol = []
            for bit_i in range(len(variables)):
                transition_symbol.append(_out_transition_symbols[next_transition_symbol_bit_i])
                next_transition_symbol_bit_i += 1
            state_transition_symbol_pairs.append((state, tuple(transition_symbol)))

        mtbdd_wrapper.amaya_do_free(_out_states)
        return state_transition_symbol_pairs

    @staticmethod
    def remove_states_from_mtbdd_transitions(mtbdds: List[ct.c_ulong], removed_states: Iterable[int]) -> List[ct.c_ulong]:
        '''Removes the specified states from given transition mtbdds.
        Returns:
            The list of transition mtbdds without the removed states, in the same order as given.
        '''

        _mtbdds = (ct.c_ulong * len(mtbdds))(*mtbdds)
        _mtbdds_cnt = ct.c_uint32(len(mtbdds))
        _removed_states = (c_side_state_type * len(removed_states))(*removed_states)
        _removed_states_cnt = ct.c_uint32(len(removed_states))

        _patched_mtbdds = mtbdd_wrapper.amaya_remove_states_from_transitions(ct.cast(_mtbdds, ct.POINTER(ct.c_ulong)),
                                                                             _mtbdds_cnt,
                                                                             ct.cast(_removed_states, ct.POINTER(c_side_state_type)),
                                                                             _removed_states_cnt)
        patched_mtbdds: List[ct.c_ulong] = list()
        for i in range(len(mtbdds)):
            patched_mtbdds.append(_patched_mtbdds[i])

        mtbdd_wrapper.amaya_do_free(_patched_mtbdds)

        return patched_mtbdds

    def remove_states(self, removed_states: Iterable[int]):
        # It is worth processing only those mtbdds that will be left after the
        # removal.
        transition_origins_after_removal = list(set(self.mtbdds.keys()) - set(removed_states))

        transitions_mtbdds = []
        for transition_origin in transition_origins_after_removal:
            transitions_mtbdds.append(self.mtbdds[transition_origin])

        patched_mtbdds = MTBDDTransitionFn.remove_states_from_mtbdd_transitions(transitions_mtbdds, removed_states)

        new_mtbdds: Dict[int, ct.c_ulong] = {}
        for state, patched_mtbdd in zip(transition_origins_after_removal, patched_mtbdds):
            if patched_mtbdd == mtbdd_false:
                continue
            new_mtbdds[state] = patched_mtbdd
        self.mtbdds = new_mtbdds

    def change_automaton_ids_for_leaves(self, new_id: int):
        mtbdd_roots_arr = (ct.c_ulong * len(self.mtbdds))()
        for i, mtbdd in enumerate(self.mtbdds.values()):
            mtbdd_roots_arr[i] = mtbdd
        root_cnt = ct.c_uint32(len(self.mtbdds))
        mtbdd_wrapper.amaya_mtbdd_change_automaton_id_for_leaves(
            ct.cast(mtbdd_roots_arr, ct.POINTER(ct.c_ulong)),
            root_cnt,
            ct.c_uint32(new_id)
        )

    def complete_transitions_with_trapstate(self, trapstate: int) -> bool:
        '''Complete every stored transition mtbdd with the given trapstate, so that the
        transitions have a destination for every origin state (and any alphabet symbol).'''
        completed_mtbdds = {}
        # Cummulative information about whether a trapstate was somewhere added
        was_trapstate_added = False
        for origin, mtbdd in self.mtbdds.items():
            completed_mtbdd, had_effect = self.complete_mtbdd_with_trapstate(mtbdd, self.automaton_id, trapstate)
            was_trapstate_added = was_trapstate_added or had_effect
            completed_mtbdds[origin] = completed_mtbdd
        self.mtbdds = completed_mtbdds
        return was_trapstate_added


if __name__ == '__main__':
    from automatons import LSBF_Alphabet, MTBDD_NFA, AutomatonType
    alphabet = LSBF_Alphabet.from_variable_names([1, 2, 3])
    nfa = MTBDD_NFA(alphabet, AutomatonType.NFA)
    tfn = MTBDDTransitionFn(alphabet, 1)

    zeta0 = (0, 0, 1)
    # zeta1 = (1, 0, 0)

    # TODO: Move this to a test file (pad closure)
    nfa.update_transition_fn(0, zeta0, 1)
    # tfn.insert_transition(0, zeta1, 1)

    # tfn.insert_transition(1, zeta1, 2)
    # tfn.insert_transition(1, zeta0, 3)

    # tfn.insert_transition(2, zeta1, 3)

    # final_states = [3]
    # initial_states = [0]

    # Initialstate, final states
    # tfn.do_pad_closure(initial_states, final_states)
    # tfn.insert_transition(0, (0, 0, 1), 1)
    # tfn.insert_transition(0, (0, 0, 1), 2)

    # tfn.insert_transition(1, (0, 0, 1), 1)
    # tfn.insert_transition(1, (0, 0, 1), 3)

    # MTBDDTransitionFn.get_mtbdd_leaves(tfn.mtbdds[0])

    # print(list(tfn.iter_transitions(0, [1, 2, 3])))
