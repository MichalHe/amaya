from __future__ import annotations
import ctypes as ct
from typing import (
    Any,
    Callable,
    Dict,
    Generator,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
    TYPE_CHECKING,
    Union,
)
from collections import defaultdict
import enum
import itertools
import functools
import pathlib
import os
import sys

from amaya import logger
from amaya.alphabet import LSBF_Alphabet, LSBF_AlphabetSymbol
from amaya.automatons import AutomatonType
from amaya.relations_structures import Congruence, ModuloTerm, Relation

if TYPE_CHECKING:
    from amaya.mtbdd_automatons import MTBDD_NFA


amaya_root_path = pathlib.Path(__file__).parent.absolute()
mtbdd_wrapper = ct.CDLL(os.path.join(amaya_root_path, 'amaya-mtbdd.so'))
mtbdd_wrapper.init_machinery()

c_side_state_type = ct.c_int64


class Serialized_NFA(ct.Structure):
    """Entire MTBDD-NFA serialized to be passed to C side."""
    _fields_ = [
        ('states', ct.POINTER(c_side_state_type)),
        ('state_count', ct.c_uint64),
        ('initial_states', ct.POINTER(c_side_state_type)),
        ('initial_state_count', ct.c_uint64),
        ('final_states', ct.POINTER(c_side_state_type)),
        ('final_state_count', ct.c_uint64),
        ('mtbdds', ct.POINTER(ct.c_ulong)),
        ('vars', ct.POINTER(ct.c_uint64)),
        ('var_count', ct.c_uint64),
    ]


def deserialize_nfa(serialized_nfa: Serialized_NFA, alphabet: LSBF_Alphabet) -> MTBDD_NFA:
    from amaya.mtbdd_automatons import MTBDD_NFA

    nfa = MTBDD_NFA(
        states={serialized_nfa.states[i] for i in range(serialized_nfa.state_count)},
        initial_states={serialized_nfa.initial_states[i] for i in range(serialized_nfa.initial_state_count)},
        final_states={
            serialized_nfa.final_states[i] for i in range(serialized_nfa.final_state_count)
        },
        used_variables=sorted(serialized_nfa.vars[i] for i in range(serialized_nfa.var_count)),
        alphabet=alphabet,
        state_semantics=None  # type: ignore @TODO
    )

    for i in range(serialized_nfa.state_count):
        state = serialized_nfa.states[i]
        mtbdd = serialized_nfa.mtbdds[i]
        nfa.transition_fn.mtbdds[state] = mtbdd

    return nfa


def free_serialized_nfa(serialized_nfa):
    mtbdd_wrapper.amaya_do_free(serialized_nfa.contents.states)
    mtbdd_wrapper.amaya_do_free(serialized_nfa.contents.initial_states)
    mtbdd_wrapper.amaya_do_free(serialized_nfa.contents.final_states)
    mtbdd_wrapper.amaya_do_free(serialized_nfa.contents.vars)
    mtbdd_wrapper.amaya_do_free(serialized_nfa)


def serialize_nfa(nfa: MTBDD_NFA) -> Serialized_NFA:
    logger.debug('Serializing nfa (var_count=%d, vars=%s)', len(nfa.used_variables), nfa.used_variables)
    _states = tuple(nfa.states)
    _mtbdds = tuple(nfa.transition_fn.mtbdds.get(s, mtbdd_false) for s in _states)
    mtbdds = (ct.c_ulong * len(nfa.states))(*_mtbdds)

    serialized_nfa = Serialized_NFA(
        states=(c_side_state_type * len(nfa.states))(*_states),
        state_count=len(nfa.states),
        initial_states=(c_side_state_type * len(nfa.initial_states))(*tuple(nfa.initial_states)),
        initial_state_count=len(nfa.initial_states),
        final_states=(c_side_state_type * len(nfa.final_states))(*tuple(nfa.final_states)),
        final_state_count=len(nfa.final_states),
        mtbdds=mtbdds,
        vars=(ct.c_uint64 * len(nfa.used_variables))(*nfa.used_variables),
        var_count=ct.c_uint64(len(nfa.used_variables))
    )
    return serialized_nfa


class Serialized_Atom(ct.Structure):
    _fields_ = [
        ('type', ct.c_uint64),
        ('coefs', ct.POINTER(ct.c_int64)),
        ('coef_cnt', ct.c_uint64),
        ('modulus', ct.c_int64),
    ]


class Serialized_Quantified_Atom_Conjunction(ct.Structure):
    _fields_ = [
        ('atoms', ct.POINTER(Serialized_Atom)),
        ('atom_cnt', ct.c_uint64),
        ('initial_state', ct.POINTER(ct.c_int64)),
        ('vars', ct.POINTER(ct.c_uint64)),
        ('var_cnt', ct.c_uint64),
        ('quantified_vars', ct.POINTER(ct.c_uint64)),
        ('quantified_var_cnt', ct.c_uint64),
    ]


class Serialized_Atom_Type(enum.IntEnum):
    INEQ = 1,
    EQ = 2,
    CONGRUENCE = 3


mtbdd_wrapper.amaya_mtbdd_build_single_terminal.argtypes = (
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
    ct.POINTER(ct.c_ulong),         # MTBDD roots
    ct.c_uint32,                    # root_count
    ct.POINTER(c_side_state_type),  # Mappings [old_name1, new_name1, ...]
    ct.c_uint32,                    # Mapping size
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
)
mtbdd_wrapper.amaya_unite_mtbdds.restype = ct.c_ulong

mtbdd_wrapper.amaya_mtbdd_get_state_post.argtypes = (
    ct.c_ulong,  # MTBDD m
    ct.POINTER(ct.c_uint32),  # MTBDD result array size
)
mtbdd_wrapper.amaya_mtbdd_get_state_post.restype = ct.POINTER(c_side_state_type)

mtbdd_wrapper.amaya_mtbdd_get_transitions.argtypes = (
    ct.c_ulong,                                     # MTBDD root
    ct.POINTER(ct.c_uint32),                        # Array with variables.
    ct.c_uint32,                                    # Size of array with variables
    ct.POINTER(ct.c_uint32),                        # OUT, number of transitions
    ct.POINTER(ct.POINTER(c_side_state_type)),      # OUT Pointer to array containing destinations states
    ct.POINTER(ct.POINTER(ct.c_uint32)),            # OUT Pointer to array containing sizes of serialized destinations states
)
mtbdd_wrapper.amaya_mtbdd_get_transitions.restype = ct.POINTER(ct.c_uint8)

mtbdd_wrapper.amaya_set_debugging.argtypes = (ct.c_bool, )

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

mtbdd_wrapper.amaya_mtbdd_ref.argtypes = (
    ct.c_ulong,
)

mtbdd_wrapper.amaya_mtbdd_deref.argtypes = (
    ct.c_ulong,
)

mtbdd_wrapper.amaya_sylvan_gc.argtypes = ()

mtbdd_wrapper.amaya_get_states_in_mtbdd_leaves.argtypes = (
    ct.POINTER(ct.c_ulong),   # Array of MTBBDs
    ct.c_uint32,              # The number of passed MTBDDs
    ct.POINTER(ct.c_uint32),  # The size of returned array with states
)
mtbdd_wrapper.amaya_get_states_in_mtbdd_leaves.restype = ct.POINTER(ct.c_int64)  # States

mtbdd_wrapper.amaya_sylvan_clear_cache.argtypes = ()
mtbdd_wrapper.amaya_sylvan_clear_cache.restype = None

mtbdd_wrapper.amaya_minimize_hopcroft.argtypes = (ct.POINTER(Serialized_NFA), )
mtbdd_wrapper.amaya_minimize_hopcroft.restype = ct.POINTER(Serialized_NFA)

mtbdd_wrapper.amaya_compute_nfa_intersection.argtypes = (ct.POINTER(Serialized_NFA), ct.POINTER(Serialized_NFA))
mtbdd_wrapper.amaya_compute_nfa_intersection.restype = ct.POINTER(Serialized_NFA)

mtbdd_wrapper.amaya_determinize.argtypes = (ct.POINTER(Serialized_NFA), )
mtbdd_wrapper.amaya_determinize.restype = ct.POINTER(Serialized_NFA)

mtbdd_wrapper.amaya_construct_dfa_for_atom_conjunction.argtypes = (ct.POINTER(Serialized_Quantified_Atom_Conjunction),)
mtbdd_wrapper.amaya_construct_dfa_for_atom_conjunction.restype = ct.POINTER(Serialized_NFA)

mtbdd_wrapper.amaya_perform_pad_closure.argtypes = (ct.POINTER(Serialized_NFA), )
mtbdd_wrapper.amaya_perform_pad_closure.restype = ct.POINTER(Serialized_NFA)

# TODO: fix the shared lib - this symbol is not available ct.c_ulong.in_dll(mtbdd_wrapper, 'w_mtbdd_false')
mtbdd_false = ct.c_ulong(0)

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
    def __init__(self, alphabet_variables: List[int]):
        self.mtbdds: Dict[Any, MTBDD] = {}
        self.post_cache = dict()
        self.is_post_cache_valid = False
        self.alphabet_variables = alphabet_variables

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
            ct.cast(cube, ct.POINTER(ct.c_uint8)),      # Transition symbols, 2d array
            ct.c_uint32(1),                             # Transitions symbols count
            cube_size,                                  # Variables count
            ct.cast(dest_state, ct.POINTER(c_side_state_type)),  # Set of the terminal states
            ct.c_uint32(1),                             # Destination set size
        )

        mtbdd_wrapper.amaya_mtbdd_ref(mtbdd_new)
        resulting_mtbdd = mtbdd_wrapper.amaya_unite_mtbdds(mtbdd_new, current_mtbdd)

        # Perform referece counting updates
        # Keep only the newly created mtbdd, drop the sigle-terminal one and
        # the old transition mtbdd
        self.inc_mtbdd_ref(resulting_mtbdd)
        # self.dec_mtbdd_ref_unsafe(mtbdd_new)
        self.dec_mtbdd_ref(current_mtbdd)

        self.mtbdds[source] = resulting_mtbdd

    @staticmethod
    def write_mtbdd_dot_to_file(m, filename):
        """Write the dot representation of given MTBDD m to the file."""
        output_f = open(filename, 'w')
        fd = output_f.fileno()

        MTBDDTransitionFn.write_mtbdd_dot_to_fd(m, fd)

        output_f.close()  # The C side does not close the file descriptor

    @staticmethod
    def write_mtbdd_dot_to_fd(mtbdd: MTBDD, fd: int):
        mtbdd_wrapper.amaya_print_dot(mtbdd, fd)

    @staticmethod
    def convert_symbol_to_mtbdd_cube(symbol: Symbol):
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

        return MTBDDTransitionFn.call_get_transition_target(mtbdd, symbol)

    @staticmethod
    def call_get_transition_target(mtbdd: ct.c_ulong,
                                   symbol: Tuple[Union[str, int], ...]) -> Set[int]:
        '''Performs a call to the C side retrieving the set of states that are reachable
        in given mtbdd via the provided symbol'''

        cs, c = MTBDDTransitionFn.convert_symbol_to_mtbdd_cube(symbol)
        result_size = ct.c_uint32(0)
        result = mtbdd_wrapper.amaya_mtbdd_get_transition_target(
            mtbdd,
            ct.cast(c, ct.POINTER(ct.c_uint8)),     # Cube
            cs,                                     # Cube size
            ct.byref(result_size)
        )

        dest_ = []
        for i in range(int(result_size.value)):
            dest_.append(result[i])

        mtbdd_wrapper.amaya_do_free(result)
        return set(dest_)

    def rename_states(self, mappings: Dict[int, int]):
        """
        Renames all states referenced within stored mtbdds using the provided
        mapping.

        Requires all states present in the leaf sets of the MTBDDs to be present
        in this mapping, otherwise assertion in the C++ side will cause
        termination.

        :param mappings: A dictionary mapping old states to its new names.
        """
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

        logger.debug('Performing call to C backend for renaming.')
        renamed_mtbdds = mtbdd_wrapper.amaya_mtbdd_rename_states(
            ct.cast(mtbdd_roots, ct.POINTER(ct.c_ulong)),
            root_cnt,
            mapping_ptr,
            mapping_size
        )
        logger.debug('Done.')

        # @Note(codeboy): The renamed mtbdds do already have their refs
        # increased to 1, so there is not need to manually increase the
        # refcount

        # We've received an array of new mtbdds (they have renamed states in
        # the sets inside the leaves). Now we need to reacreate the transition
        # function which returns a transition MTBDD for every state to contain
        # the renamed states (origins)
        new_mtbdds = dict()
        for i, state_old_mtbdd_pair in enumerate(self.mtbdds.items()):
            state, old_mtbdd = state_old_mtbdd_pair
            new_mtbdds[mappings[state]] = renamed_mtbdds[i]
            # self.dec_mtbdd_ref(old_mtbdd)  # The old ones are not used anymore
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
            self.inc_mtbdd_ref_unsafe(new_mtbdd)
            self.dec_mtbdd_ref(mtbdd)
            self.mtbdds[state] = new_mtbdd

    @staticmethod
    def call_get_mtbdd_leaves(mtbdd: MTBDD,
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

    def get_union_mtbdd_for_states(self, states: List[int]) -> MTBDD:
        resulting_mtbdd = mtbdd_false
        for state in states:
            if state not in self.mtbdds:
                continue
            mtbdd = self.mtbdds[state]
            new_resulting_mtbdd = mtbdd_wrapper.amaya_unite_mtbdds(mtbdd, resulting_mtbdd)

            # The union algorithm works iteratively, adding a single MTBDD to the union mtbdd computed so far.
            # The old intermediate MTBDD has to has its reference counter decrememented, so it gets GC'd,
            # as it is only temporary and the new one has to be incremented to ensure it lives long enough
            # for the next iteration. The call do dec_mtbdd_ref will not decrement ref count of mtbdd_false
            # which is passed in in the first iteration. If we are computing a union of only one mtbdd, the result
            # would be the same mtbdd with ref count = 2, which is OK, since the mtbdd is referenced by the old
            # automaton and the new union one.
            MTBDDTransitionFn.inc_mtbdd_ref_unsafe(new_resulting_mtbdd)
            MTBDDTransitionFn.dec_mtbdd_ref(resulting_mtbdd)
            resulting_mtbdd = new_resulting_mtbdd

        if resulting_mtbdd == mtbdd_false:
            return None
        return resulting_mtbdd

    def get_state_post(self, state: int) -> List[int]:
        mtbdd = self.mtbdds.get(state, None)
        if mtbdd is None:
            return []
        return MTBDDTransitionFn.call_get_state_post(mtbdd)

    @staticmethod
    def call_get_state_post(mtbdd: ct.c_ulong) -> List[int]:
        '''Performs call to the C side, retrieving all states that are somehow reachable
        from the state that has the outgoing transitions encoded in given MTBDD.'''
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
        work_set = set(work_queue)
        logger.debug('Building adjacency matrix for the automaton.')
        while work_queue:
            logger.debug(f'Build adjacency matrix: The number of states remaining in the work queue: {len(work_queue)}')
            state = work_queue.pop(-1)
            work_set.remove(state)

            state_post = self.get_state_post(state)
            if not state_post:
                # state is terminal
                continue
            morph_map[state] = set(state_post)
            for new_state in state_post:
                # Check whether the state is not scheduled/processed already
                if new_state not in work_set and new_state not in morph_map:
                    work_queue.append(new_state)
                    work_set.add(new_state)

        return morph_map

    @staticmethod
    def reverse_adjacency_matrix(adjacency_matrix: Dict[int, Set[int]]) -> Dict[int, Set[int]]:
        reversed_adjacency_matrix: Dict[int, Set[int]] = defaultdict(set)
        for origin_state in adjacency_matrix:
            for destination_state in adjacency_matrix[origin_state]:
                reversed_adjacency_matrix[destination_state].add(origin_state)
        return reversed_adjacency_matrix

    @staticmethod
    def do_pad_closure(nfa: MTBDD_NFA) -> MTBDD_NFA:
        serialized_nfa = serialize_nfa(nfa)
        serialized_result = mtbdd_wrapper.amaya_perform_pad_closure(serialized_nfa)
        result = deserialize_nfa(serialized_result.contents, nfa.alphabet)
        free_serialized_nfa(serialized_result)
        return result

    def iter_single_state(self,
                          state: int,
                          variables: Optional[List[int]] = None
                          ) -> Generator[Tuple[int, LSBF_AlphabetSymbol, int], None, None]:
        """
        Iterate over all transitions from the given state.

        The transitions are yielded in their compressed form, meaning that the don't care bits have the value `*`.

        :param state: State from which should the yielded transitions originate.
        :param variables: Alphabet variables onto which the transition symbols will be projected.
                          If None supplied, the symbols contain bits for all alphabet variables.
        :returns: Generates the transition tuples (state, symbol, dest_state) where state is the same as the supplied
                  parameter.
        """
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

    @staticmethod
    def union_of(mtfn0: MTBDDTransitionFn, mtfn1: MTBDDTransitionFn) -> MTBDDTransitionFn:
        '''Creates a new MTBDD transition function that contains transitions
        from both transition functions.

        Since a new MTBDDTransitionFn is created all refs for the contained mtbdds
        are incremented.
        '''

        assert mtfn0.alphabet_variables == mtfn1.alphabet_variables, \
            'MTBBDs require to have the same set of variables.'

        resulting_mtbdds: Dict[int, MTBDD] = dict()
        resulting_mtbdds.update(mtfn0.mtbdds)
        for s1, m1 in mtfn1.mtbdds.items():
            assert s1 not in resulting_mtbdds, \
                f'The union should be calculated on states that have been renamed first. {s1} in {resulting_mtbdds}'
            resulting_mtbdds[s1] = m1

        union_tfn = MTBDDTransitionFn(mtfn0.alphabet_variables)
        union_tfn.mtbdds = resulting_mtbdds

        # Perform the refs increment
        for mtbdd in union_tfn.mtbdds.values():
            mtbdd_wrapper.amaya_mtbdd_ref(mtbdd)

        return union_tfn

    @staticmethod
    def set_debugging(debug_on: bool):
        '''Enables debug output of the C side.'''
        _debug_on = ct.c_bool(debug_on)
        mtbdd_wrapper.amaya_set_debugging(_debug_on)

    def get_state_post_with_some_symbol(self, state: int) -> List[Tuple[int, LSBF_AlphabetSymbol]]:
        if state not in self.mtbdds:
            return []
        mtbdd = self.mtbdds[state]
        return self.get_state_post_with_some_symbol_from_its_mtbdd(mtbdd, self.alphabet_variables)

    @staticmethod
    def get_state_post_with_some_symbol_from_its_mtbdd(mtbdd: ct.c_ulong,
                                                       variables: List[int]) -> List[Tuple[int, LSBF_AlphabetSymbol]]:
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
        """
        Removes the specified states from given transition mtbdds.

        :returns:  The list of transition mtbdds without the removed states, in the same order as given.
        """

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

        # The mtbdds created in remove_states_from_mtbdd_transitions come with
        # their reference incremented, no need to protect them here.
        patched_mtbdds = MTBDDTransitionFn.remove_states_from_mtbdd_transitions(transitions_mtbdds, removed_states)

        new_mtbdds: Dict[int, ct.c_ulong] = {}
        for state, patched_mtbdd in zip(transition_origins_after_removal, patched_mtbdds):
            if patched_mtbdd == mtbdd_false:
                continue
            self.inc_mtbdd_ref_unsafe(patched_mtbdd)  # The old mtbdd sould be discarded
            new_mtbdds[state] = patched_mtbdd

        for removed_state in set(removed_states):
            if removed_state in self.mtbdds:
                self.dec_mtbdd_ref_unsafe(self.mtbdds[removed_state])
                del self.mtbdds[removed_state]

        self.mtbdds = new_mtbdds

    def complete_transitions_with_trapstate(self, trapstate: int) -> bool:
        '''Complete every stored transition mtbdd with the given trapstate, so that the
        transitions have a destination for every origin state (and any alphabet symbol).'''
        completed_mtbdds = {}
        # Cummulative information about whether a trapstate was somewhere added
        was_trapstate_added = False
        for origin, mtbdd in self.mtbdds.items():
            completed_mtbdd, had_effect = self.complete_mtbdd_with_trapstate(mtbdd, trapstate)
            mtbdd_wrapper.amaya_mtbdd_ref(completed_mtbdd)
            was_trapstate_added = was_trapstate_added or had_effect
            completed_mtbdds[origin] = completed_mtbdd

        # Drop the references to all old mtbdds, keep only the
        # completed/patched ones
        for old_mtbdd in self.mtbdds.values():
            mtbdd_wrapper.amaya_mtbdd_deref(old_mtbdd)

        self.mtbdds = completed_mtbdds
        return was_trapstate_added

    def __del__(self):
        # Release all mtbdds stored
        for state, mtbdd in self.mtbdds.items():
            self.dec_mtbdd_ref(mtbdd)

    @staticmethod
    def inc_mtbdd_ref(dd: int):
        if dd != mtbdd_false:
            mtbdd_wrapper.amaya_mtbdd_ref(dd)

    @staticmethod
    def dec_mtbdd_ref(dd: int):
        if dd != mtbdd_false:
            mtbdd_wrapper.amaya_mtbdd_deref(dd)

    @staticmethod
    def inc_mtbdd_ref_unsafe(dd: int):
        mtbdd_wrapper.amaya_mtbdd_ref(dd)

    @staticmethod
    def dec_mtbdd_ref_unsafe(dd: int):
        mtbdd_wrapper.amaya_mtbdd_deref(dd)

    @staticmethod
    def call_sylvan_gc():
        mtbdd_wrapper.amaya_sylvan_gc()

    @staticmethod
    def participate_in_gc():
        mtbdd_wrapper.amaya_sylvan_try_performing_gc()

    @staticmethod
    def call_clear_cachce():
        mtbdd_wrapper.amaya_sylvan_clear_cache()

    @staticmethod
    def get_states_in_mtbdd_leaves(mtbdds: List[int]) -> List[int]:
        """
        Calls the C side to retrieve a list of states that are present in the
        leaves of given MTBDDs.

        :param mtbdds: MTBDDs whose leaves will be searched for states.
        :returns: The list of unique states present in the leaves of given MTBBDs.

        MTBDD wrapper.
        """

        _mtbdds = (ct.c_ulong * len(mtbdds))(*mtbdds)
        _mtbdd_cnt = ct.c_uint32(len(mtbdds))

        # Output parameters of the calls
        _out_state_cnt = ct.c_uint32()

        _out_states = mtbdd_wrapper.amaya_get_states_in_mtbdd_leaves(
            _mtbdds,
            _mtbdd_cnt,
            ct.byref(_out_state_cnt)
        )

        states_in_leaves = []

        for i in range(_out_state_cnt.value):
            states_in_leaves.append(_out_states[i])

    @staticmethod
    def compute_nfa_intersection(left: MTBDD_NFA, right: MTBDD_NFA) -> MTBDD_NFA:
        """Compute the intersection of two automata with transitions represented by MTBDDs."""
        left_serialized = serialize_nfa(left)
        right_serialized = serialize_nfa(right)
        serialized_result_ptr = mtbdd_wrapper.amaya_compute_nfa_intersection(left_serialized, right_serialized);
        serialized_result = serialized_result_ptr.contents
        intersection = deserialize_nfa(serialized_result, left.alphabet)
        free_serialized_nfa(serialized_result_ptr)
        return intersection

    @staticmethod
    def minimize_hopcroft(dfa: MTBDD_NFA) -> MTBDD_NFA:
        """Call to the MTBDD backend to minimize the given DFA"""
        from amaya.mtbdd_automatons import MTBDD_NFA  # We have to import it here to avoid circular imports
        logger.info('[MTBDD Hopcroft minimization] Entering minimization routine - serializing data.')

        serialized_dfa = serialize_nfa(dfa)
        logger.info('[MTBDD Hopcroft minimization] Serialisation done.')
        logger.info('[MTBDD Hopcroft minimization] Minimizing.')
        minimized_serialized_dfa_ptr = mtbdd_wrapper.amaya_minimize_hopcroft(serialized_dfa)
        logger.info('[MTBDD Hopcroft minimization] Done.')
        minimized_serialized_dfa = minimized_serialized_dfa_ptr.contents

        minimized_dfa = deserialize_nfa(minimized_serialized_dfa, dfa.alphabet)
        mtbdd_wrapper.amaya_do_free(minimized_serialized_dfa_ptr)

        logger.info('[MTBDD Hopcroft minimization] Exiting minimization routine')
        return minimized_dfa

    @staticmethod
    def construct_dfa_for_atom_conjunction(conjunction: List[Atom], quantified_vars: List[str], alphabet: LSBF_Alphabet, var_name_to_id: Callable[[str], int]) -> MTBDD_NFA:
        serialized_atoms = (Serialized_Atom * len(conjunction))()
        atom_type_map = {
            '=': Serialized_Atom_Type.EQ,
            '<=': Serialized_Atom_Type.INEQ,
        }

        all_vars = set()
        linear_atoms: List[Relation] = []
        congruences: List[Congruence] = []
        for atom in conjunction:
            if isinstance(atom, Congruence):
                congruences.append(atom)
                all_vars.update(atom.vars)
            else:
                linear_atoms.append(atom)
                all_vars.update(atom.variable_names)

        solver_var_ids = sorted(var_name_to_id(var) for var in all_vars)
        var_id_to_local_track = dict((var_id, i) for i, var_id in enumerate(solver_var_ids))

        atom_idx = 0
        for atom in linear_atoms:
            atom_type = atom_type_map[atom.predicate_symbol]

            dense_coefs: List[int] = [0] * len(all_vars)
            for i, var in enumerate(atom.variable_names):
                var_id = var_name_to_id(var)
                local_track = var_id_to_local_track[var_id]
                dense_coefs[local_track] = atom.variable_coefficients[i]
            coefs = (ct.c_int64 * len(all_vars))(*dense_coefs)

            serialized_atoms[atom_idx] = Serialized_Atom(type=atom_type,
                                                         coefs=coefs,
                                                         coef_cnt=len(all_vars),
                                                         modulus=0)
            atom_idx += 1

        for atom in congruences:
            dense_coefs: List[int] = [0] * len(all_vars)
            for i, var in enumerate(atom.vars):
                var_id = var_name_to_id(var)
                local_track = var_id_to_local_track[var_id]
                dense_coefs[local_track] = atom.coefs[i]
            coefs = (ct.c_int64 * len(all_vars))(*dense_coefs)

            serialized_atoms[atom_idx] = Serialized_Atom(type=Serialized_Atom_Type.CONGRUENCE,
                                                         coefs=coefs,
                                                         coef_cnt=len(all_vars),
                                                         modulus=atom.modulus)
            atom_idx += 1

        initial_state_nums = [a.absolute_part for a in linear_atoms] + [a.rhs for a in congruences]
        initial_state = (ct.c_int64 * len(conjunction))(*tuple(initial_state_nums))

        # Construct an array with variable IDs as the solver recognizes them
        var_ids = (ct.c_uint64 * len(solver_var_ids))()
        for i, var in enumerate(solver_var_ids):
            var_ids[i] = var

        serialized_quantified_vars = (ct.c_uint64 * len(quantified_vars))()
        for i, var in enumerate(sorted(quantified_vars)):
            var_id = var_name_to_id(var)
            serialized_quantified_vars[i] = var_id_to_local_track[var_id]

        serialized_conjunction = Serialized_Quantified_Atom_Conjunction(
            atoms=serialized_atoms,
            atom_cnt=len(conjunction),
            initial_state=initial_state,
            vars=var_ids,
            var_cnt=len(all_vars),
            quantified_vars=serialized_quantified_vars,
            quantified_var_cnt=len(quantified_vars)
        )

        logger.info('Lazy constructing automaton for conjunction: %s', linear_atoms + congruences)
        logger.info('Variables to IDs: %s', var_id_to_local_track)

        result_ptr = mtbdd_wrapper.amaya_construct_dfa_for_atom_conjunction(serialized_conjunction)
        nfa = deserialize_nfa(result_ptr.contents, alphabet)
        nfa.automaton_type = AutomatonType.DFA
        free_serialized_nfa(result_ptr)

        return nfa

    @staticmethod
    def determinize(nfa: MTBDD_NFA) -> MTBDD_NFA:
        serialized_dfa = serialize_nfa(nfa)
        result_ptr = mtbdd_wrapper.amaya_determinize(serialized_dfa)
        dfa = deserialize_nfa(result_ptr.contents, nfa.alphabet)
        free_serialized_nfa(result_ptr)
        dfa.automaton_type = AutomatonType.DFA
        return dfa
