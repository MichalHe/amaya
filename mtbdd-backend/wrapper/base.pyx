# distutils: language = c++
"""Cython wrapper around mtbdd-backend's C++ NFA (include/base.hpp)."""

from libc.stdint cimport int64_t, uint64_t, uint32_t, uint8_t
from libcpp.vector cimport vector
from libcpp.set cimport set as cpp_set
from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.utility cimport move


ctypedef int64_t State
ctypedef uint64_t MTBDD
ctypedef uint64_t BDDSET
ctypedef uint8_t u8
ctypedef uint64_t u64
ctypedef uint32_t BDDVAR


cdef extern from "<sstream>" namespace "std":
    cdef cppclass ostream:
        pass

    cdef cppclass ostringstream(ostream):
        ostringstream() except +
        string str() except +


cdef extern from "sylvan.h" namespace "sylvan":
    MTBDD mtbdd_set_empty()
    MTBDD mtbdd_set_from_array(BDDVAR* arr, size_t length)
    void  mtbdd_set_to_array(MTBDD s, BDDVAR* arr)
    size_t mtbdd_set_count(MTBDD s)


cdef extern from "wrapper.hpp":
    void init_machinery()
    void shutdown_machinery()


cdef extern from "base.hpp":
    cdef cppclass Transition:
        State from_ "from"
        State to
        vector[u8] symbol

    cdef enum NFA_Flags:
        NFA_FLAG_DETERMINISTIC

    cdef cppclass NFA:
        cpp_set[State] states
        cpp_set[State] final_states
        cpp_set[State] initial_states
        unordered_map[State, MTBDD] transitions

        u64 flags

        BDDSET vars
        u64 var_count

        NFA() except +
        NFA(BDDSET vars, u64 var_count) except +
        NFA(NFA other) except +

        void perform_pad_closure() except +

        void add_transition(State src, State dest, u64 symbol, u64 quantified_bits_mask) except +
        void add_transition(State src, State dest, vector[u8] symbol) except +
        void add_universal_transition(State src, State dest) except +

        vector[Transition] get_symbolic_transitions_for_state(State state) except +
        vector[Transition] get_symbolic_transitions() except +
        void write_into_mata_format(ostream& output_stream) except +

        cpp_set[State] get_state_post(State state) except +

        void remove_states(cpp_set[State]& states_to_remove) except +

        void add_state_final(State state) except +
        void mark_state_final(State state) except +

    NFA c_compute_nfa_intersection "compute_nfa_intersection"(NFA& left, NFA& right) except +
    void c_remove_nonfinishing_states "remove_nonfinishing_states"(NFA& nfa) except +
    NFA c_determinize_nfa "determinize_nfa"(NFA& nfa) except +
    NFA c_minimize_hopcroft "minimize_hopcroft"(NFA& nfa) except +


cdef bint _machinery_initialized = False


def init():
    """Initialize the sylvan/lace machinery. Safe to call multiple times."""
    global _machinery_initialized
    if not _machinery_initialized:
        init_machinery()
        _machinery_initialized = True


def shutdown():
    """Tear down the sylvan/lace machinery. Do this at most once, after all
    PyNFA instances have been released."""
    global _machinery_initialized
    if _machinery_initialized:
        shutdown_machinery()
        _machinery_initialized = False


# Sylvan must be initialized before any MTBDD/BDDSET can be created, which
# happens as soon as a NFA is constructed - so make sure it happens on import.
init()


cdef class PyNFA:
    cdef NFA* _c_nfa

    def __cinit__(self, vars=None):
        cdef vector[BDDVAR] var_vec
        cdef BDDSET var_set
        cdef u64 var_count

        if vars is None:
            var_set = mtbdd_set_empty()
            var_count = 0
        else:
            var_vec = vars
            var_set = mtbdd_set_from_array(var_vec.data(), var_vec.size())
            var_count = var_vec.size()

        self._c_nfa = new NFA(var_set, var_count)

    def __dealloc__(self):
        if self._c_nfa != NULL:
            del self._c_nfa

    # --- states -----------------------------------------------------

    @property
    def states(self):
        return self._c_nfa.states

    @states.setter
    def states(self, new_states):
        self._c_nfa.states = <cpp_set[State]> new_states

    @property
    def initial_states(self):
        return self._c_nfa.initial_states

    @initial_states.setter
    def initial_states(self, new_states):
        self._c_nfa.initial_states = <cpp_set[State]> new_states

    @property
    def final_states(self):
        return self._c_nfa.final_states

    @final_states.setter
    def final_states(self, new_states):
        self._c_nfa.final_states = <cpp_set[State]> new_states

    def add_state(self, State state):
        self._c_nfa.states.insert(state)

    def add_state_initial(self, State state):
        self._c_nfa.states.insert(state)
        self._c_nfa.initial_states.insert(state)

    def add_state_final(self, State state):
        self._c_nfa.add_state_final(state)

    def mark_state_final(self, State state):
        self._c_nfa.mark_state_final(state)

    # --- symbolic alphabet -------------------------------------------

    @property
    def var_count(self):
        return self._c_nfa.var_count

    @property
    def vars(self):
        cdef vector[BDDVAR] var_vec
        var_vec.resize(mtbdd_set_count(self._c_nfa.vars))
        if var_vec.size() > 0:
            mtbdd_set_to_array(self._c_nfa.vars, var_vec.data())
        return list(var_vec)

    @property
    def is_deterministic(self):
        return bool(self._c_nfa.flags & NFA_FLAG_DETERMINISTIC)

    # --- transitions ---------------------------------------------------

    def add_transition(self, State src, State dest, symbol):
        """Add a transition src --symbol--> dest. `symbol` is an iterable of
        the automaton's variable count containing 0, 1, or 2 (don't care)."""
        cdef vector[u8] symbol_vec = symbol
        self._c_nfa.add_transition(src, dest, move(symbol_vec))

    def add_universal_transition(self, State src, State dest):
        self._c_nfa.add_universal_transition(src, dest)

    def get_state_post(self, State state):
        return self._c_nfa.get_state_post(state)

    def get_symbolic_transitions_for_state(self, State state):
        cdef vector[Transition] transitions = self._c_nfa.get_symbolic_transitions_for_state(state)
        return [
            (t.from_, t.to, bytes(t.symbol))
            for t in transitions
        ]

    def get_symbolic_transitions(self):
        cdef vector[Transition] transitions = self._c_nfa.get_symbolic_transitions()
        return [
            (t.from_, t.to, bytes(t.symbol))
            for t in transitions
        ]

    def remove_states(self, states_to_remove):
        cdef cpp_set[State] states = <cpp_set[State]> states_to_remove
        self._c_nfa.remove_states(states)

    def perform_pad_closure(self):
        self._c_nfa.perform_pad_closure()

    # --- (de)serialization / debug -------------------------------------

    def write_into_mata_format(self):
        cdef ostringstream out
        self._c_nfa.write_into_mata_format(out)
        return (<bytes>out.str()).decode('utf-8')

    def __repr__(self):
        return (
            f"PyNFA(states={set(self._c_nfa.states)}, "
            f"initial_states={set(self._c_nfa.initial_states)}, "
            f"final_states={set(self._c_nfa.final_states)}, "
            f"var_count={self._c_nfa.var_count})"
        )


def compute_nfa_intersection(PyNFA left, PyNFA right):
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_compute_nfa_intersection(left._c_nfa[0], right._c_nfa[0]))
    return result


def determinize_nfa(PyNFA nfa):
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_determinize_nfa(nfa._c_nfa[0]))
    return result


def minimize_hopcroft(PyNFA nfa):
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_minimize_hopcroft(nfa._c_nfa[0]))
    return result


def remove_nonfinishing_states(PyNFA nfa):
    c_remove_nonfinishing_states(nfa._c_nfa[0])
