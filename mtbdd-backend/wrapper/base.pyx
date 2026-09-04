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
ctypedef uint32_t u32
ctypedef int64_t s64
ctypedef uint32_t BDDVAR


class Atom_Type:
    """Mirrors the C++ `Presburger_Atom_Type` enum (include/lazy.hpp)."""
    INEQ = 1
    EQ = 2
    CONGRUENCE = 3


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

    cdef struct Serialized_Atom:
        u64 type
        s64* coefs
        u64 coef_cnt
        s64 modulus

    cdef struct Serialized_Quantified_Atom_Conjunction:
        Serialized_Atom* atoms
        u64 atom_cnt
        s64* initial_state
        u64* vars
        u64 var_cnt
        u64* quantified_vars
        u64 quantified_var_cnt

    NFA c_construct_nfa_from_congruence "construct_nfa_from_congruence"(Serialized_Atom* congruence, s64 init_val, BDDSET vars, u64 var_count) except +
    NFA c_construct_nfa_from_congruence_with_bounded_var "construct_nfa_from_congruence_with_bounded_var"(Serialized_Atom* congruence, s64 rhs, u64 bound_var_idx, s64 lower_bound, s64 upper_bound, BDDSET vars, u64 var_count) except +
    NFA c_construct_nfa_from_ineq "construct_nfa_from_ineq"(Serialized_Atom* ineq, s64 init_state, BDDSET vars, u64 var_count) except +
    NFA c_construct_nfa_from_eq "construct_nfa_from_eq"(Serialized_Atom* eq, s64 init_state, BDDSET vars, u64 var_count) except +
    NFA c_construct_dfa_for_atom_conjunction "construct_dfa_for_atom_conjunction"(Serialized_Quantified_Atom_Conjunction* raw_formula) except +
    NFA c_perform_pad_closure_using_bit_sets "perform_pad_closure_using_bit_sets"(NFA& nfa) except +
    void c_amaya_enable_bit_sets "amaya_enable_bit_sets"()


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

    def clone(self):
        """Return an independent copy of this automaton (deep-copies the underlying NFA,
        including proper ref-counting of every transition MTBDD)."""
        cdef PyNFA other = PyNFA()
        del other._c_nfa
        other._c_nfa = new NFA(self._c_nfa[0])
        return other

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


def perform_pad_closure_using_bit_sets(PyNFA nfa):
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_perform_pad_closure_using_bit_sets(nfa._c_nfa[0]))
    return result


def enable_bit_sets():
    c_amaya_enable_bit_sets()


def construct_nfa_from_ineq(coefs, s64 rhs, vars):
    cdef vector[s64] c_coefs = coefs
    cdef vector[BDDVAR] c_vars = vars
    cdef Serialized_Atom atom
    atom.type = Atom_Type.INEQ
    atom.coefs = c_coefs.data()
    atom.coef_cnt = c_coefs.size()
    atom.modulus = 0

    cdef BDDSET var_set = mtbdd_set_from_array(c_vars.data(), c_vars.size())
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_construct_nfa_from_ineq(&atom, rhs, var_set, c_vars.size()))
    return result


def construct_nfa_from_eq(coefs, s64 rhs, vars):
    cdef vector[s64] c_coefs = coefs
    cdef vector[BDDVAR] c_vars = vars
    cdef Serialized_Atom atom
    atom.type = Atom_Type.EQ
    atom.coefs = c_coefs.data()
    atom.coef_cnt = c_coefs.size()
    atom.modulus = 0

    cdef BDDSET var_set = mtbdd_set_from_array(c_vars.data(), c_vars.size())
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_construct_nfa_from_eq(&atom, rhs, var_set, c_vars.size()))
    return result


def construct_nfa_from_congruence(coefs, s64 modulus, s64 rhs, vars):
    cdef vector[s64] c_coefs = coefs
    cdef vector[BDDVAR] c_vars = vars
    cdef Serialized_Atom atom
    atom.type = Atom_Type.CONGRUENCE
    atom.coefs = c_coefs.data()
    atom.coef_cnt = c_coefs.size()
    atom.modulus = modulus

    cdef BDDSET var_set = mtbdd_set_from_array(c_vars.data(), c_vars.size())
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_construct_nfa_from_congruence(&atom, rhs, var_set, c_vars.size()))
    return result


def construct_nfa_from_congruence_with_bounded_var(coefs, s64 modulus, s64 rhs, bound_var_idx,
                                                  s64 lower_bound, s64 upper_bound, vars):
    """
    Build an NFA for `exists X. (lower_bound <= X <= upper_bound  and  <coefs, vars> = rhs (mod modulus))`,
    where `X` is the variable at index `bound_var_idx`.

    `X` is projected away: the returned automaton is over the remaining tracks, i.e. `vars` with the
    `bound_var_idx`-th entry removed, and its `var_count` is `len(vars) - 1`. It generally has several
    initial states - one per distinct right-hand side produced by instantiating `X` - which all share
    a single state graph. See BOUNDED_CONGRUENCE.md.

    :param coefs: coefficients, one per entry of `vars`, in the same (ascending) order.
    :param modulus: the congruence's modulus; must be positive.
    :param rhs: the congruence's right-hand side.
    :param bound_var_idx: index into `coefs`/`vars` of the bounded variable.
    :param lower_bound, upper_bound: inclusive bounds on the bounded variable. An empty range
                                     (`lower_bound > upper_bound`) yields an automaton accepting nothing.
    """
    cdef vector[s64] c_coefs = coefs
    cdef vector[BDDVAR] c_vars = vars
    cdef u64 c_bound_var_idx

    if c_coefs.size() != c_vars.size():
        raise ValueError(f'Got {c_coefs.size()} coefficients for {c_vars.size()} variables - the counts must match.')
    if c_vars.size() < 2:
        raise ValueError('At least 2 variables are needed - one to project away, and one to be left in the automaton.')
    if not 0 <= bound_var_idx < c_vars.size():
        raise ValueError(f'bound_var_idx={bound_var_idx} is out of range for {c_vars.size()} variables.')
    if modulus <= 0:
        raise ValueError(f'The modulus must be positive, got {modulus}.')

    c_bound_var_idx = bound_var_idx

    cdef Serialized_Atom atom
    atom.type = Atom_Type.CONGRUENCE
    atom.coefs = c_coefs.data()
    atom.coef_cnt = c_coefs.size()
    atom.modulus = modulus

    cdef BDDSET var_set = mtbdd_set_from_array(c_vars.data(), c_vars.size())
    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_construct_nfa_from_congruence_with_bounded_var(
        &atom, rhs, c_bound_var_idx, lower_bound, upper_bound, var_set, c_vars.size()))
    return result


def construct_dfa_for_atom_conjunction(atoms, initial_state, vars, quantified_vars):
    """
    :param atoms: list of (atom_type: int (Atom_Type.*), coefs: list[int] of length len(vars), modulus: int)
    :param initial_state: list[int], one entry per atom
    :param vars: list[int] - the (solver-level) variable ids used by this conjunction, in track order
    :param quantified_vars: list[int] - local track indices (into `vars`) that are existentially quantified
    """
    cdef u64 atom_cnt = len(atoms)
    cdef u64 var_cnt = len(vars)

    cdef vector[s64] all_coefs
    all_coefs.resize(atom_cnt * var_cnt)

    cdef vector[Serialized_Atom] c_atoms
    c_atoms.resize(atom_cnt)

    cdef u64 i, j
    cdef s64 coef
    for i in range(atom_cnt):
        atom_type, coefs, modulus = atoms[i]
        for j in range(var_cnt):
            all_coefs[i * var_cnt + j] = coefs[j]
        c_atoms[i].type = atom_type
        c_atoms[i].coefs = all_coefs.data() + i * var_cnt
        c_atoms[i].coef_cnt = var_cnt
        c_atoms[i].modulus = modulus

    cdef vector[s64] c_initial_state = initial_state
    cdef vector[u64] c_vars = vars
    cdef vector[u64] c_quantified_vars = quantified_vars

    cdef Serialized_Quantified_Atom_Conjunction conjunction
    conjunction.atoms = c_atoms.data()
    conjunction.atom_cnt = atom_cnt
    conjunction.initial_state = c_initial_state.data()
    conjunction.vars = c_vars.data()
    conjunction.var_cnt = var_cnt
    conjunction.quantified_vars = c_quantified_vars.data()
    conjunction.quantified_var_cnt = c_quantified_vars.size()

    result = PyNFA()
    del result._c_nfa
    result._c_nfa = new NFA(c_construct_dfa_for_atom_conjunction(&conjunction))
    return result
