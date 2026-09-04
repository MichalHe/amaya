from __future__ import annotations
from typing import (
    Any,
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
import itertools

from amaya import libamaya
from amaya import logger
from amaya.alphabet import LSBF_Alphabet, LSBF_AlphabetSymbol
from amaya.automatons import AutomatonType
from amaya.relations_structures import AST_Atom, Congruence, Relation, Var

if TYPE_CHECKING:
    from amaya.mtbdd_automatons import MTBDD_NFA


Symbol = Tuple[Union[str, int], ...]


def _symbol_to_bits(symbol: Symbol) -> List[int]:
    """Convert a symbol using the solver-wide convention (0, 1 or '*' for don't care)
    into the compressed bit representation used by the C++ NFA (0, 1 or 2 for don't care)."""
    return [2 if bit == '*' else int(bit) for bit in symbol]


def _bits_matches_query(stored_bits: bytes, query: Symbol) -> bool:
    for stored_bit, query_bit in zip(stored_bits, query):
        if stored_bit == 2 or query_bit == '*':
            continue
        if int(stored_bit) != int(query_bit):
            return False
    return True


def _nfa_from_pynfa(pynfa: libamaya.PyNFA, alphabet: LSBF_Alphabet,
                    automaton_type: Optional[AutomatonType] = None) -> MTBDD_NFA:
    from amaya.mtbdd_automatons import MTBDD_NFA

    var_ids = sorted(pynfa.vars)
    nfa = MTBDD_NFA(
        states=set(pynfa.states),
        initial_states=set(pynfa.initial_states),
        final_states=set(pynfa.final_states),
        used_variables=[Var(id=var_id) for var_id in var_ids],
        alphabet=alphabet,
        state_semantics=None,  # type: ignore
    )
    if automaton_type is not None:
        nfa.automaton_type = automaton_type
    nfa.transition_fn._nfa = pynfa
    return nfa


def _snapshot_pynfa(nfa: MTBDD_NFA) -> libamaya.PyNFA:
    """
    Build an independent PyNFA reflecting `nfa`'s current states/initial_states/final_states
    (which are authoritative at the MTBDD_NFA level) together with its transitions.

    The returned object is a copy - operating on it (e.g. performing pad closure) never
    mutates `nfa` itself.
    """
    pynfa = nfa.transition_fn._nfa.clone()
    pynfa.states = nfa.states
    pynfa.initial_states = nfa.initial_states
    pynfa.final_states = nfa.final_states
    return pynfa


def _add_transition(pynfa: libamaya.PyNFA, source: int, dest: int, symbol) -> None:
    """
    Add a transition into `pynfa`, additionally registering `source`/`dest` in `pynfa.states`.

    `PyNFA.get_symbolic_transitions()` walks `pynfa.states`, not the transition map directly, so
    a `MTBDDTransitionFn`'s underlying PyNFA (which otherwise never has states explicitly added to
    it - it is used purely as a transitions container) needs source/dest states registered for
    that (and other whole-automaton) operation(s) to see the transition.
    """
    pynfa.add_state(source)
    pynfa.add_state(dest)
    pynfa.add_transition(source, dest, symbol)


class MTBDDTransitionFn():
    def __init__(self, alphabet_variables: List[int]):
        # `alphabet_variables` is nominal bookkeeping only (the full working alphabet this
        # automaton is declared over) - it is intentionally decoupled from `self._nfa.vars`,
        # which may be narrower (e.g. an automaton built for a single atom only talks about
        # that atom's own variables). It never changes after construction.
        self.alphabet_variables: List[int] = list(alphabet_variables)
        self._nfa = libamaya.PyNFA(vars=list(alphabet_variables))

    def insert_transition(self, source: Any, symbol: Symbol, dest: int):
        assert type(dest) == int
        assert type(source) == int
        _add_transition(self._nfa, source, dest, _symbol_to_bits(symbol))

    def get_transition_target(self, source, symbol: Symbol) -> Set[int]:
        '''Retrieve the set of states that lead from `source` via `symbol`.'''
        targets: Set[int] = set()
        for _origin, dest, stored_bits in self._nfa.get_symbolic_transitions_for_state(source):
            if _bits_matches_query(stored_bits, symbol):
                targets.add(dest)
        return targets

    def rename_states(self, mappings: Dict[int, int]):
        """
        Renames all states referenced within stored transitions using the provided mapping.

        Requires all states present (as either transition origin or destination) to be present
        in this mapping.

        :param mappings: A dictionary mapping old states to their new names.
        """
        new_nfa = libamaya.PyNFA(vars=self._nfa.vars)
        for origin, dest, symbol in self._nfa.get_symbolic_transitions():
            _add_transition(new_nfa, mappings[origin], mappings[dest], symbol)
        self._nfa = new_nfa

    def project_variable_away(self, variable: Var):
        """
        Project away the variable with given number from every transition stored within this
        transition function.
        """
        assert variable.id > 0, 'MTBDD variables are numbered via ints from 1 up'

        old_vars = self._nfa.vars
        var_idx = old_vars.index(variable.id)
        new_vars = old_vars[:var_idx] + old_vars[var_idx + 1:]

        new_nfa = libamaya.PyNFA(vars=new_vars)
        for origin, dest, symbol in self._nfa.get_symbolic_transitions():
            new_symbol = symbol[:var_idx] + symbol[var_idx + 1:]
            _add_transition(new_nfa, origin, dest, new_symbol)
        self._nfa = new_nfa

    def get_union_mtbdd_for_states(self, states: List[int]):
        raise NotImplementedError('get_union_mtbdd_for_states is no longer supported - it exposed raw MTBDD handles')

    def get_state_post(self, state: int) -> List[int]:
        return list(self._nfa.get_state_post(state))

    def get_state_pre(self, state: int, initial_states: Iterable[int]) -> List[int]:
        adjacency_matrix = self.build_automaton_adjacency_matrix(initial_states)
        state_pre = set()
        for s in adjacency_matrix:
            if state in adjacency_matrix[s]:
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
            state = work_queue.pop(-1)
            work_set.remove(state)

            state_post = self.get_state_post(state)
            if not state_post:
                continue
            morph_map[state] = set(state_post)
            for new_state in state_post:
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
        pynfa = _snapshot_pynfa(nfa)
        pynfa.perform_pad_closure()
        return _nfa_from_pynfa(pynfa, nfa.alphabet, nfa.automaton_type)

    @staticmethod
    def do_pad_closure_using_bit_sets(nfa: MTBDD_NFA) -> MTBDD_NFA:
        pynfa = _snapshot_pynfa(nfa)
        result_pynfa = libamaya.perform_pad_closure_using_bit_sets(pynfa)
        return _nfa_from_pynfa(result_pynfa, nfa.alphabet, nfa.automaton_type)

    def iter_single_state(self,
                          state: int,
                          variables: Optional[List[int]] = None
                          ) -> Generator[Tuple[int, LSBF_AlphabetSymbol, int], None, None]:
        """
        Iterate over all transitions from the given state.

        The transitions are yielded in their compressed form, meaning that the don't care bits
        have the value `2`.
        """
        for origin, dest, symbol in self._nfa.get_symbolic_transitions_for_state(state):
            yield (origin, tuple(symbol), dest)

    def iter_compressed(self, variables: Optional[List[int]] = None):
        for origin, dest, symbol in self._nfa.get_symbolic_transitions():
            yield (origin, tuple(symbol), dest)

    def iter(self, variables: Optional[List[int]] = None):
        '''Iterates over all transitions stored within this transition function.
        The transitions are yielded in form of (Origin, Symbol, Destination), where:
            - Origin is the origin for the transitions,
            - Symbol is **uncompressed** transition symbol e.g. (1, 0, 0) for alphabet of 3 vars,
            - Destination is a **single** destination state.
        '''
        for compact_symbol in self.iter_compressed():
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

        Note: a transition function's underlying PyNFA may talk about a variable subset that is
        narrower than the transition function's own (nominal, declared) alphabet_variables - e.g.
        an automaton freshly built for a single atom only encodes that atom's own variables. Such
        transitions are widened (missing variables become don't-care) onto the union's target
        alphabet, which is the (asserted-equal) nominal alphabet of both operands.
        '''

        assert mtfn0.alphabet_variables == mtfn1.alphabet_variables, \
            'MTBBDs require to have the same set of variables.'

        target_vars = mtfn0.alphabet_variables

        def widen(symbol, own_vars) -> List[int]:
            if list(own_vars) == list(target_vars):
                return list(symbol)
            own_pairs = iter(zip(own_vars, symbol))
            cur = next(own_pairs, None)
            widened = []
            for var in target_vars:
                if cur is not None and cur[0] == var:
                    widened.append(cur[1])
                    cur = next(own_pairs, None)
                else:
                    widened.append(2)
            return widened

        union_tfn = MTBDDTransitionFn(target_vars)
        for origin, dest, symbol in mtfn0._nfa.get_symbolic_transitions():
            _add_transition(union_tfn._nfa, origin, dest, widen(symbol, mtfn0._nfa.vars))
        for origin, dest, symbol in mtfn1._nfa.get_symbolic_transitions():
            _add_transition(union_tfn._nfa, origin, dest, widen(symbol, mtfn1._nfa.vars))

        return union_tfn

    def get_state_post_with_some_symbol(self, state: int) -> List[Tuple[int, LSBF_AlphabetSymbol]]:
        '''Retrieves the state post set including an examplatory symbol for each destination.'''
        seen_dests: Set[int] = set()
        result: List[Tuple[int, LSBF_AlphabetSymbol]] = []
        for _origin, dest, symbol in self._nfa.get_symbolic_transitions_for_state(state):
            if dest in seen_dests:
                continue
            seen_dests.add(dest)
            concrete_symbol = tuple(0 if bit == 2 else bit for bit in symbol)
            result.append((dest, concrete_symbol))
        return result

    def remove_states(self, removed_states: Iterable[int]):
        self._nfa.remove_states(set(removed_states))

    def complete_with_trap_state(self, alphabet: LSBF_Alphabet, used_variables: List[Var],
                                 states: Iterable[int], trap_state: Any = 'TRAP') -> bool:
        """
        Complete every given state with a transition to `trap_state` for any symbol not already
        covered by one of its outgoing transitions, so that every state has an outgoing transition
        for every symbol.

        Note: the MTBDD backend's own determinize() already returns a complete DFA (the underlying
        C++ NFA::determinize_nfa adds its own trapstate), so this is not on the solver's hot path -
        it exists for automata assembled directly (e.g. in tests). Implemented via enumerating all
        alphabet symbols, so it is not intended for automata with a large number of variables.
        """
        var_count = len(self.alphabet_variables)
        all_symbols = list(itertools.product((0, 1), repeat=var_count)) if var_count else [()]

        trap_state_present = False
        for state in states:
            covered: Set[Tuple[int, ...]] = set()
            for origin, dest, symbol in self._nfa.get_symbolic_transitions_for_state(state):
                for _, concrete_symbol, _ in MTBDDTransitionFn._iter_unpack_transition((origin, tuple(symbol), dest)):
                    covered.add(concrete_symbol)

            missing_symbols = [symbol for symbol in all_symbols if symbol not in covered]
            if not missing_symbols:
                continue

            if not trap_state_present:
                self._nfa.add_state(trap_state)
                self._nfa.add_universal_transition(trap_state, trap_state)
                trap_state_present = True

            for symbol in missing_symbols:
                _add_transition(self._nfa, state, trap_state, list(symbol))

        return trap_state_present

    def __del__(self):
        pass

    def copy(self) -> MTBDDTransitionFn:
        """ Construct a copy of the transition function. """
        new = MTBDDTransitionFn(self.alphabet_variables)
        new._nfa = self._nfa.clone()
        return new

    @staticmethod
    def compute_nfa_intersection(left: MTBDD_NFA, right: MTBDD_NFA) -> MTBDD_NFA:
        """Compute the intersection of two automata with transitions represented by MTBDDs."""
        left_pynfa = _snapshot_pynfa(left)
        right_pynfa = _snapshot_pynfa(right)
        result_pynfa = libamaya.compute_nfa_intersection(left_pynfa, right_pynfa)
        return _nfa_from_pynfa(result_pynfa, left.alphabet)

    @staticmethod
    def minimize_hopcroft(dfa: MTBDD_NFA) -> MTBDD_NFA:
        """Call to the MTBDD backend to minimize the given DFA"""
        pynfa = _snapshot_pynfa(dfa)
        result_pynfa = libamaya.minimize_hopcroft(pynfa)
        return _nfa_from_pynfa(result_pynfa, dfa.alphabet, AutomatonType.DFA)

    @staticmethod
    def construct_dfa_for_atom_conjunction(conjunction: List[AST_Atom], quantified_vars: List[Var], alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        atom_type_map = {
            '=': libamaya.Atom_Type.EQ,
            '<=': libamaya.Atom_Type.INEQ,
        }

        all_vars = set()
        linear_atoms: List[Relation] = []
        congruences: List[Congruence] = []
        for atom in conjunction:
            if isinstance(atom, Congruence):
                congruences.append(atom)
                all_vars.update(atom.vars)
            else:
                assert isinstance(atom, Relation)
                linear_atoms.append(atom)
                all_vars.update(atom.vars)

        solver_var_ids = sorted(var.id for var in all_vars)
        var_id_to_local_track = dict((var_id, i) for i, var_id in enumerate(solver_var_ids))

        atoms = []
        initial_state = []
        for atom in linear_atoms:
            dense_coefs: List[int] = [0] * len(all_vars)
            for i, var in enumerate(atom.vars):
                dense_coefs[var_id_to_local_track[var.id]] = atom.coefs[i]
            atoms.append((atom_type_map[atom.predicate_symbol], dense_coefs, 0))
            initial_state.append(atom.rhs)

        for atom in congruences:
            dense_coefs = [0] * len(all_vars)
            for i, var in enumerate(atom.vars):
                dense_coefs[var_id_to_local_track[var.id]] = atom.coefs[i]
            atoms.append((libamaya.Atom_Type.CONGRUENCE, dense_coefs, atom.modulus))
            initial_state.append(atom.rhs)

        quantified_local_tracks = [var_id_to_local_track[var.id] for var in sorted(quantified_vars)]

        logger.info('Lazy constructing automaton for conjunction: %s', linear_atoms + congruences)
        logger.info('Variables to IDs: %s', var_id_to_local_track)

        pynfa = libamaya.construct_dfa_for_atom_conjunction(atoms, initial_state, solver_var_ids, quantified_local_tracks)
        return _nfa_from_pynfa(pynfa, alphabet, AutomatonType.DFA)

    @staticmethod
    def determinize(nfa: MTBDD_NFA) -> MTBDD_NFA:
        pynfa = _snapshot_pynfa(nfa)
        result_pynfa = libamaya.determinize_nfa(pynfa)
        return _nfa_from_pynfa(result_pynfa, nfa.alphabet, AutomatonType.DFA)

    @staticmethod
    def construct_nfa_for_congruence(congruence: Congruence, alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        var_ids = [var.id for var in congruence.vars]
        pynfa = libamaya.construct_nfa_from_congruence(list(congruence.coefs), congruence.modulus, congruence.rhs, var_ids)
        return _nfa_from_pynfa(pynfa, alphabet)

    @staticmethod
    def construct_nfa_for_congruence_with_bounded_var(congruence: Congruence, bound_var: Var,
                                                     lower_bound: int, upper_bound: int,
                                                     alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        """
        Construct an automaton for `exists bound_var. (lower_bound <= bound_var <= upper_bound and congruence)`.

        The bound variable is projected away by the construction itself - the resulting automaton is over
        the congruence's remaining variables. See BOUNDED_CONGRUENCE.md.
        """
        var_ids = [var.id for var in congruence.vars]
        bound_var_idx = congruence.vars.index(bound_var)
        pynfa = libamaya.construct_nfa_from_congruence_with_bounded_var(
            list(congruence.coefs), congruence.modulus, congruence.rhs, bound_var_idx,
            lower_bound, upper_bound, var_ids)
        return _nfa_from_pynfa(pynfa, alphabet)

    @staticmethod
    def construct_nfa_for_ineq(ineq: Relation, alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        var_ids = [var.id for var in ineq.vars]
        pynfa = libamaya.construct_nfa_from_ineq(list(ineq.coefs), ineq.rhs, var_ids)
        return _nfa_from_pynfa(pynfa, alphabet)

    @staticmethod
    def construct_nfa_for_eq(eq: Relation, alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        var_ids = [var.id for var in eq.vars]
        pynfa = libamaya.construct_nfa_from_eq(list(eq.coefs), eq.rhs, var_ids)
        return _nfa_from_pynfa(pynfa, alphabet)

    @staticmethod
    def enable_bit_sets():
        libamaya.enable_bit_sets()
