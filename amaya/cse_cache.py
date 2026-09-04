"""
Experimental De Bruijn-keyed automaton cache (common-subexpression elimination for automaton
construction). See `DEBRUJIN_CSE.md` for the design this implements.

`Scoper` (`preprocessing/eval.py`) hands out a globally fresh `Var` id to every binder, so e.g.
`(exists ((y Int)) (<= x y))` and `(exists ((z Int)) (<= x z))` are different `ASTp_Node` trees
that construct the exact same automaton (up to renaming). This module gives every subformula a
hashable canonical key (`amaya.debruijn.encode_formula`) that is equal for alpha-equivalent
subformulae and different otherwise, and uses it to memoise the automaton built for each distinct
subformula, reusing it (with its tracks renamed onto the current occurrence's variables) instead
of rebuilding it.

**This is entirely opt-in and touches no other module's source.** The only integration point is
`amaya.parse.run_evaluation_procedure`, and even that is not edited: `run_evaluation_procedure`
is looked up by every recursive call site inside `amaya/parse.py` (`get_automaton_for_operand`,
`evaluate_using_sharding`, `perform_whole_evaluation_on_source_text`) through Python's normal
module-global lookup, so *temporarily rebinding the module attribute* `parse.run_evaluation_procedure`
to `run_evaluation_procedure_cse` (see `cse_enabled` below) is enough to route every recursive
evaluation call through the cache, without changing a single line of `parse.py`. Nothing is
patched unless a caller explicitly enters `cse_enabled()` (or calls `run_evaluation_procedure_cse`
directly), so the solver's default behavior is completely unaffected by this module merely being
importable.

**Correctness invariant.** Several code paths in `parse.py` synthesize fresh `ASTp_Node`s after
`encode_formula` has already run over the tree passed in (e.g. `reorder_conjunction_to_derive_
conflict_more_quickly`, `try_construct_bounded_congruence`, `select_children_to_lazily_evaluate`,
`split_conjunction_to_shards`). Those synthetic nodes are simply absent from the encoding table,
so they are neither looked up nor cached - a missing table entry can only cost a cache hit, it
can never cause an incorrect one. `run_evaluation_procedure_cse` relies on exactly this: on any
node it has no encoding for, it behaves identically to plain `run_evaluation_procedure`.

**Non-MTBDD backend.** `NFA` (`automatons.py`) has no notion of renaming tracks (its symbols are
positional over the whole alphabet, not narrowed per-automaton the way MTBDD tracks are), so this
module does nothing there: `run_evaluation_procedure_cse` falls straight through to the ordinary
`run_evaluation_procedure` whenever `solver_config.backend_type != BackendType.MTBDD`.

Note: this is unrelated to `connective_child_dedup`'s `_id` field, which is a structural-identity
marker used for a different purpose and is not a substitute for this encoding - see the docstring
of `amaya.debruijn` for why.
"""
from __future__ import annotations

from collections import OrderedDict
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Dict, Generator, Optional, Tuple

from amaya import libamaya, parse
from amaya.automatons import NFA
from amaya.config import BackendType, solver_config
from amaya.debruijn import Encoded_Node, encode_formula
from amaya.mtbdd_transitions import MTBDDTransitionFn
from amaya.relations_structures import ASTp_Leaf_Type_List, ASTp_Node, Var
from amaya.solver_core import EvaluationContext

# The un-patched function - captured once, at import time, before this module (or anyone else)
# has a chance to rebind `parse.run_evaluation_procedure`. This is what a cache miss falls back
# on to actually build an automaton; its recursive calls resolve `run_evaluation_procedure`
# through `parse`'s module globals at call time, so as long as `cse_enabled()` (or an equivalent
# direct rebind) is active, those recursive calls are routed through the cache too.
_original_run_evaluation_procedure = parse.run_evaluation_procedure


# ---------------------------------------------------------------------------------------------
# MTBDD_NFA.renamed_copy - added onto the class at runtime (not by editing mtbdd_automatons.py)
# ---------------------------------------------------------------------------------------------

def _renamed_copy(self, renaming: Dict[Var, Var]):
    """
    Return an independent automaton equal to `self` with its tracks renamed according to
    `renaming` (vars with no entry keep their id). `self` is left untouched.

    Deliberately does *not* go through `MTBDDTransitionFn.rename_vars`/`MTBDD_NFA.rename_vars`:
    those additionally (and incorrectly, for our purposes) remap `alphabet_variables`, which is
    documented as the automaton's nominal *global* alphabet and is asserted to be identical across
    operands by `MTBDDTransitionFn.union_of` - a renaming that is monotone on this automaton's own
    (narrow) var set is generally not monotone on the full alphabet, so remapping it would corrupt
    that invariant for every future union against a freshly built automaton. We rename only the
    underlying MTBDD (`libamaya.rename_vars`, which is itself required to be order-preserving and
    raises `ValueError` otherwise) and leave `transition_fn.alphabet_variables` alone.
    """
    from amaya.mtbdd_automatons import MTBDD_NFA

    id_renaming = {old.id: new.id for old, new in renaming.items() if old.id != new.id}
    new_pynfa = libamaya.rename_vars(self.transition_fn._nfa, id_renaming)

    new_used_variables = sorted(renaming.get(var, var) for var in self.used_variables)

    new_nfa = MTBDD_NFA(
        alphabet=self.alphabet,
        state_semantics=self.state_semantics,
        automaton_type=self.automaton_type,
        states=set(self.states),
        initial_states=set(self.initial_states),
        final_states=set(self.final_states),
        used_variables=new_used_variables,
        applied_operations_info=list(self.applied_operations_info),
    )
    # `MTBDD_NFA.__post_init__` already built a fresh, empty `transition_fn` with the correct
    # (untouched) `alphabet_variables` derived from `self.alphabet` - just swap in the renamed
    # MTBDD.
    new_nfa.transition_fn._nfa = new_pynfa
    return new_nfa


def _install_renamed_copy():
    from amaya.mtbdd_automatons import MTBDD_NFA
    if not hasattr(MTBDD_NFA, 'renamed_copy'):
        MTBDD_NFA.renamed_copy = _renamed_copy


# Adding a new method to `MTBDD_NFA` at import time is observable only to code that explicitly
# calls `.renamed_copy(...)` - nothing on the default evaluation path does, so this does not
# change the solver's default behavior; it just makes `renamed_copy` available as soon as this
# module is imported, rather than only after the first `run_evaluation_procedure_cse` call.
_install_renamed_copy()


# ---------------------------------------------------------------------------------------------
# Cache
# ---------------------------------------------------------------------------------------------

@dataclass
class Automaton_Cache:
    """
    Maps an `Encoded_Node.key` to the (signature, automaton) that was built for the first
    subformula that produced that key.

    Bounded by `max_entries` (LRU eviction, oldest-hit-first) so that caching every subformula
    of a large input does not pin every intermediate automaton in memory for the whole run.
    `min_subformula_size` is enforced by the caller (`_worth_caching`), not stored here.
    """
    max_entries: int = 4096
    pop_on_hit: bool = False
    """
    If True, a cache hit removes the entry (only the *next* occurrence of the same subformula, if
    any, benefits). If False (default), a hit copies the cached automaton and leaves the entry in
    place, so every occurrence benefits at the cost of one clone per hit. See DEBRUJIN_CSE.md.
    """

    entries: 'OrderedDict[Tuple, Tuple[Tuple[Var, ...], NFA]]' = field(default_factory=OrderedDict)
    hits: int = 0
    misses: int = 0
    evictions: int = 0

    def get(self, key: Tuple) -> Optional[Tuple[Tuple[Var, ...], NFA]]:
        entry = self.entries.get(key)
        if entry is None:
            self.misses += 1
            return None

        self.hits += 1
        if self.pop_on_hit:
            del self.entries[key]
        else:
            self.entries.move_to_end(key)
        return entry

    def put(self, key: Tuple, sig: Tuple[Var, ...], nfa: NFA) -> None:
        self.entries[key] = (sig, nfa)
        self.entries.move_to_end(key)
        while len(self.entries) > self.max_entries:
            self.entries.popitem(last=False)
            self.evictions += 1


def _worth_caching(ast: ASTp_Node) -> bool:
    """ Atoms/leaves are cheap to (re)build and are the most numerous nodes - do not cache them. """
    return not isinstance(ast, ASTp_Leaf_Type_List)


# ---------------------------------------------------------------------------------------------
# The alternative evaluation entry point
# ---------------------------------------------------------------------------------------------

def run_evaluation_procedure_cse(ast: ASTp_Node,
                                 ctx: EvaluationContext,
                                 _debug_recursion_depth: int = 0) -> NFA:
    """
    Drop-in, cache-aware replacement for `amaya.parse.run_evaluation_procedure`: same signature,
    same observable result, but subformulae whose De Bruijn-keyed encoding has already been built
    are served from `ctx.automaton_cache` (with their tracks renamed onto the current occurrence's
    variables) instead of being reconstructed.

    On the first call for a given `ctx`, lazily attaches `ctx.enc_table`/`ctx.automaton_cache` to
    it and computes the encoding for `ast`'s subtree; a later call for the same `ctx` but a
    *different* root (e.g. one shard of a sharded conjunction) extends `ctx.enc_table` rather than
    recomputing/discarding it, so distinct roots sharing one evaluation context still share a
    cache.
    """
    if solver_config.backend_type != BackendType.MTBDD:
        # Renaming tracks is an MTBDD-only trick (see module docstring) - do not attempt to cache.
        return _original_run_evaluation_procedure(ast, ctx, _debug_recursion_depth)

    _install_renamed_copy()

    enc_table: Optional[Dict[int, Encoded_Node]] = getattr(ctx, 'enc_table', None)
    if enc_table is None:
        enc_table = {}
        ctx.enc_table = enc_table

    automaton_cache: Optional[Automaton_Cache] = getattr(ctx, 'automaton_cache', None)
    if automaton_cache is None:
        automaton_cache = Automaton_Cache()
        ctx.automaton_cache = automaton_cache

    if id(ast) not in enc_table:
        encode_formula(ast, var_table=ctx.var_table, table=enc_table)

    enc = enc_table.get(id(ast))

    if enc is not None:
        hit = automaton_cache.get(enc.key)
        if hit is not None:
            cached_sig, cached_nfa = hit
            renaming = dict(zip(cached_sig, enc.sig))
            return cached_nfa.renamed_copy(renaming)

    nfa = _original_run_evaluation_procedure(ast, ctx, _debug_recursion_depth)

    if enc is not None and _worth_caching(ast):
        automaton_cache.put(enc.key, enc.sig, nfa.renamed_copy({}))

    return nfa


@contextmanager
def cse_enabled() -> Generator[None, None, None]:
    """
    Route every evaluation performed through `amaya.parse.run_evaluation_procedure` (and thus
    `perform_whole_evaluation_on_source_text`, `evaluate_using_sharding`, and every recursive call
    inside `parse.py`) through `run_evaluation_procedure_cse` for the duration of the `with` block.

    Restores the original function on exit, including if the block raises.
    """
    previous = parse.run_evaluation_procedure
    parse.run_evaluation_procedure = run_evaluation_procedure_cse
    try:
        yield
    finally:
        parse.run_evaluation_procedure = previous


def perform_whole_evaluation_on_source_text_with_cse(source_text: str, emit_introspect=None):
    """ Convenience wrapper: `perform_whole_evaluation_on_source_text` with the cache enabled. """
    with cse_enabled():
        return parse.perform_whole_evaluation_on_source_text(source_text, emit_introspect=emit_introspect)
