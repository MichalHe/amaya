# Design: A Fixpoint Optimization Pipeline for Formula Preprocessing

Status: design proposal (not yet implemented), revised after a review against the code
Scope: replaces the body of `amaya.parse.optimize_formula_structure`
New module: `amaya/preprocessing/pipeline.py` (+ `amaya/preprocessing/structural_id.py`)
Implementation plan: `OPTIMIZATION_PIPELINE_PLAN.md` (order, files, done-when criteria)

> **Revision note.** §1's analysis was verified line-by-line against `parse.py`, `config.py`,
> `run-amaya.py` and the pass modules and holds up. The mechanism in §4–§6 needed corrections;
> the substantive ones, in rough order of severity, are:
> 1. The fingerprint was specified as the root id from a *fresh* id table — a small counter value
>    that collides for nearly every pair of formulae of similar size (§4.1).
> 2. The fingerprint inherited `connective_child_dedup`'s `frozenset` child key, under which
>    `dedup-connective-children` cannot ever appear productive and its output is discarded on
>    every run (§4.1).
> 3. The `idempotent` descriptor field defaulted to *not* re-running a productive pass against its
>    own output, which collapses the 9× CER / 2× model-reasoning / 3× unconstrained-vars
>    repetitions to one invocation each — the exact optimisations P1 exists to recover. Replaced
>    by `self_triggering`, defaulting to re-run (§5.1).
> 4. The pipeline returned the smallest formula it ever saw in *all* cases, which systematically
>    discards `miniscope` and `light-sat` — the two passes deliberately allowed to grow the AST
>    (§6.4).
> 5. `run_count` was incremented after the growth-guard `continue`, so a repeatedly-discarded
>    heavy pass never reached `max_runs` (§6.3).
> 6. Assorted smaller ones: `pending_facts` was dead state, `best_score` was typed `int` against a
>    tuple-valued `score`, `max_rounds`/`max_pass_applications` were two names for one knob, the
>    `_id` invariant story overstates a field nothing reads, `-O` flag gating for
>    `flatten-connectives` and `unconstrained-vars` was wrong, and §5.2's note about
>    `Asserted_Model_Properties` misdescribed what `parse.py` does.

---

## 1. Analysis of the current mechanism

### 1.1 Where optimisation happens

All formula-level optimisations are applied in exactly one place:

```
amaya/parse.py:157   optimize_formula_structure(astp: ASTp_Node, var_table) -> ASTp_Node
```

It is called from two sites — `perform_whole_evaluation_on_source_text` (`parse.py:412`, the
normal solving path) and `run-amaya.py:839` (the `convert` subcommand). It runs *after*
`preprocessing.preprocess_ast`, which does the non-optional lowering work (let expansion, ITE
rewriting, `forall`→`exists`, `=>` expansion, double-negation removal, atom condensation into
`Relation`/`Congruence` leaves, variable disambiguation). So the split is:

* `preprocess_ast` — **mandatory, run-once lowering**. Operates on the raw list-based `Raw_AST`.
* `optimize_formula_structure` — **optional, semantics-preserving rewriting**. Operates on the
  typed, immutable-ish `ASTp_Node` algebra (`AST_Connective`, `AST_Negation`, `AST_Quantifier`,
  `Relation`, `Congruence`, `Var`, `BoolLiteral`).

This design concerns only the second stage.

### 1.2 The current shape of the second stage

`optimize_formula_structure` is a **flat, hard-coded, straight-line sequence of `if
solver_config.optimizations.<flag>:` blocks**. Each block calls one top-level pass function that
takes the whole tree and returns a whole new tree. Every pass is a full recursive traversal of the
formula. Passes live in:

| Module | Passes |
|---|---|
| `preprocessing/unbound_vars.py` (2731 lines) | `simplify_bounded_atoms`, `simplify_unbounded_equations`, `simplify_congruences_on_unbounded_existential_vars`, `push_negations_towards_atoms`, `detect_conflics_on_isomorphic_fragments`, `convert_and_or_trees_to_dnf_if_talking_about_similar_atoms`, `prune_conjunctions_false_due_to_parent_context`, `optimize_bottom_quantifiers`, `linearize_congruences`, `inline_bool_var_definitions`, `remove_vars_with_no_consequences_on_the_model` |
| `preprocessing/theory_reasoning.py` | `simplify_formula_using_model_properties`, `scan_variable_use`, `remove_atoms_satisfied_by_unconstrained_vars` |
| `preprocessing/antiprenexing.py` | `miniscope_quantifiers` |
| `preprocessing/conditional_equality_resolution.py` | `resolve_conditional_equalities`, `fill_referenced_vars` |
| `preprocessing/connective_child_dedup.py` | `remove_duplicit_connective_children` |
| `preprocessing/__init__.py` | `flatten_bool_nary_connectives` |

Enablement is per-pass via `OptimizationsConfig` boolean fields (`amaya/config.py:39`), wired to
the `-O/--optimize` and `-N/--no-optimize` CLI flags through the `opt_to_config_field` table
(`run-amaya.py:186`). **Every optimisation defaults to `False` except `do_interval_analysis` and
`do_gcd_divide`.** There is no notion of an optimisation *level*; the benchmark harness selects
sets of `-O` flags explicitly.

### 1.3 Concrete problems with the current mechanism

**(P1) Fixpoints are hand-unrolled.** The clearest symptom is `parse.py:241-262`: conditional
equality resolution is written out **nine times**, interleaved with `flatten_bool_nary_connectives`
and one `miniscope_quantifiers` call, because each round of CER exposes new opportunities for the
next. Similarly `simplify_formula_using_model_properties` is called twice in a row (`:213-214`),
again twice more later (`:238-239`), `remove_atoms_satisfied_by_unconstrained_vars` three times
(`:218-220`), and `remove_vars_with_no_consequences_on_the_model` twice (`:231-232`). These
magic repetition counts are simultaneously **too many** (most formulae reach a fixpoint after one
or two rounds and the rest of the calls are pure traversal cost) and **too few** (a formula that
needs a tenth CER round silently does not get it).

**(P2) `do_interval_reasonining_twice` is a config flag for what should be a loop.**
`parse.py:207` exists solely because quantifier elimination performed by later passes can expose
new interval conflicts. That is a *dependency between passes*, encoded as a user-visible boolean.

**(P3) Stale analysis results.** `parse.py:216-220` scans variable uses **once**
(`scan_variable_use`) and then runs `remove_atoms_satisfied_by_unconstrained_vars` three times
against that same `Variable_Use_Info`. After the first call the formula has changed, so uses two
and three consult a stale map. This is at best a missed opportunity and at worst a correctness
hazard as the pass grows.

**(P4) The order is a frozen guess.** The sequence encodes real dependencies (e.g. CER needs
`fill_referenced_vars` first; `push_negations_towards_atoms` and the DNF pass want flattened
n-ary connectives) but they are implicit. Adding a pass means guessing where in the 110-line
`if`-ladder it belongs, and nothing detects that the guess was wrong.

**(P5) Enabling a pass costs a traversal even when it does nothing.** There is no
change-detection, so a pass that finds nothing to do on a 100k-node formula still pays a full
traversal — and every downstream pass pays another one, even though the formula is bit-identical
to what the previous pass already processed.

**(P6) No cost control.** `convert_and_or_trees_to_dnf_if_talking_about_similar_atoms` can blow
the formula up (DNF), `detect_conflics_on_isomorphic_fragments` is quadratic in the children of a
conjunction with an isomorphism check inside, and interval analysis is a full context-carrying
traversal. Nothing measures whether a pass paid for itself, and nothing stops a pass from making
the formula worse.

**(P7) Invariant management is manual and lossy.** Three separate structural annotations are
carried on nodes and each is maintained by hand:
* `referenced_vars` (on every `ASTp_Node_Base`) — required accurate by miniscoping, CER, and the
  quantifier optimisations. `fill_referenced_vars`
  (`preprocessing/conditional_equality_resolution.py:92`) exists to repair it, and is called
  exactly once, defensively, before CER. Note that its docstring currently describes it as a
  helper for *hand-built test trees*; parse.py's use of it is already outside that contract, and
  this design promotes it to a real invariant-repair pass (see §5.5).
* `_id` (on `AST_Connective`/`AST_Negation`/`AST_Quantifier`/atoms) — structural identity assigned
  by `connective_child_dedup`. **Nothing outside `connective_child_dedup` reads `_id` today**
  (`grep -rn '\._id' amaya/` finds no other consumer), so a stale `_id` is currently harmless; it
  is a latent hazard for future passes, not a present bug. This design therefore does *not* treat
  `_id` freshness as an invariant to be scheduled for — see §5.5.
* `variable_bounds` (on `AST_Connective`) — cached interval information. Written by
  `prune_conjunctions_false_due_to_parent_context` (`unbound_vars.py:1438`) and propagated by
  node-rebuilding helpers, but **never read back** anywhere in the tree today. Unlike the other
  two it is *not* `compare=False`, so it does participate in `==`; the pipeline never uses `==`,
  so this does not matter here.

### 1.4 Properties of the AST that the new design can rely on

* Nodes are dataclasses with `referenced_vars` marked `compare=False` and `_id` marked
  `compare=False`, so `==` on two trees is a **structural** comparison that ignores the
  annotations. Useful, but O(n) and order-*sensitive*.
* `connective_child_dedup` already computes a canonical, **order-insensitive** structural key per
  node (`Node_Id_Table`, keys insensitive to the order of a connective's children and of an atom's
  terms) in a single bottom-up pass. This is *nearly* the fingerprint a fixpoint loop needs — but
  its keying is fused with the dedup rewrite and is set-based rather than multiset-based, so it
  cannot be used directly. See §4.1.
* `amaya/debruijn.py:encode_formula` computes an even stronger key — canonical *modulo bound
  variable renaming* (α-equivalence), used by the automaton CSE cache. Stronger than needed here
  and slightly more expensive, but available.
* Passes are overwhelmingly **functional**: `f(ast) -> ast`, rebuilding nodes rather than mutating.
  The exceptions are `fill_referenced_vars` (mutates `referenced_vars` in place) and
  `remove_duplicit_connective_children` (writes `_id` into atoms in place while rebuilding the
  inner nodes). Both are idempotent annotation repairs. Because passes share unmodified subtrees
  between their input and output, an in-place annotation write is visible from every tree that
  still holds the node — see §5.5.

---

## 2. Design goals

1. **Run to fixpoint.** Keep applying enabled optimisations until the formula stops changing —
   delete all hand-unrolled repetitions and the `do_interval_reasonining_twice` flag.
2. **Do not pay for passes that cannot fire.** A pass is re-run only when something has changed
   that it could plausibly exploit.
3. **Cheap passes often, expensive passes rarely.** Normalisation is nearly free and enables
   everything else; DNF conversion is exponential in the worst case and must be rationed.
4. **Terminate, always, deterministically.** Cycles (pass A undoes pass B) and pathological growth
   must be detected and stopped, with a well-defined result.
5. **Never return a worse formula than the input.** The pipeline keeps the best formula it saw.
6. **Zero change to individual pass signatures** in the first implementation step, so the
   migration is mechanical and low-risk.
7. **Observability.** Per-pass invocation count, productive-run count, time and size delta, so the
   tier assignments below can be re-tuned from benchmark data instead of intuition.

---

## 3. Architecture overview

```
                        ┌─────────────────────────────────────────┐
   ASTp_Node  ────────► │        Optimization_Pipeline            │ ────► ASTp_Node
   (+ var_table)        │                                         │       (+ Pipeline_Report)
                        │  ┌───────────────────────────────────┐  │
                        │  │ Pass_Registry: Pass_Descriptor[]  │  │
                        │  └───────────────────────────────────┘  │
                        │                  │                       │
                        │                  ▼                       │
                        │  ┌───────────────────────────────────┐  │
                        │  │ Worklist scheduler                │  │
                        │  │  - tiers (cadence)                │  │
                        │  │  - produces/consumes trigger graph│  │
                        │  │  - budgets & growth guard         │  │
                        │  └───────────────────────────────────┘  │
                        │                  │                       │
                        │                  ▼                       │
                        │  ┌───────────────────────────────────┐  │
                        │  │ Fingerprint (structural_id)       │  │
                        │  │  - change detection               │  │
                        │  │  - cycle detection                │  │
                        │  │  - result memoisation             │  │
                        │  └───────────────────────────────────┘  │
                        └─────────────────────────────────────────┘
```

The pipeline is a **worklist over passes**, not a fixed sequence. A pass sits in the worklist when
some fact it consumes may have been produced since it last ran. The loop terminates when the
worklist is empty (true fixpoint) or a budget is exhausted.

---

## 4. Change detection: structural fingerprints

### 4.1 New module `amaya/preprocessing/structural_id.py`

What can be shared with `connective_child_dedup` is only the *keying vocabulary* — `Node_Key`,
the id table, `_make_linear_terms_key` and `_make_atom_key`. Its `_assign_ids` traversal cannot be
reused as-is: it **fuses** id assignment with the dedup rewrite (it drops duplicate children, and
collapses a single-child connective into that child or into `BoolLiteral(True)` for `EQUIV`), so
the ids it produces describe the *rewritten* tree, not the input. The pipeline needs a separate,
purely observational traversal:

```python
Node_Key = Tuple

@dataclass
class Structural_Id_Table:
    """Assigns a stable integer id to every distinct (sub)formula seen so far."""
    key_to_id: Dict[Node_Key, int] = field(default_factory=dict)
    next_id: int = 0
    def get_id(self, key: Node_Key) -> int: ...

def compute_structural_id(root: ASTp_Node, table: Structural_Id_Table) -> Tuple[int, int]:
    """
    Bottom-up hash-consing of the tree. Returns `(id_of_root, node_count)`. Never mutates the
    tree it is measuring.

    Keys are insensitive to (a) the order of a connective's children and (b) the order of an
    atom's terms. They are NOT insensitive to bound-variable renaming (see 4.3).

    A connective's key uses the *sorted tuple* (multiset) of its child ids, NOT a frozenset —
    see the warning below.
    """
```

**Two mandatory deviations from `connective_child_dedup`'s keying:**

1. **Multiset, not set, of child ids.** `_assign_ids` keys a connective by
   `('connective', type, frozenset(child_ids))`, which is correct *there* because it has already
   dropped the duplicates. A fingerprint built on a frozenset would give `(and A B A)` and
   `(and A B)` the same key — so `dedup-connective-children` would fingerprint its own output as
   *identical to its input*, be recorded "unproductive", and have its result thrown away by the
   scheduler on every single run. Use `tuple(sorted(child_ids))`.
2. **No single-child collapse.** For the same reason: an observational fingerprint must describe
   the tree it was handed, not a normalised form of it, or the passes that perform exactly that
   normalisation become invisible to change detection.

**The fingerprint of a formula is the root id obtained from a `Structural_Id_Table` that lives for
the whole pipeline run.** This must not be a fresh table per call: ids are handed out by a counter
in traversal order, so with a fresh table almost every formula with *k* distinct subformulae gets
root id *k−1*. Two structurally different formulae of similar shape would collide constantly, the
"unproductive" branch would fire on productive passes, and optimisation results would be silently
discarded. With one persistent table the guarantee is exact: **id equality ⟺ structural equality**,
for every pair of (sub)formulae seen anywhere in the run.

(The persistent table also makes the ids usable as the `seen_fingerprints` keys of §6.4 without
further hashing. Its memory is bounded by the total number of distinct subformulae the pipeline
ever constructs; if that becomes a concern on very large inputs, replace the counter with a
64-bit hash of the key tuple and accept the collision probability, keeping the same interface.)

Cost: one O(n) traversal with dictionary lookups — the same order of cost as the cheapest pass,
and far less than any of the analysis passes. `node_count` is accumulated in the same traversal,
so §6.5's scoring is free.

### 4.2 Why order-insensitive

A pass that merely reorders the children of a conjunction has not changed the formula in any way
that matters to any other pass. Treating a reordering as "changed" would let two passes with
different preferred orders spin against each other forever. Note that `reorder_conjunctions`
(the one deliberate reordering optimisation) is applied at *automaton construction* time in
`parse.py`, not in this pipeline, so nothing is lost.

### 4.3 Why not α-equivalence (`debruijn.encode_formula`)

`encode_formula` would also identify `(exists y. x <= y)` with `(exists z. x <= z)`. That is
strictly more precise, but: (a) it is keyed by `id(node)` and assumes the tree stays alive, which
is awkward when the tree is being replaced every round; (b) it carries a `var_table` dependency;
(c) passes here do not rename bound variables gratuitously, so the extra precision buys almost
nothing. Use the cheaper key; if benchmarking later shows spurious "changed" verdicts caused by
renaming, `Structural_Id_Table` can be swapped for the De Bruijn encoder behind the same interface.

### 4.4 Fingerprint reuse

The fingerprint computed after pass *P* is the fingerprint *before* pass *Q* — compute it once per
pass application, not twice. The scheduler threads a single `current_fingerprint` through the loop.

---

## 5. Pass descriptors

### 5.1 The descriptor

```python
class Pass_Tier(IntEnum):
    NORMALIZE = 0   # re-run after every productive pass; ~free
    CORE      = 1   # re-run every round it is triggered
    HEAVY     = 2   # rationed: at most `max_runs` times per pipeline
    FINALIZE  = 3   # run once, after the fixpoint loop has ended

@dataclass(frozen=True)
class Pass_Descriptor:
    name: str
    """Stable identifier, used in reports, in the `-O` mapping and in tests."""

    config_flag: str | None
    """Attribute on `OptimizationsConfig` gating this pass; None = unconditional."""

    run: Callable[[ASTp_Node, Pass_Context], ASTp_Node]
    """The pass itself, adapted to the uniform signature (see 5.2)."""

    tier: Pass_Tier

    consumes: frozenset[str]
    """Facts whose (re)appearance makes this pass worth re-running."""

    produces: frozenset[str]
    """Facts this pass may create when it fires."""

    max_runs: int | None = None
    """Hard cap on invocations per pipeline run. None = unlimited (bounded by the fixpoint)."""

    growth_factor_limit: float | None = None
    """If the pass increases the node count by more than this factor, its result is discarded."""

    requires_referenced_vars: bool = False
    """Scheduler runs `fill_referenced_vars` first if the annotation may be stale."""

    self_triggering: bool = True
    """If True, a productive run of this pass re-enqueues the pass itself: `f(f(x))` may differ
       from `f(x)`, so the pass must be driven to its own fixpoint. Default True — see below."""
```

**On `self_triggering` (this replaces an earlier `idempotent` flag, which had it backwards).**
The flag has to default to *re-run*, not to *skip*. Two distinct properties were being conflated:

* "running `f` on a formula `f` has already left unchanged does nothing" — trivially true for
  every functional pass here, and already enforced by the fingerprint memo of §6.3; it needs no
  descriptor field.
* "`f(f(x)) == f(x)`" — **false for most of the interesting passes.** The nine consecutive
  `resolve_conditional_equalities` calls at `parse.py:244-261` exist precisely because each round
  exposes work for the next; the same holds for the doubled `simplify_formula_using_model_properties`,
  the tripled `remove_atoms_satisfied_by_unconstrained_vars` and the doubled
  `remove_vars_with_no_consequences_on_the_model`.

A descriptor field defaulting to "don't re-run a pass against its own output" would collapse all
of those to a single invocation and lose exactly the optimisations P1 says the pipeline exists to
recover. Defaulting to self-triggering is also free of risk: if a pass really is idempotent, its
second run is unproductive, the fingerprint is unchanged, nothing is re-enqueued, and the cost is
one traversal — the same traversal today's code pays unconditionally. Set
`self_triggering=False` only for a pass measured to be genuinely run-once (§9), and note that
`max_runs` already provides a hard stop for the tier-2 passes.

`Pass_Context` carries the immutable side inputs (`var_table`, `solver_config`) plus a place for
passes that need scratch state (see 5.3), so that the uniform `run` signature holds for every pass.

### 5.2 Adapting the existing passes

Adapters are one-liners; no pass body is touched.

```python
def _pass_simplify_bounded_atoms(ast, ctx):
    result = var_bounds_lib.simplify_bounded_atoms(ast)
    return ast if result is None else result       # signature is Optional; None never observed

def _pass_congruences_on_unbound(ast, ctx):
    return var_bounds_lib.simplify_congruences_on_unbounded_existential_vars(ast, ctx.var_table)

def _pass_infinite_domain(ast, ctx):
    return var_bounds_lib.remove_vars_with_no_consequences_on_the_model(ast, ctx.var_table)

def _pass_model_properties(ast, ctx):
    # `Asserted_Model_Properties` is a stateful accumulator, fresh per invocation here.
    return simplify_formula_using_model_properties(ast, Asserted_Model_Properties())

def _pass_unconstrained_vars(ast, ctx):
    # Fixes P3: the scan is redone on the current formula on every invocation.
    var_uses = Variable_Use_Info()
    scan_variable_use(ast, var_uses)
    return remove_atoms_satisfied_by_unconstrained_vars(ast, var_uses, desired_polarity=True)
```

Two adaptations are *not* faithful to `parse.py` and must be validated by step 4 of the migration:

* **`_pass_model_properties` does not reproduce today's accumulator sharing.** `parse.py:211-214`
  and `:236-239` each build **one** `Asserted_Model_Properties` and thread it through **two**
  consecutive calls; the accumulator carries cross-call state (`vars_eliminated_via_alias` in
  particular is a `set` that a traversal fills and the binding quantifier is supposed to consume).
  A fresh instance per invocation is the *safer* choice — an accumulator whose stacks are left
  unbalanced by a previous traversal is exactly the kind of thing that produces wrong answers —
  but it is a behaviour change, not a mechanical port. Verify on the corpus that fresh-per-run
  loses nothing; if it does, the descriptor needs a `Pass_Context` scratch slot so a single
  accumulator can be threaded through consecutive invocations of the same pass.
* **`_pass_simplify_bounded_atoms` swallows `None`.** `parse.py:160` `cast`s the `Optional` away
  and would propagate a `None` downstream (i.e. crash). Treating `None` as "unchanged" is the
  right call, but say so rather than implying parity.

### 5.3 Fact vocabulary (the `produces` / `consumes` tags)

The tags are deliberately coarse — a handful of *kinds of opportunity*, not a fine-grained
dependency calculus. Over-approximating a trigger costs one wasted traversal; under-approximating
it loses an optimisation, so when in doubt, add the tag.

| Tag | Meaning — "the formula now contains …" |
|---|---|
| `nary-shape` | connectives whose arity/nesting changed (an AND may now sit directly under an AND) |
| `bool-literal` | a freshly introduced `BoolLiteral` (annihilator/identity folding is now possible) |
| `duplicate-children` | a connective may now have structurally equal children |
| `negation-shape` | a `NOT` was introduced or moved (pushing negations may now progress) |
| `atom-rewritten` | some `Relation`/`Congruence` was replaced by a different atom |
| `bounds-tightened` | a new or strengthened bound on some variable is asserted somewhere |
| `var-eliminated` | a quantified variable disappeared (frees up every var-indexed analysis) |
| `quantifier-shape` | a quantifier was moved, split, merged or removed |
| `equality-exposed` | a new equality atom, or an equality moved to a position where it constrains more |
| `subtree-removed` | some subtree was deleted (any global analysis may now conclude more) |

Every pass implicitly also produces `subtree-removed` if its output has fewer nodes than its
input; the scheduler adds that tag automatically from the node-count delta, so descriptors need
not declare it.

### 5.4 The registry

Tiers below are the *initial* assignment, derived from (a) each pass's asymptotic behaviour, (b)
how many times the current code hand-unrolls it, and (c) whether it can grow the formula. §9
describes how to re-tune them from measurements.

#### Tier 0 — NORMALIZE (cheap, enabling, re-run after every productive pass)

| Pass | Existing function | consumes | produces |
|---|---|---|---|
| `flatten-connectives` | `flatten_bool_nary_connectives` | `nary-shape`, `subtree-removed` | `nary-shape`, `duplicate-children` |
| `stomp-negations` | `push_negations_towards_atoms` | `negation-shape`, `nary-shape` | `nary-shape`, `atom-rewritten`, `negation-shape` |
| `dedup-connective-children` | `remove_duplicit_connective_children` | `duplicate-children`, `nary-shape` | `nary-shape`, `subtree-removed` |

Rationale: all three are single linear traversals with no analysis, and every other pass in the
pipeline works better on a flattened, negation-normalised, duplicate-free tree. This is the answer
to "which optimisations are called frequently": **these three, and only these three, are candidates
after every single productive step.** (`dedup-connective-children` also writes `_id`, but since
nothing outside that module reads `_id` — see P7 — that is a side effect, not a reason to schedule
it. Note too that "cheap" here means *analysis-free*, not allocation-free: it rebuilds every
connective node it visits, so a tier-0 slot for it is still a real per-round cost.)

**Gating caveat — a behaviour change hiding in the tier-0 flags.** `flatten_bool_nary_connectives`
and `remove_duplicit_connective_children` are currently invoked from *inside* other blocks
(`parse.py:245-260` interleaves flattening with CER; `:265` flattens after dedup) where they run
**regardless of the `flatten_connectives` flag**. If the registry gates `flatten-connectives` on
`solver_config.optimizations.flatten_connectives` alone, then `-O rce` without `-O
flatten-connectives` — a combination the benchmark scripts do use — stops flattening entirely and
CER, which consumes `nary-shape`, loses most of its triggers. Either register
`flatten-connectives` with `config_flag=None` (unconditional, matching what today's code
effectively does whenever rce or dedup is on), or make the `rce`/`dedup` descriptors force it on.
The former is simpler and is what §10 step 4's differential run should be built against.

#### Tier 1 — CORE (moderate cost, re-run whenever triggered)

| Pass | Existing function | consumes | produces |
|---|---|---|---|
| `var-bounds` | `simplify_bounded_atoms` | `atom-rewritten`, `bounds-tightened`, `nary-shape` | `atom-rewritten`, `bounds-tightened`, `bool-literal` |
| `interval-analysis` | `prune_conjunctions_false_due_to_parent_context` | `bounds-tightened`, `atom-rewritten`, `var-eliminated`, `nary-shape` | `bool-literal`, `atom-rewritten`, `nary-shape` |
| `model-reasoning` | `simplify_formula_using_model_properties` | `equality-exposed`, `atom-rewritten`, `bool-literal`, `nary-shape` | `bool-literal`, `atom-rewritten`, `subtree-removed` |
| `unconstrained-vars` | `scan_variable_use` + `remove_atoms_satisfied_by_unconstrained_vars` | `var-eliminated`, `subtree-removed`, `atom-rewritten` | `bool-literal`, `subtree-removed` |
| `inline-bool-definitions` | `inline_bool_var_definitions` | `equality-exposed`, `nary-shape`, `subtree-removed` | `subtree-removed`, `nary-shape`, `var-eliminated` |
| `rce` | `resolve_conditional_equalities` (requires `referenced_vars`) | `nary-shape`, `equality-exposed`, `quantifier-shape`, `var-eliminated` | `equality-exposed`, `var-eliminated`, `quantifier-shape`, `nary-shape` |

**Step 9 update (measured, partial data).** `gcd-rewrite` and `infinite-domain` were originally
tier 1 (below); a ~160-formula local sample of `benchmarks/formulae/**` (see `PROGRESS.md`) measured
their hit rate (`productive / invocations`) at 0.9% and 2.0% respectively — well under the ~5%
tier-0/1 threshold §9 sets — so both were demoted to tier 2 with `max_runs=3` and no growth limit
(neither pass grows the tree; the cap only bounds wasted traversals). They now live in the tier 2
table below. This sample was local, non-containerized, and LIA-only (no `smtcomp25-results`,
no SAT-heavy families) — treat it as a first pass, not the full step-7/9 gate.

`rce` sets `requires_referenced_vars=True`; this replaces the single defensive
`fill_referenced_vars` call at `parse.py:243`, and — crucially — makes it run again before *every*
CER invocation rather than only the first, which is what the nine hand-written repetitions
silently depend on.

This tier is where the hand-unrolling disappears: the 9× CER / 2× model-reasoning / 3×
unconstrained-vars / 2× infinite-domain repetitions all become "run until the trigger set is
empty". All four therefore need `self_triggering=True` (the default) — this is the field that
carries the repetition, not the `consumes` sets.

**Config-flag mapping (not one flag per row).** Two of these rows share a flag:
`model-reasoning` and `unconstrained-vars` are both gated by
`solver_config.optimizations.reason_about_models` — today they live in the same `if` block
(`parse.py:210-222`). Splitting them into two registry entries is right (they have different
trigger profiles) but the descriptors must both name `reason_about_models`; introducing a
separate flag for `unconstrained-vars` would change the meaning of `-O model-reasoning`.
Also note the `-O` name for `inline-bool-definitions` is misspelled in `run-amaya.py:205` as
`iniline-bool-definitions`. §7.1 promises existing invocations keep working, so the registry
must either use that spelling as the pass name or the typo must be fixed with the old spelling
kept as an accepted alias.

#### Tier 2 — HEAVY (rationed; `max_runs` and a growth guard)

> **Note on `linearize`'s growth guard.** It was 1.2 and is now none. Node count is a proxy for the
> cost of a formula, and it is a poor one for this pass: the automaton for a congruence has states on
> the order of its modulus, so replacing one of modulus 299909 by an equation removes ~300k states in
> exchange for four nodes. Under a relative guard the pass could never fire on a formula below about
> twenty nodes — exactly where a congruence dominates the cost. Its output is bounded without the
> guard: `unbound_vars._should_linearize` declines a congruence whose variable range spans more than
> four strides, and `max_runs=1` bounds the applications.

| Pass | Existing function | max_runs | growth limit | consumes | produces | measured hit rate |
|---|---|---|---|---|---|---|
| `miniscope` | `miniscope_quantifiers` | 2 | 1.5 | `quantifier-shape`, `nary-shape`, `var-eliminated` | `quantifier-shape`, `nary-shape` | 56.2% (n=217) |
| `opt-bottom-exists` | `optimize_bottom_quantifiers` | 2 | 1.2 | `quantifier-shape`, `bounds-tightened`, `atom-rewritten` | `var-eliminated`, `quantifier-shape`, `atom-rewritten`, `bool-literal` | 21.7% (n=152) |
| `gcd-rewrite` | `simplify_unbounded_equations` | 3 | — | `quantifier-shape`, `equality-exposed`, `atom-rewritten` | `atom-rewritten`, `var-eliminated`, `quantifier-shape` | 0.9% (n=551) — demoted from tier 1, see above |
| `infinite-domain` | `remove_vars_with_no_consequences_on_the_model` | 3 | — | `var-eliminated`, `quantifier-shape`, `subtree-removed` | `var-eliminated`, `quantifier-shape`, `subtree-removed` | 2.0% (n=348) — demoted from tier 1, see above |
| `minimize-congruences` | `simplify_congruences_on_unbounded_existential_vars` | 2 | 1.2 | `quantifier-shape`, `atom-rewritten` | `atom-rewritten`, `var-eliminated` | 0.0% (n=123) — not yet acted on, see note below |
| `linearize` | `linearize_congruences` | 1 | none | `atom-rewritten`, `bounds-tightened` | `atom-rewritten`, `equality-exposed` | 2.5% (n=120) |
| `iso-conflicts` | `detect_conflics_on_isomorphic_fragments` | 1 | 1.0 | `nary-shape`, `subtree-removed` | `bool-literal`, `subtree-removed` | 0.8% (n=120) — not yet acted on, see note below |
| `light-sat` | `convert_and_or_trees_to_dnf_if_talking_about_similar_atoms` | 1 | 2.0 | `nary-shape`, `atom-rewritten` | `nary-shape`, `bool-literal`, `subtree-removed` | 0.0% (n=120) — not yet acted on, see note below |

Rationale for each cap:
* `light-sat` materialises DNF — genuinely exponential in the clause count. One shot, and the
  result is thrown away if the formula more than doubles.
* `iso-conflicts` compares every pair of children of every conjunction under an isomorphism check;
  quadratic with an expensive kernel. Its output is purely subtractive (it can only replace a
  conjunction with `FALSE`), so a second run is worth very little.
* `miniscope` is a whole-tree restructuring that can duplicate a quantifier across a disjunction —
  the one Tier-2 pass that legitimately *grows* the tree. The current code already runs it twice
  (`parse.py:196` and again inside the CER block at `:257`), which is why `max_runs=2`.
* `linearize` / `minimize-congruences` / `opt-bottom-exists` are context-carrying traversals with
  per-variable monotonicity or bounds analyses.
* `gcd-rewrite` / `infinite-domain` were demoted here from tier 1 (see above); their `max_runs=3`
  is a cheap-insurance cap, not a cost control (neither pass risks blowing up the tree).

**On the three 0%-or-near-0% rows left unchanged** (`minimize-congruences`, `iso-conflicts`,
`light-sat`): the measurement sample was LIA formulae from a handful of `benchmarks/formulae/`
families (mostly `psyco`/`UltimateAutomizer`/`frobenius`), not the Boolean-structure-heavy or
congruence-heavy inputs these three passes specifically target (`light-sat` in particular exists
for AND-OR-tree-shaped formulas that this sample may simply not contain). A near-0% hit rate on an
unrepresentative sample is not evidence the pass is useless in general, so §9's tier/`self_triggering`
rules were deliberately *not* applied to them here - that needs the full corpus (plus
`smtcomp25-results` and the `smtcomp-submissions` wrappers' `-O all`) from the still-outstanding
step 7 container run.

A tier-2 pass that fires productively still re-enables the whole of tier 0 and tier 1 — its
*output* is cheap to exploit even though the pass itself was not.

#### Tier 3 — FINALIZE (once, after the loop)

| Pass | Function | Purpose |
|---|---|---|
| `finalize-flatten` | `flatten_bool_nary_connectives` | guarantee the n-ary normal form the evaluator expects |
| `finalize-dedup` | `remove_duplicit_connective_children` | final duplicate removal (and, incidentally, complete `_id`s) |
| `finalize-refvars` | `fill_referenced_vars` | guarantee accurate `referenced_vars` for the evaluator |

`finalize-flatten` and `finalize-refvars` run **unconditionally** — they establish invariants the
consumers of the formula rely on, not optimisations. `finalize-dedup` is a real optimisation and
stays gated on `deduplicate_connective_children`; it is listed here only because running it last
is free once the loop has settled, and it is *not* the mechanism that keeps `_id` fresh for other
passes (nothing else reads `_id`, P7).

### 5.5 Invariants the scheduler maintains

Exactly one annotation needs scheduler support: **`referenced_vars`**. `requires_referenced_vars`
+ the `refvars_stale` flag of §6.3 covers it, and this is a strict improvement on today's single
defensive repair at `parse.py:243` — CER's repetitions after the first currently consume whatever
`referenced_vars` the intervening rewrites happened to leave behind.

Two consequences worth stating explicitly:

* `fill_referenced_vars` **mutates nodes in place**. Passes share unmodified subtrees between the
  input and output trees, so repairing `current` can also alter nodes still reachable from `best`
  (§6.5) or from a discarded candidate. This is benign — the repair is a fixpoint and the values
  it writes are correct for any tree containing that node — but it means `best` is not an
  immutable snapshot, and any future annotation repair that is *context-dependent* (i.e. whose
  correct value depends on the ancestors of a node) cannot use this mechanism.
* Its docstring currently scopes it to test trees; promoting it to a pipeline component should
  come with a docstring update in the same commit, or the next reader will assume it is dead
  weight outside tests.

`_id` and `variable_bounds` need no scheduling: neither is read by anything today (P7).

---

## 6. The scheduler

### 6.1 State

```python
worklist: set[str]                     # pass names eligible to run
run_count: dict[str, int]
last_run_fingerprint: dict[str, int]   # pass name -> fingerprint it last ran against
current: ASTp_Node
current_fingerprint: int
current_size: int
best: ASTp_Node ; best_score: tuple[int, int]   # see 6.5
seen_fingerprints: set[int]            # for cycle detection
id_table: Structural_Id_Table          # persistent for the whole run (§4.1)
```

(The earlier draft of this section also declared `pending_facts: dict[str, set[str]]`, which no
part of the loop ever read — facts are consumed immediately at the point of production to decide
what to enqueue, and the worklist is the only carrier of pending work. It is dropped.
`last_run_fingerprint` is new and is what actually implements the "never re-run a pass against a
formula it has already processed unchanged" claim below.)

### 6.2 Ordering inside a round

Passes are drawn from the worklist by **(tier, registration index)** — tier 0 before tier 1 before
tier 2, and within a tier, the registration order of §5.4. This preserves the intent of the
current hand-written order (normalise → cheap analyses → expensive structural rewrites) while
letting the trigger graph decide *whether* each one runs.

Registration order is fixed, so **the pipeline is fully deterministic**: same input + same config
⇒ same output, same pass sequence. This matters for reproducing benchmark results and for tests.

### 6.3 The loop

```
enqueue every enabled pass                     # first round: everything runs once
current_fingerprint, current_size = measure(current, id_table)
seen_fingerprints = {current_fingerprint}
best, best_score = current, score(current)

while worklist and not budget_exhausted():
    p = pop_lowest(worklist)                        # by (tier, index)

    if last_run_fingerprint.get(p) == current_fingerprint:
        continue                                    # p has already seen exactly this formula

    if p.requires_referenced_vars and refvars_stale:
        fill_referenced_vars(current); refvars_stale = False

    candidate = p.run(current, ctx)                 # ← the only expensive step
    run_count[p] += 1                               # counted even if discarded below
    last_run_fingerprint[p] = current_fingerprint
    cand_fingerprint, cand_size = measure(candidate, id_table)   # one traversal, §4.1

    # growth guard
    if p.growth_factor_limit and cand_size > p.growth_factor_limit * current_size:
        record(p, discarded_for_growth); continue   # `current` untouched

    if cand_fingerprint == current_fingerprint:
        record(p, unproductive)                     # no facts produced, nothing re-enqueued
        continue

    # --- the pass was productive ---
    facts = p.produces | ({'subtree-removed'} if cand_size < current_size else set())
    current, current_fingerprint, current_size = candidate, cand_fingerprint, cand_size
    refvars_stale = True
    if score(current) < best_score: best, best_score = current, score(current)

    if cand_fingerprint in seen_fingerprints:
        record(cycle_detected); break               # §6.4
    seen_fingerprints.add(cand_fingerprint)

    for q in registry:
        if enabled(q) and q.tier != FINALIZE and (facts & q.consumes):
            if q is p and not q.self_triggering: continue
            if q.max_runs is not None and run_count[q] >= q.max_runs: continue
            worklist.add(q.name)

result = current if terminated_at_fixpoint else best     # §6.5
run finalizers on `result`
```

Key points, and the three defects the pseudo-code above fixes relative to the first draft:

* **`run_count` is incremented immediately after the pass runs**, before the growth guard. In the
  first draft the growth-discard path `continue`d *before* the increment, so a pass that is
  repeatedly re-enqueued and repeatedly discarded for growth never approached its `max_runs` cap
  and could burn an unbounded number of full traversals — the exact cost blow-up `max_runs` exists
  to prevent. `light-sat` and `miniscope`, the two passes most likely to trip the guard, are also
  the two most expensive to run.
* **Size and fingerprint are measured in one traversal** (`measure`), after the pass runs. The
  first draft computed `node_count` before the fingerprint and separately from it, contradicting
  §6.5's claim that scoring is free.
* **A pass is skipped outright if it has already run against this exact formula**
  (`last_run_fingerprint`). This is the mechanism behind the P5 claim; without it the claim was
  asserted but not implemented. Note it also makes self-re-enqueueing (§5.1) safe and cheap: a
  truly idempotent pass runs at most twice per formula state.
* **`current` is only replaced by a strictly-different formula**, so the "did anything change"
  question is answered exactly once per pass application, by an O(n) fingerprint.
* **Growth is rejected, not merely recorded.** A pass whose output is too large is discarded and
  the previous formula is kept — the pipeline never *accepts* a blow-up beyond the pass's declared
  budget.

### 6.4 Termination

Three exit conditions. Only the last two are *termination guarantees* — a fixpoint is the outcome
we hope for, not a bound on the run; either of the other two alone bounds it.

1. **Fixpoint** — the worklist empties. This is the normal exit.
2. **Cycle detection** — if a fingerprint repeats, some set of passes is undoing each other's
   work (e.g. miniscoping splitting a quantifier that `infinite-domain` re-merges). The loop stops
   immediately and takes `best`. Because fingerprints are order-insensitive, a benign reordering
   never triggers this. Note this is deliberately conservative: a repeated *formula* does not
   strictly imply a cycle (the worklist and `run_count` differ, so progress might still be
   possible), but stopping is always sound and the `last_run_fingerprint` memo already prevents
   the common benign case from reaching here.
3. **Budgets** — `max_pass_applications` (default 32 per 1000 formula nodes, floor 32, cap 512 —
   §7.1 names the same knob; the earlier `max_rounds` spelling was a leftover and the loop counts
   pass *applications*, not rounds) and `max_wall_time_seconds` (default 0 = unlimited). Budget
   exhaustion is logged at `WARNING` with the pass that was pending, so the benchmark harness can
   spot formulae that need a bigger budget.

**What is returned.** On a clean fixpoint the pipeline returns `current`. On an *abnormal* exit
(cycle or budget) it returns `best`. The first draft returned `best` in all three cases, which is
wrong: `best` is chosen by the §6.5 score, and that score is minimised by node count, so returning
it unconditionally would systematically undo `miniscope` and `light-sat` — the two passes whose
whole purpose is to grow the AST in exchange for a smaller automaton, and for which the growth
budgets in §5.4 exist to *permit* growth. Discarding their output after paying for it is the worst
of both worlds. `best` is a safety net for a run that ended in a state we do not trust, not a
selection rule for normal operation.

That also means the "never worse than the input" property must be stated honestly: it holds
**with respect to node count**, and only on abnormal exits. §6.5 itself concedes node count is a
poor proxy for automaton size, so this was never the strong guarantee the first draft implied.
What *is* guaranteed unconditionally is that no pass's output is accepted if it exceeds that
pass's declared growth factor.

### 6.5 The scoring function

`best` is selected by node count, with a tie-break that prefers fewer quantifiers:

```python
def score(ast) -> tuple[int, int]:      # lower is better
    return (node_count(ast), quantifier_count(ast))
```

Node count is a proxy, not a truth: automaton size is what actually matters and is not predictable
from the AST. But it is monotone in the right direction for every pass in the registry except
`miniscope` and `light-sat`, and those two have explicit growth budgets that let them exceed it
deliberately. The scoring function is a single, isolated place to refine later — e.g. weighting
quantifier alternations, or the width of congruence moduli.

The node count is computed alongside the fingerprint in the same traversal (`Structural_Id_Table`
already visits every node), so scoring is free. `best_score` is this tuple, not a bare `int` —
the first draft's loop compared `cand_size < best_score`, mixing the two representations.

Note also that the growth guard (§6.3) is *not* expressed in terms of `score`: it compares raw
node counts against `current_size`, deliberately, because it is a cost control and not a quality
judgement.

---

## 7. Configuration

### 7.1 New config section

```python
@dataclass
class OptimizationPipelineConfig:
    enabled: bool = True
    """Run passes to fixpoint. If False, fall back to the legacy straight-line sequence."""

    max_pass_applications: int | None = None
    """None = derive from formula size (32 per 1000 nodes, clamped to [32, 512])."""

    max_wall_time_seconds: float = 0.0
    """0 = no time limit."""

    tier_overrides: dict[str, int] = field(default_factory=dict)
    """Pass name -> Pass_Tier value; for experimentation without editing the registry."""

    max_runs_overrides: dict[str, int] = field(default_factory=dict)

    report: bool = False
    """Log the per-pass statistics table after the pipeline finishes."""
```

Added to `SolverConfig` as `optimization_pipeline`. The existing per-pass
`OptimizationsConfig` booleans are **unchanged** and keep their exact meaning ("is this pass in
the registry at all"), so every existing `-O` / `-N` invocation, benchmark script and
`smtcomp-submissions` entry keeps working.

### 7.2 Flags that become obsolete

* `do_interval_reasonining_twice` (`-O purge-twice`) — subsumed by the trigger graph (P2). It must
  be **ignored by the pipeline but still honoured by the legacy path**, not ignored outright: §10
  step 3 keeps the legacy body alive behind `optimization_pipeline.enabled=False` as the
  bisection escape hatch and as the reference for the step-4 differential run, and that body reads
  the flag at `parse.py:207`. Dropping the flag's effect while the legacy path exists would make
  the two paths incomparable for exactly the pass whose repetition motivated P2. Keep the CLI
  option accepted, log a deprecation note when it is passed *together with* the pipeline, and
  delete it only in step 5 when the legacy body goes.

### 7.3 New CLI

* `--opt-fixpoint` / `--no-opt-fixpoint` → `optimization_pipeline.enabled`
* `--opt-budget N` → `max_pass_applications`
* `--opt-report` → `report`

---

## 8. Reporting

```python
@dataclass
class Pass_Stats:
    name: str
    invocations: int = 0
    productive: int = 0
    discarded_for_growth: int = 0
    total_time_ns: int = 0
    nodes_removed: int = 0        # cumulative, over productive runs only

@dataclass
class Pipeline_Report:
    pass_stats: dict[str, Pass_Stats]
    rounds: int
    termination: Literal['fixpoint', 'cycle', 'budget', 'time']
    input_size: int
    output_size: int
    pass_sequence: list[str]      # for reproducing / debugging a specific run
```

Logged at `INFO` under `--opt-report`, and attached to `Evaluation_Result` so the benchmark
harness (`run-amaya.py benchmark`) can emit it as CSV columns. This is the data that turns the
tier assignments of §5.4 from a guess into a measurement.

---

## 9. Tuning the tiers from data

The initial tiering is a hypothesis. Once `Pipeline_Report` is collected over the benchmark corpus
(`benchmarks/`, `smtcomp25-results/`), each pass gets two numbers:

* **hit rate** = `productive / invocations` — how often the pass finds anything.
* **yield** = `nodes_removed / total_time_ns` — how much it removes per unit of time.

The rules are then mechanical:
* hit rate < ~5% and the pass is in tier 0/1 → demote a tier, or narrow its `consumes` set (the
  more likely cause: the trigger is over-approximated).
* hit rate > ~50% in tier 2 with acceptable time → promote to tier 1 or raise `max_runs`.
* A pass whose `productive` count is ~always 1 regardless of budget is genuinely run-once; set
  `self_triggering=False` (or `max_runs=1`) and stop paying for the re-checks. This is the only
  place `self_triggering=False` should ever be set — never as an a-priori guess (§5.1).
* A pass with a high `discarded_for_growth` count has the wrong growth limit, or should not be
  enabled for that formula family.

---

## 10. Migration plan

**Step 1 — extract the fingerprint.** Create `structural_id.py` by lifting `Node_Key`,
`Node_Id_Table` (as `Structural_Id_Table`), `_make_linear_terms_key` and `_make_atom_key` out of
`connective_child_dedup.py`, and add the new observational `compute_structural_id` traversal
there. `connective_child_dedup` keeps its own `_assign_ids` — it cannot be expressed in terms of
`compute_structural_id`, because its ids describe the deduplicated tree and use a `frozenset` of
child ids, while the fingerprint must describe the input tree and use a sorted tuple (§4.1). So
this step is a pure refactor *of the shared keying vocabulary only*; the two traversals stay
separate on purpose.
*Tests:* `tests/test_cse_cache.py` and the existing dedup tests must be unchanged and passing,
plus new unit tests asserting that (a) structurally identical trees fingerprint equal,
(b) reordered children and reordered atom terms fingerprint equal, (c) any semantic change
fingerprints differently, (d) **`(and A B A)` and `(and A B)` fingerprint differently** — the
regression test for the frozenset trap, and (e) two structurally different trees with the same
number of distinct subformulae fingerprint differently — the regression test for the fresh-table
trap.

**Step 2 — build the registry and the pipeline** in `pipeline.py`, with the adapters of §5.2. No
call site changes yet.
*Tests:* new `tests/test_optimization_pipeline.py` — fixpoint reached, cycle detection fires on a
synthetic oscillating pass pair, growth guard discards *and still charges `run_count`*, budget
exhaustion returns `best` while a clean fixpoint returns `current`, a synthetic non-idempotent
pass (one that needs *n* applications) is driven to its fixpoint, and determinism (same input
twice ⇒ identical `pass_sequence`).

**Step 3 — switch `optimize_formula_structure`** to
```python
def optimize_formula_structure(astp, var_table):
    if not solver_config.optimization_pipeline.enabled:
        return _optimize_formula_structure_legacy(astp, var_table)   # today's body, verbatim
    return Optimization_Pipeline(build_registry(solver_config), var_table).run(astp)
```
Keeping the legacy body under a flag makes every regression bisectable to "pipeline vs. pass" with
a single CLI switch, and gives the differential test of step 4 something to compare against.

**Step 4 — differential validation.** For every formula in `benchmarks/` and the SMT-COMP corpus,
run both paths under the same `-O` set and check that (a) the sat/unsat verdict is identical, and
(b) the pipeline's output formula is no larger than the legacy output.

(b) is a *sanity check, not an invariant*, and must not be turned into an assertion. Two reasons
the pipeline can legitimately emit a larger formula than the legacy sequence: `miniscope` and
`light-sat` are permitted to grow the tree within their budgets and may fire in positions the
legacy order never reaches, and the pipeline returns `current` on a clean fixpoint rather than the
smallest formula it saw (§6.4). Nor does the pipeline "strictly generalise" the legacy sequence:
the legacy order is *not* in general a schedule the worklist can produce, because a legacy call
that the trigger graph considers untriggered is simply never made. Treat a size regression as a
signal to inspect the `pass_sequence`, and gate the migration on (a) plus aggregate automaton-size
and wall-clock numbers over the corpus — automaton size being what actually matters (§6.5).

The `_pass_model_properties` accumulator change flagged in §5.2 is the highest-risk item to check
here; run the corpus with `-O model-reasoning` specifically.

**Step 5 — delete the hand-unrolling.** Remove the 9× CER block, the doubled model-reasoning
calls, the tripled unconstrained-vars calls, and `do_interval_reasonining_twice`. This is the
commit that actually shrinks `parse.py` by ~110 lines.

**Step 6 (optional, later) — passes report their own change flag.** Once the pipeline is in place,
passes can be migrated one at a time from `f(ast) -> ast` to `f(ast) -> Pass_Result(ast, changed,
facts)`, letting a pass declare precisely which facts it produced instead of the conservative
static `produces` set — and skipping the fingerprint traversal entirely when `changed is False`.
The scheduler needs no change: it can accept either signature and fall back to fingerprinting for
un-migrated passes. This is a pure optimisation of the pipeline itself and is deliberately *not*
required for correctness, which is what keeps steps 1–5 mechanical.

---

## 11. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Two passes oscillate, undoing each other's work | Cycle detection (§6.4); `max_runs` on the tier-2 restructurers; `self_triggering=False` only once measured (§9) |
| Fingerprinting cost dominates on huge formulae | It is one O(n) hash-consing pass, cheaper than any pass it guards; step 6 removes it for migrated passes |
| Fingerprint too coarse ⇒ productive passes discarded | The multiset-key and persistent-table requirements of §4.1, with the step-1 regression tests (d) and (e) |
| Stale `referenced_vars` breaks miniscoping/CER | `requires_referenced_vars` + `refvars_stale` tracking; `finalize-refvars` at exit |
| A stale `_id` from a pass that rebuilds nodes | Not a live risk: nothing outside `connective_child_dedup` reads `_id` (P7). Revisit if a pass ever starts consuming it |
| Fresh `Asserted_Model_Properties` per run differs from today's shared accumulator | Explicitly validated in step 4 under `-O model-reasoning`; fall back to a `Pass_Context` scratch slot if it regresses (§5.2) |
| Tier-0 flag gating silently disables the flattening that CER depends on | Register `flatten-connectives` unconditionally (§5.4) |
| More total traversals than today on some formulae | Budgets are configurable per run; `--opt-report` identifies the offender; the differential run in step 4 measures it |
| Behaviour change breaks an SMT-COMP submission script | `optimization_pipeline.enabled=False` restores today's behaviour byte-for-byte, provided `purge-twice` keeps its effect on that path (§7.2) |
