"""
(EXPERIMENTAL) Propagation of modular interval bounds through a system of congruences.

The pass targets an existential block whose body is a conjunction of hard bounds and congruences of
one modulus - the shape a machine-arithmetic encoding produces, where the modulus is `2**32` and the
congruences model wraparound. Such a congruence costs an automaton on the order of its modulus, so
eliminating one is worth a great deal more than the nodes it costs.

The reasoning, on the block that motivated the pass:

    exists x13 x14 x15 x16.
        48 <= x13 <= 57                      48 <= x14 <= 57
        2**31 <= x15 <= 2**32-1              2**31 <= x16 <= 2**32-1
        x13 + 10*x15 - x16 == 48  (mod 2**32)            (C26)
        10*x1 + x14 - x15  == 48  (mod 2**32)            (C25)

`x16` occurs only in C26 and its own bounds, and its coefficient there is invertible, so C26
*determines* it: `x16 == x13 + 10*x15 - 48`. The block is satisfiable for a given `x15` exactly when
that value lands in `x16`'s window, which is a modular interval constraint on the rest of C26. `x13`
is likewise local and folds into the window, widening it by its own span. C26 and both variables
disappear, leaving

    10*x15 in [2**31 - 9, 2**32 - 1]   (mod 2**32)

`x15` is now local to C25, which determines it in turn, and substituting carries the fact onto a term
over `x1`. Nothing is approximated except where a variable that several facts mention is folded into a
constant range - see `Modular_Bound_Fact.with_variable_folded`.

**The representation avoids unions of intervals.** A fact is one interval on one linear term. That
works because substituting a determined variable into `k*v in W` multiplies the coefficients of the
*term* and leaves `W` alone: no interval is ever scaled, only shifted. Projecting several facts onto a
single term would require a union - `docs/MODULAR_BOUNDS.md` records why - so the pass emits one fact
per derivation instead.

Nothing here is wired into the solver. `derive_modular_bound_facts` is the entry point; it reports
what it derived and rewrites nothing.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

from amaya import logger
from amaya.relations_structures import (
    AST_Connective,
    AST_Quantifier,
    ASTp_Node,
    Bound_Type,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    get_hard_bound_semantics,
)


@dataclass(frozen=True)
class Modular_Interval:
    """
    An interval of values modulo some modulus, with **unreduced** endpoints.

    The endpoints are kept over the integers and may be negative or exceed the modulus; only the value
    being tested is ever reduced (`contains`). Two properties depend on that convention:

    * `measure` is meaningful, so `measure >= modulus` is the vacuity test. Reduce the endpoints first
      and a full-circle constraint becomes indistinguishable from a tight one.
    * Shifting is exact and needs no case analysis, which matters because every combination step this
      pass performs is a shift.
    """

    lower: int
    upper: int

    @property
    def measure(self) -> int:
        return self.upper - self.lower + 1

    def is_vacuous(self, modulus: int) -> bool:
        return self.measure >= modulus

    def is_empty(self) -> bool:
        return self.measure <= 0

    def shifted_by(self, lower_delta: int, upper_delta: int) -> 'Modular_Interval':
        """ The Minkowski sum with `[lower_delta, upper_delta]`; exact. """
        return Modular_Interval(self.lower + lower_delta, self.upper + upper_delta)

    def contains(self, value: int, modulus: int) -> bool:
        """ Whether `value` reduced modulo `modulus` falls inside this window. """
        if self.is_vacuous(modulus):
            return True
        reduced = value % modulus
        return any(self.lower <= reduced + offset * modulus <= self.upper for offset in (-1, 0, 1))

    def __repr__(self) -> str:
        return f'[{self.lower}, {self.upper}]'


Linear_Term = Tuple[Tuple[Var, int], ...]
""" A linear term as a tuple of `(variable, coefficient)` pairs, sorted by variable and without zeros. """


def _normalise_term(coefficient_of_var: Dict[Var, int], modulus: int) -> Linear_Term:
    """ Reduce every coefficient modulo `modulus` into `(-modulus/2, modulus/2]` and drop the zeros. """
    normalised: List[Tuple[Var, int]] = []
    for var in sorted(coefficient_of_var):
        coefficient = coefficient_of_var[var] % modulus
        if coefficient > modulus // 2:
            coefficient -= modulus
        if coefficient != 0:
            normalised.append((var, coefficient))
    return tuple(normalised)


@dataclass(frozen=True)
class Modular_Bound_Fact:
    """
    `term + constant` lies in `interval`, modulo `modulus`.

    One interval over one linear term. The pass never scales an interval - which would turn it into a
    union - so every fact stays a single interval for its whole life.
    """

    term: Linear_Term
    constant: int
    interval: Modular_Interval
    modulus: int
    derivation: Tuple[str, ...] = tuple()
    """ What produced this fact, in order, for the log and for tests. """

    @property
    def variables(self) -> FrozenSet[Var]:
        return frozenset(var for var, _ in self.term)

    def coefficient_of(self, var: Var) -> int:
        for term_var, coefficient in self.term:
            if term_var == var:
                return coefficient
        return 0

    def is_vacuous(self) -> bool:
        return self.interval.is_vacuous(self.modulus) or not self.term

    def holds_for(self, assignment: Dict[Var, int]) -> bool:
        value = self.constant + sum(coefficient * assignment[var] for var, coefficient in self.term)
        return self.interval.contains(value, self.modulus)

    def with_substitution(self, var: Var, replacement: 'Determined_Variable') -> 'Modular_Bound_Fact':
        """
        Replace `var` by the term a congruence determines it to equal.

        The coefficient `var` carries in this fact multiplies through into the replacement's
        coefficients; the interval is untouched. That is what keeps a fact a single interval - scaling
        an interval by the coefficient would produce a union.
        """
        multiplier = self.coefficient_of(var)
        if multiplier == 0:
            return self

        coefficient_of_var: Dict[Var, int] = {
            term_var: coefficient for term_var, coefficient in self.term if term_var != var
        }
        for replacement_var, replacement_coefficient in replacement.term:
            coefficient_of_var[replacement_var] = (coefficient_of_var.get(replacement_var, 0)
                                                   + multiplier * replacement_coefficient)

        return Modular_Bound_Fact(
            term=_normalise_term(coefficient_of_var, self.modulus),
            constant=self.constant + multiplier * replacement.constant,
            interval=self.interval,
            modulus=self.modulus,
            derivation=self.derivation + (f'substitute {var} from {replacement.source}',),
        )

    def with_variable_folded(self, var: Var, lower: int, upper: int) -> 'Modular_Bound_Fact':
        """
        Remove `var` by absorbing its range into the interval.

        Widens the window by the variable's span times its coefficient, so the fact loses the ability
        to say anything about `var` itself. Exact only when no other fact mentions `var`: two facts
        that fold the same variable independently may pick different values for it.
        """
        coefficient = self.coefficient_of(var)
        if coefficient == 0:
            return self

        contributions = (coefficient * lower, coefficient * upper)
        remaining = tuple((term_var, term_coefficient) for term_var, term_coefficient in self.term
                          if term_var != var)
        return Modular_Bound_Fact(
            term=remaining,
            constant=self.constant,
            interval=self.interval.shifted_by(-max(contributions), -min(contributions)),
            modulus=self.modulus,
            derivation=self.derivation + (f'fold {var} over [{lower}, {upper}]',),
        )

    def __repr__(self) -> str:
        rendered = ' '.join(f'{coefficient:+d}*{var}' for var, coefficient in self.term)
        constant = f' {self.constant:+d}' if self.constant else ''
        return f'{rendered}{constant} in {self.interval} (mod {self.modulus})'


@dataclass(frozen=True)
class Determined_Variable:
    """ A variable a congruence pins down: `var == term + constant` modulo the congruence's modulus. """

    var: Var
    term: Linear_Term
    constant: int
    source: str


def solve_congruence_for_variable(congruence: Congruence, var: Var) -> Optional[Determined_Variable]:
    """
    Solve `congruence` for `var`, or return None when its coefficient is not invertible.

    Invertibility is what makes the congruence *determine* the variable rather than merely constrain
    it. A non-invertible coefficient `c` leaves `var` known only modulo `modulus / gcd(c, modulus)`,
    which this pass does not represent.
    """
    modulus = congruence.modulus
    coefficient_of_var = dict(zip(congruence.vars, congruence.coefs))
    if var not in coefficient_of_var:
        return None

    coefficient = coefficient_of_var[var] % modulus
    if math.gcd(coefficient, modulus) != 1:
        return None

    inverse = pow(coefficient, -1, modulus)
    remaining = {other_var: -inverse * other_coefficient
                 for other_var, other_coefficient in coefficient_of_var.items() if other_var != var}

    return Determined_Variable(var=var,
                               term=_normalise_term(remaining, modulus),
                               constant=(inverse * congruence.rhs) % modulus,
                               source=f'congruence (mod {modulus})')


@dataclass
class Congruence_System:
    """
    The part of an existential block this pass reasons about: its bounds and its congruences.

    `bound_vars` are the block's quantified variables; a variable outside that set is free and may not
    be eliminated, since the surrounding formula constrains it too.
    """

    bound_vars: FrozenSet[Var]
    bounds: Dict[Var, Tuple[int, int]]
    congruences: List[Congruence] = field(default_factory=list)
    other_conjuncts: List[ASTp_Node] = field(default_factory=list)

    def variable_is_local_to(self, var: Var, congruence: Congruence) -> bool:
        """
        Whether `var` occurs in `congruence` and nowhere else but its own bounds.

        Locality is what makes eliminating the variable exact: the value the congruence forces on it
        must be free to take. It is not stable under the pass's own rewrites - eliminating one variable
        can make another local - so it is re-tested after every step rather than computed once.
        """
        if var not in self.bound_vars or var not in congruence.vars:
            return False
        if any(var in other.vars for other in self.congruences if other is not congruence):
            return False
        return not any(var in _referenced_vars_of(conjunct) for conjunct in self.other_conjuncts)


def _referenced_vars_of(node: ASTp_Node) -> FrozenSet[Var]:
    if isinstance(node, (Relation, Congruence)):
        return frozenset(node.vars)
    if isinstance(node, Var):
        return frozenset((node,))
    return frozenset(getattr(node, 'referenced_vars', ()))


def collect_congruence_system(quantifier: AST_Quantifier) -> Optional[Congruence_System]:
    """
    Read an existential block into a `Congruence_System`, or return None for a shape this pass does
    not handle: a body that is not a conjunction, or congruences of more than one modulus.
    """
    body = quantifier.child
    if not (isinstance(body, AST_Connective) and body.type == Connective_Type.AND):
        return None

    bounds: Dict[Var, Tuple[Optional[int], Optional[int]]] = {}
    congruences: List[Congruence] = []
    other_conjuncts: List[ASTp_Node] = []

    for conjunct in body.children:
        if isinstance(conjunct, Congruence):
            congruences.append(conjunct)
            continue
        if isinstance(conjunct, Relation) and conjunct.is_hard_bound():
            bound_type, var, limit = get_hard_bound_semantics(conjunct)
            lower, upper = bounds.get(var, (None, None))
            if bound_type == Bound_Type.LOWER:
                lower = limit if lower is None else max(lower, limit)
            else:
                upper = limit if upper is None else min(upper, limit)
            bounds[var] = (lower, upper)
            continue
        other_conjuncts.append(conjunct)

    if not congruences or len({congruence.modulus for congruence in congruences}) != 1:
        return None

    two_sided = {var: (lower, upper) for var, (lower, upper) in bounds.items()
                 if lower is not None and upper is not None}
    return Congruence_System(bound_vars=frozenset(quantifier.bound_vars), bounds=two_sided,
                             congruences=congruences, other_conjuncts=other_conjuncts)


@dataclass
class Modular_Bound_Derivation:
    """ What `derive_modular_bound_facts` produced. """

    facts: List[Modular_Bound_Fact] = field(default_factory=list)
    eliminated_vars: List[Var] = field(default_factory=list)
    eliminated_congruences: int = 0
    surviving_congruences: List[Congruence] = field(default_factory=list)

    def holds_for(self, assignment: Dict[Var, int]) -> bool:
        return all(fact.holds_for(assignment) for fact in self.facts)


def derive_modular_bound_facts(quantifier: AST_Quantifier,
                               fold_shared_variables: bool = True) -> Optional[Modular_Bound_Derivation]:
    """
    Eliminate the quantified variables a congruence determines, carrying their windows forward as
    modular interval facts.

    One round eliminates one variable:

    | Step | Condition |
    |---|---|
    | pick `v` | quantified, two-sidedly bounded, local to one congruence `C`, invertible coefficient in `C` |
    | substitute | rewrite every fact mentioning `v`, and every *other* congruence, in terms of `C`'s solution for `v` |
    | residualise | emit `v`'s own window as a fact on `C`'s remaining term, unless the window spans a full period |
    | discard | drop `v`, its bounds and `C` |

    Locality is re-tested each round, because eliminating one variable can make another local - in the
    motivating block `x15` becomes local only after `x16` has gone.

    `fold_shared_variables` controls the one lossy step: absorbing a still-bounded variable's range into
    a fact's interval. With it off the facts keep those variables and stay exact, at the cost of
    mentioning variables the caller may not want.

    Returns None when the block's shape is not handled at all.
    """
    system = collect_congruence_system(quantifier)
    if system is None:
        return None

    modulus = system.congruences[0].modulus
    derivation = Modular_Bound_Derivation()
    facts: List[Modular_Bound_Fact] = []
    congruences = list(system.congruences)

    while True:
        eliminable = _find_eliminable_variable(system, congruences)
        if eliminable is None:
            break
        var, congruence = eliminable

        determined = solve_congruence_for_variable(congruence, var)
        assert determined is not None, 'the search guarantees an invertible coefficient'

        lower, upper = system.bounds[var]
        if upper - lower + 1 < modulus:
            window = Modular_Interval(lower, upper)
            window_fact = Modular_Bound_Fact(term=determined.term, constant=determined.constant,
                                             interval=window, modulus=modulus,
                                             derivation=(f'window of {var}',))
            if not window_fact.is_vacuous():
                facts.append(window_fact)

        facts = [fact.with_substitution(var, determined) for fact in facts]
        congruences = [_substitute_into_congruence(other, var, determined, modulus)
                       for other in congruences if other is not congruence]

        derivation.eliminated_vars.append(var)
        derivation.eliminated_congruences += 1
        system.bounds.pop(var, None)

    if fold_shared_variables:
        facts = [_fold_bounded_variables(fact, system) for fact in facts]

    derivation.facts = [fact for fact in facts if not fact.is_vacuous()]
    derivation.surviving_congruences = congruences
    return derivation


def _find_eliminable_variable(system: Congruence_System,
                              congruences: Sequence[Congruence]) -> Optional[Tuple[Var, Congruence]]:
    """
    The next quantified variable to eliminate: the one with the **widest** window among those a
    congruence determines and nothing else constrains.

    Widest first, because a variable leaves the system by one of two routes and the routes cost
    differently. Eliminating it turns its window into a fact's interval; folding it *adds* its span to
    an interval, multiplied by whatever coefficient it carries. Each congruence can eliminate only one
    variable, so spending a congruence on a narrow window forces a wide one to be folded - which is how
    a `2**31`-wide window ends up widening a fact into vacuity.

    On the motivating block this picks `x16` and then `x15`, leaving the two ten-wide windows of `x13`
    and `x14` to be folded for a total widening of 99.
    """
    system.congruences = list(congruences)

    candidates: List[Tuple[int, Var, Congruence]] = []
    for congruence in congruences:
        for var in congruence.vars:
            if var not in system.bounds:
                continue
            if not system.variable_is_local_to(var, congruence):
                continue
            if solve_congruence_for_variable(congruence, var) is None:
                continue
            lower, upper = system.bounds[var]
            candidates.append((upper - lower + 1, var, congruence))

    if not candidates:
        return None

    widest = max(candidates, key=lambda candidate: (candidate[0], -candidate[1].id))
    return widest[1], widest[2]


def _substitute_into_congruence(congruence: Congruence, var: Var, replacement: Determined_Variable,
                                modulus: int) -> Congruence:
    """ `congruence` with `var` replaced by the term another congruence determines it to equal. """
    coefficient_of_var = dict(zip(congruence.vars, congruence.coefs))
    multiplier = coefficient_of_var.pop(var, 0)
    if multiplier == 0:
        return congruence

    for replacement_var, replacement_coefficient in replacement.term:
        coefficient_of_var[replacement_var] = (coefficient_of_var.get(replacement_var, 0)
                                               + multiplier * replacement_coefficient)

    term = _normalise_term(coefficient_of_var, modulus)
    return Congruence(vars=[var for var, _ in term], coefs=[coefficient for _, coefficient in term],
                      rhs=(congruence.rhs - multiplier * replacement.constant) % modulus,
                      modulus=modulus)


def _fold_bounded_variables(fact: Modular_Bound_Fact, system: Congruence_System) -> Modular_Bound_Fact:
    """ Absorb every still-quantified bounded variable of `fact` into its interval. """
    for var in sorted(fact.variables):
        if var not in system.bound_vars or var not in system.bounds:
            continue
        lower, upper = system.bounds[var]
        folded = fact.with_variable_folded(var, lower, upper)
        if folded.is_vacuous():
            return folded
        fact = folded
    return fact


# ---------------------------------------------------------------------------------------------
# The rewrite
# ---------------------------------------------------------------------------------------------

def _make_hard_bound(var: Var, lower: Optional[int], upper: Optional[int]) -> List[Relation]:
    bounds = []
    if lower is not None:
        bounds.append(Relation(vars=[var], coefs=[-1], rhs=-lower, predicate_symbol='<='))
    if upper is not None:
        bounds.append(Relation(vars=[var], coefs=[1], rhs=upper, predicate_symbol='<='))
    return bounds


def encode_fact(fact: Modular_Bound_Fact, witness: Var) -> Tuple[Congruence, List[Relation]]:
    """
    Encode `term + constant in [lo, hi] (mod M)` as a congruence over a witness variable and its bounds.

    `term + constant == witness (mod M)` with `witness` confined to the interval. The witness's range is
    shorter than the modulus - a fact whose interval reaches the modulus is vacuous and never encoded -
    so it names the residue unambiguously.
    """
    congruence = Congruence(vars=[var for var, _ in fact.term] + [witness],
                            coefs=[coefficient for _, coefficient in fact.term] + [-1],
                            rhs=(-fact.constant) % fact.modulus,
                            modulus=fact.modulus)
    return congruence, _make_hard_bound(witness, fact.interval.lower, fact.interval.upper)


@dataclass
class Modular_Bound_Rewrite_Stats:
    blocks_examined: int = 0
    blocks_rewritten: int = 0
    congruences_eliminated: int = 0
    facts_emitted: int = 0
    vars_eliminated: int = 0
    witnesses_introduced: int = 0

    declined_unhandled_shape: int = 0
    """ Body not a conjunction, or congruences of more than one modulus. """

    declined_nothing_determined: int = 0
    """ No quantified variable is bounded, local to one congruence, and invertibly coefficiented there. """

    declined_no_congruence_saved: int = 0
    """
    As many facts came out as congruences went in. Each fact costs a congruence of the same modulus
    plus a witness variable, so the rewrite would be a rename. This is what a block holding a single
    congruence always reduces to, and it is the common case.
    """

    def describe(self) -> str:
        return (f'examined {self.blocks_examined} blocks, rewrote {self.blocks_rewritten} '
                f'(eliminated {self.congruences_eliminated} congruences and {self.vars_eliminated} '
                f'variables, emitted {self.facts_emitted} facts over {self.witnesses_introduced} '
                f'witnesses); declined {self.declined_unhandled_shape} on shape, '
                f'{self.declined_nothing_determined} with nothing determined, '
                f'{self.declined_no_congruence_saved} that would have saved no congruence')


def rewrite_quantifier_with_modular_bounds(quantifier: AST_Quantifier,
                                           var_table: Dict[Var, 'VarInfo'],
                                           stats: Modular_Bound_Rewrite_Stats) -> ASTp_Node:
    """
    Rewrite one existential block, or return it unchanged.

    The rewrite is applied only when it does not increase the number of congruences and does decrease
    the number of quantified variables. Each emitted fact costs one congruence of the same modulus and
    one witness variable, so without that guard the pass could trade two congruences for three.
    """
    from amaya.preprocessing.eval import VarInfo

    stats.blocks_examined += 1
    # `fold_shared_variables=False` is required, not a tuning choice. Folding absorbs a variable's range
    # into an interval, which *weakens* the block - sound for deriving a necessary condition, and
    # unsound as a rewrite, since a weaker formula can be satisfiable where the original is not. The
    # residualisation itself is exact, so with folding off the rewrite preserves the solution set.
    derivation = derive_modular_bound_facts(quantifier, fold_shared_variables=False)
    if derivation is None:
        stats.declined_unhandled_shape += 1
        return quantifier
    if not derivation.eliminated_vars:
        stats.declined_nothing_determined += 1
        logger.debug('Modular bounds: no variable of the block is determined by a congruence it is '
                     'local to; leaving it alone.')
        return quantifier

    system = collect_congruence_system(quantifier)
    assert system is not None, 'the derivation already parsed this block'

    # A fact costs one congruence of the same modulus and one witness variable, so the rewrite is worth
    # making only when strictly fewer congruences come out than went in. That happens when a fact turned
    # out vacuous, or when a variable's window spanned a full period and its congruence vanished
    # outright. Trading two congruences for two is a rename, not a simplification.
    emitted, eliminated = len(derivation.facts), derivation.eliminated_congruences
    if emitted >= eliminated:
        stats.declined_no_congruence_saved += 1
        logger.debug('Modular bounds: eliminating %d variable(s) would trade %d congruence(s) for %d '
                     'fact(s), which saves none; leaving the block alone.',
                     len(derivation.eliminated_vars), eliminated, emitted)
        return quantifier

    eliminated_vars = set(derivation.eliminated_vars)
    surviving_vars = [var for var in quantifier.bound_vars if var not in eliminated_vars]

    conjuncts: List[ASTp_Node] = list(system.other_conjuncts)
    conjuncts.extend(derivation.surviving_congruences)
    for var in surviving_vars:
        lower, upper = system.bounds.get(var, (None, None))
        conjuncts.extend(_make_hard_bound(var, lower, upper))

    next_var_id = max((var.id for var in var_table), default=0) + 1
    witnesses: List[Var] = []
    for index, fact in enumerate(derivation.facts):
        witness = Var(id=next_var_id + index)
        var_table[witness] = VarInfo(name=f'mod_witness_{witness.id}',
                                     type=next(iter(var_table.values())).type, is_formula_param=False)
        witnesses.append(witness)
        congruence, bounds = encode_fact(fact, witness)
        conjuncts.append(congruence)
        conjuncts.extend(bounds)

    logger.info('Modular bounds: eliminated %s and %d congruence(s) from a block, emitting %d fact(s).',
                ', '.join(str(var) for var in derivation.eliminated_vars), eliminated, emitted)
    stats.blocks_rewritten += 1
    stats.congruences_eliminated += eliminated
    stats.facts_emitted += emitted
    stats.vars_eliminated += len(derivation.eliminated_vars)
    stats.witnesses_introduced += len(witnesses)

    body = AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND, children=tuple(conjuncts))
    return AST_Quantifier(referenced_vars=tuple(), bound_vars=tuple(surviving_vars) + tuple(witnesses),
                          child=body)


def propagate_modular_bounds(ast: ASTp_Node, var_table: Dict[Var, 'VarInfo'],
                             stats: Optional[Modular_Bound_Rewrite_Stats] = None) -> ASTp_Node:
    """
    Eliminate congruence-determined quantified variables from every existential block of `ast`.

    See the module docstring for the reasoning. Experimental and disabled by default; enable with
    `-O modular-bounds`.
    """
    from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars

    if stats is None:
        stats = Modular_Bound_Rewrite_Stats()

    rewritten = _rewrite_recursively(ast, var_table, stats)
    if stats.blocks_rewritten:
        fill_referenced_vars(rewritten)
        logger.info('Modular bounds: %s', stats.describe())
    else:
        logger.debug('Modular bounds: %s', stats.describe())
    return rewritten


def _rewrite_recursively(node: ASTp_Node, var_table: Dict[Var, 'VarInfo'],
                         stats: Modular_Bound_Rewrite_Stats) -> ASTp_Node:
    from amaya.relations_structures import AST_Negation

    if isinstance(node, AST_Quantifier):
        rewritten_child = _rewrite_recursively(node.child, var_table, stats)
        candidate = AST_Quantifier(referenced_vars=node.referenced_vars, bound_vars=node.bound_vars,
                                   child=rewritten_child)
        return rewrite_quantifier_with_modular_bounds(candidate, var_table, stats)

    if isinstance(node, AST_Connective):
        return node.replace_children(tuple(_rewrite_recursively(child, var_table, stats)
                                           for child in node.children))

    if isinstance(node, AST_Negation):
        return AST_Negation(referenced_vars=node.referenced_vars,
                            child=_rewrite_recursively(node.child, var_table, stats))

    return node
