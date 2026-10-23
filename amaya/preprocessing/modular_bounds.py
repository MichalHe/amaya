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
over `x1`.

The pass has two stages:

| Stage | Entry point | Fact representation | Exact |
|---|---|---|---|
| derivation | `derive_modular_bound_facts` | `Modular_Bound_Fact`: one interval on one linear term | yes with `fold_shared_variables=False`; with it, a variable several facts mention is folded into each fact separately (`Modular_Bound_Fact.with_variable_folded`), which over-approximates |
| exact folding | `fold_facts_exactly` | `Modular_Union_Fact`: a union of intervals on one linear term | yes |

The derivation keeps every fact a single interval, because substituting a determined variable into
`k*v in W` multiplies the coefficients of the *term* and leaves `W` alone. On the motivating block it
yields two facts that share `x13` and `x14`. The exact folding removes such shared variables: when the
term of one fact is an integer multiple of the term of another (`x13 + 100*x1 + 10*x14 + c` against
`10*x1 + x14 + c'`, once `x13`, which occurs in the first fact only, is folded), the first fact is a
condition on the second fact's term, and pulling an interval back through the multiplication by `k`
gives a union of up to one interval per period crossed. `x14` then occurs in one fact only and is
folded exactly.

`rewrite_quantifier_with_modular_bounds` runs both stages and replaces the block when fewer congruences
remain. It is reached through `propagate_modular_bounds`, enabled by `-O modular-bounds`
(`amaya/config.py:propagate_modular_bounds`, disabled by default).
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Iterable, List, Optional, Sequence, Tuple

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
        """
        Whether the fact holds for every assignment, so dropping it preserves the solution set.

        A fact with an empty term is a ground test, `constant in interval (mod modulus)`, which can be
        false; it is vacuous only when that test succeeds. A false ground fact is kept, and
        `fold_facts_exactly` reports it as unsatisfiable.
        """
        if self.interval.is_vacuous(self.modulus):
            return True
        return not self.term and self.interval.contains(self.constant, self.modulus)

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


def _coefficient_of_var_in_congruence(congruence: Congruence) -> Dict[Var, int]:
    """ The coefficient of every variable of `congruence`, summed over repeated occurrences of the variable. """
    coefficient_of_var: Dict[Var, int] = {}
    for var, coefficient in zip(congruence.vars, congruence.coefs):
        coefficient_of_var[var] = coefficient_of_var.get(var, 0) + coefficient
    return coefficient_of_var


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
    coefficient_of_var = _coefficient_of_var_in_congruence(congruence)
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

    `bounds` holds only the two-sided bounds of quantified variables, which is what the derivation
    reads. `hard_bound_relations` holds every hard bound of every quantified variable as written, which
    is what the rewrite re-emits for the variables it does not eliminate. Hard bounds on free variables
    are kept in `other_conjuncts`.
    """

    bound_vars: FrozenSet[Var]
    bounds: Dict[Var, Tuple[int, int]]
    congruences: List[Congruence] = field(default_factory=list)
    other_conjuncts: List[ASTp_Node] = field(default_factory=list)
    hard_bound_relations: Dict[Var, List[Relation]] = field(default_factory=dict)

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
    """
    Every variable occurring in `node`, including variables bound inside it.

    Computed from the structure rather than read from the cached `referenced_vars` field: blocks this
    pass has already rewritten are nested inside the blocks it rewrites later, and their cached field is
    repaired only once the whole traversal ends (`propagate_modular_bounds`).
    """
    from amaya.relations_structures import AST_Negation

    if isinstance(node, (Relation, Congruence)):
        return frozenset(node.vars)
    if isinstance(node, Var):
        return frozenset((node,))
    if isinstance(node, AST_Connective):
        return frozenset().union(*(_referenced_vars_of(child) for child in node.children))
    if isinstance(node, (AST_Negation, AST_Quantifier)):
        return _referenced_vars_of(node.child)
    return frozenset()


def collect_congruence_system(quantifier: AST_Quantifier) -> Optional[Congruence_System]:
    """
    Read an existential block into a `Congruence_System`, or return None for a shape this pass does
    not handle: a body that is not a conjunction, or congruences of more than one modulus.
    """
    body = quantifier.child
    if not (isinstance(body, AST_Connective) and body.type == Connective_Type.AND):
        return None

    bound_vars = frozenset(quantifier.bound_vars)
    bounds: Dict[Var, Tuple[Optional[int], Optional[int]]] = {}
    hard_bound_relations: Dict[Var, List[Relation]] = {}
    congruences: List[Congruence] = []
    other_conjuncts: List[ASTp_Node] = []

    for conjunct in body.children:
        if isinstance(conjunct, Congruence):
            congruences.append(conjunct)
            continue
        if isinstance(conjunct, Relation) and conjunct.is_hard_bound() and conjunct.vars[0] in bound_vars:
            hard_bound_relations.setdefault(conjunct.vars[0], []).append(conjunct)
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
    return Congruence_System(bound_vars=bound_vars, bounds=two_sided,
                             congruences=congruences, other_conjuncts=other_conjuncts,
                             hard_bound_relations=hard_bound_relations)


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
    coefficient_of_var = _coefficient_of_var_in_congruence(congruence)
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
# Exact folding over unions of intervals
# ---------------------------------------------------------------------------------------------

MAX_UNION_INTERVALS = 64
""" The most intervals a `Modular_Interval_Union` produced by this pass may hold; an operation exceeding it is declined. """

MAX_ENUMERATED_FOLD_RANGE = 64
"""
The widest variable range `_shift_union_by_multiples` enumerates value by value, which it does when the
shifted copies of a union do not overlap.
"""


def _ceil_div(numerator: int, denominator: int) -> int:
    """ ceil(numerator / denominator) for a positive denominator, exact for integers of any size. """
    return -(-numerator // denominator)


@dataclass(frozen=True)
class Modular_Interval_Union:
    """
    A set of residues modulo `modulus`, as sorted, disjoint, non-adjacent intervals inside `[0, modulus - 1]`.

    The endpoints are reduced, unlike those of `Modular_Interval`: an interval that crosses the wrap is
    stored as two intervals, and a set covering every residue is `((0, modulus - 1),)`.
    """

    intervals: Tuple[Tuple[int, int], ...]
    modulus: int

    @staticmethod
    def from_unreduced_intervals(intervals: Iterable[Tuple[int, int]], modulus: int) -> 'Modular_Interval_Union':
        """ The residues of the integers in the given intervals; an interval with `upper < lower` contributes nothing. """
        pieces: List[Tuple[int, int]] = []
        for lower, upper in intervals:
            measure = upper - lower + 1
            if measure <= 0:
                continue
            if measure >= modulus:
                return Modular_Interval_Union(((0, modulus - 1),), modulus)
            reduced_lower = lower % modulus
            reduced_upper = reduced_lower + measure - 1
            if reduced_upper < modulus:
                pieces.append((reduced_lower, reduced_upper))
            else:
                pieces.append((reduced_lower, modulus - 1))
                pieces.append((0, reduced_upper - modulus))

        pieces.sort()
        merged: List[Tuple[int, int]] = []
        for lower, upper in pieces:
            if merged and lower <= merged[-1][1] + 1:
                merged[-1] = (merged[-1][0], max(merged[-1][1], upper))
            else:
                merged.append((lower, upper))
        return Modular_Interval_Union(tuple(merged), modulus)

    def is_empty(self) -> bool:
        return not self.intervals

    def is_full(self) -> bool:
        return self.intervals == ((0, self.modulus - 1),)

    def contains(self, value: int) -> bool:
        reduced = value % self.modulus
        return any(lower <= reduced <= upper for lower, upper in self.intervals)

    def negated(self) -> 'Modular_Interval_Union':
        """ `{-u : u in self}`. """
        return Modular_Interval_Union.from_unreduced_intervals(((-upper, -lower) for lower, upper in self.intervals),
                                                               self.modulus)

    def __repr__(self) -> str:
        return ' u '.join(f'[{lower}, {upper}]' for lower, upper in self.intervals) or '{}'


def _shift_union_by_multiples(residues: Modular_Interval_Union, coefficient: int,
                              lower: int, upper: int) -> Optional[Modular_Interval_Union]:
    """
    `{u - coefficient*v : u in residues, v in [lower, upper]}` modulo the union's modulus, or None when
    computing it would exceed `MAX_ENUMERATED_FOLD_RANGE` or `MAX_UNION_INTERVALS`.

    `rest + coefficient*v in residues` holds for some `v` in `[lower, upper]` exactly when `rest` lies in
    this set. Consecutive values of `v` shift a copy of each interval by `|coefficient|`; when every
    interval holds at least `|coefficient|` residues, the copies of an interval overlap or touch and their
    union is one interval. Otherwise the copies are enumerated one value of `v` at a time.

    Requires `lower <= upper`.
    """
    shifts = (coefficient * lower, coefficient * upper)
    intervals_cover_every_step = all(interval_upper - interval_lower + 1 >= abs(coefficient)
                                     for interval_lower, interval_upper in residues.intervals)
    if intervals_cover_every_step or lower == upper:
        shifted = Modular_Interval_Union.from_unreduced_intervals(
            ((interval_lower - max(shifts), interval_upper - min(shifts))
             for interval_lower, interval_upper in residues.intervals),
            residues.modulus)
    elif upper - lower + 1 <= MAX_ENUMERATED_FOLD_RANGE:
        shifted = Modular_Interval_Union.from_unreduced_intervals(
            ((interval_lower - coefficient * value, interval_upper - coefficient * value)
             for value in range(lower, upper + 1)
             for interval_lower, interval_upper in residues.intervals),
            residues.modulus)
    else:
        return None

    if len(shifted.intervals) > MAX_UNION_INTERVALS:
        return None
    return shifted


def _preimage_under_multiplication(target: Modular_Interval_Union, multiplier: int, constant: int,
                                   domain: Modular_Interval_Union) -> Optional[Modular_Interval_Union]:
    """
    `{s in domain : multiplier*s + constant (mod modulus) in target}`, or None when the result, or the
    number of candidate intervals examined to compute it, would exceed `MAX_UNION_INTERVALS`.

    For one interval `[a, b]` of the domain, `multiplier*s + constant` ranges over the periods
    `p = floor((multiplier*a + constant) / modulus) .. floor((multiplier*b + constant) / modulus)`, and
    within period `p` it lies in a target interval `[u, v]` exactly when
    `s in [ceil((u + p*modulus - constant) / multiplier), floor((v + p*modulus - constant) / multiplier)]`.
    The result can hold more intervals than the target: pulling an interval back through a
    multiplication by `k` yields up to one interval per period the image crosses.
    """
    modulus = target.modulus
    if multiplier < 0:
        return _preimage_under_multiplication(target.negated(), -multiplier, -constant, domain)
    assert multiplier > 0, 'a zero multiplier relates no terms'

    pieces: List[Tuple[int, int]] = []
    for domain_lower, domain_upper in domain.intervals:
        first_period = (multiplier * domain_lower + constant) // modulus
        last_period = (multiplier * domain_upper + constant) // modulus
        if (last_period - first_period + 1) * len(target.intervals) > 4 * MAX_UNION_INTERVALS:
            return None
        for period in range(first_period, last_period + 1):
            for target_lower, target_upper in target.intervals:
                piece_lower = max(domain_lower, _ceil_div(target_lower + period * modulus - constant, multiplier))
                piece_upper = min(domain_upper, (target_upper + period * modulus - constant) // multiplier)
                if piece_lower <= piece_upper:
                    pieces.append((piece_lower, piece_upper))

    preimage = Modular_Interval_Union.from_unreduced_intervals(pieces, modulus)
    if len(preimage.intervals) > MAX_UNION_INTERVALS:
        return None
    return preimage


def _multiplier_relating_terms(base_term: Linear_Term, other_term: Linear_Term, modulus: int) -> Optional[int]:
    """
    An integer `k` with `other_term == k * base_term` coefficientwise modulo `modulus`, or None.

    `k` is read off one variable of `base_term`, preferring one with an invertible coefficient, and then
    checked against every variable of either term. Of the values of `k` that satisfy the check, the one
    of least magnitude is returned when the coefficient is invertible, because the number of intervals
    `_preimage_under_multiplication` produces grows with `|k|`.
    """
    if not base_term:
        return None
    base_coefficient_of_var = dict(base_term)
    other_coefficient_of_var = dict(other_term)

    pivot_var, pivot_coefficient = next(((var, coefficient) for var, coefficient in base_term
                                         if math.gcd(coefficient, modulus) == 1), base_term[0])
    other_pivot_coefficient = other_coefficient_of_var.get(pivot_var, 0)
    if math.gcd(pivot_coefficient, modulus) == 1:
        multiplier = (other_pivot_coefficient * pow(pivot_coefficient, -1, modulus)) % modulus
        if multiplier > modulus // 2:
            multiplier -= modulus
    elif other_pivot_coefficient % pivot_coefficient == 0:
        multiplier = other_pivot_coefficient // pivot_coefficient
    else:
        return None

    if multiplier == 0:
        return None
    all_vars = set(base_coefficient_of_var) | set(other_coefficient_of_var)
    if all((multiplier * base_coefficient_of_var.get(var, 0) - other_coefficient_of_var.get(var, 0)) % modulus == 0
           for var in all_vars):
        return multiplier
    return None


@dataclass(frozen=True)
class Modular_Union_Fact:
    """
    `term + constant` lies in `residues`, modulo the modulus of `residues`.

    The exact counterpart of `Modular_Bound_Fact`: the residues may form several intervals, which is what
    `merged_with` and `with_variable_folded_exactly` produce.
    """

    term: Linear_Term
    constant: int
    residues: Modular_Interval_Union
    derivation: Tuple[str, ...] = tuple()

    @staticmethod
    def from_bound_fact(fact: Modular_Bound_Fact) -> 'Modular_Union_Fact':
        residues = Modular_Interval_Union.from_unreduced_intervals([(fact.interval.lower, fact.interval.upper)],
                                                                   fact.modulus)
        return Modular_Union_Fact(term=fact.term, constant=fact.constant, residues=residues,
                                  derivation=fact.derivation)

    @property
    def modulus(self) -> int:
        return self.residues.modulus

    @property
    def variables(self) -> FrozenSet[Var]:
        return frozenset(var for var, _ in self.term)

    def coefficient_of(self, var: Var) -> int:
        return dict(self.term).get(var, 0)

    def holds_for(self, assignment: Dict[Var, int]) -> bool:
        value = self.constant + sum(coefficient * assignment[var] for var, coefficient in self.term)
        return self.residues.contains(value)

    def with_variable_folded_exactly(self, var: Var, lower: int, upper: int) -> Optional['Modular_Union_Fact']:
        """
        The fact `exists var in [lower, upper]. self`, or None when `_shift_union_by_multiples` declines.

        Equivalent to the conjunction of `self` and `lower <= var <= upper` with `var` quantified away only
        when no other constraint mentions `var`; the caller establishes that.
        """
        coefficient = self.coefficient_of(var)
        if coefficient == 0:
            return self
        shifted = _shift_union_by_multiples(self.residues, coefficient, lower, upper)
        if shifted is None:
            return None
        return Modular_Union_Fact(term=tuple((term_var, term_coefficient) for term_var, term_coefficient in self.term
                                             if term_var != var),
                                  constant=self.constant,
                                  residues=shifted,
                                  derivation=self.derivation + (f'fold {var} over [{lower}, {upper}] exactly',))

    def merged_with(self, other: 'Modular_Union_Fact') -> Optional['Modular_Union_Fact']:
        """
        One fact over `self.term` equivalent to the conjunction of `self` and `other`, or None when the term
        of `other` is not an integer multiple of `self.term` or the preimage exceeds `MAX_UNION_INTERVALS`.

        With `s = self.term + self.constant (mod M)` and `other.term == k * self.term`, the term of `other`
        plus its constant equals `k*s + (other.constant - k*self.constant)`, so `other` is a condition on
        `s` alone and is pulled back through the multiplication by `k`.
        """
        multiplier = _multiplier_relating_terms(self.term, other.term, self.modulus)
        if multiplier is None:
            return None
        preimage = _preimage_under_multiplication(other.residues, multiplier,
                                                  other.constant - multiplier * self.constant, self.residues)
        if preimage is None:
            return None
        return Modular_Union_Fact(term=self.term, constant=self.constant, residues=preimage,
                                  derivation=self.derivation + (f'merge {multiplier} * ({other!r})',))

    def __repr__(self) -> str:
        rendered = ' '.join(f'{coefficient:+d}*{var}' for var, coefficient in self.term)
        constant = f' {self.constant:+d}' if self.constant else ''
        return f'{rendered}{constant} in {self.residues} (mod {self.modulus})'


@dataclass
class Exact_Folding_Result:
    """ What `fold_facts_exactly` produced. """

    facts: List[Modular_Union_Fact] = field(default_factory=list)
    folded_vars: List[Var] = field(default_factory=list)
    merges: int = 0
    is_unsatisfiable: bool = False
    """ Some fact holds for no assignment, so the conjunction of the facts is false. """


def fold_facts_exactly(facts: Sequence[Modular_Union_Fact],
                       foldable_var_ranges: Dict[Var, Tuple[int, int]],
                       vars_constrained_elsewhere: FrozenSet[Var]) -> Exact_Folding_Result:
    """
    Remove variables from a conjunction of facts without changing its solution set.

    `foldable_var_ranges` maps each quantified variable whose only other constraints are the given bounds
    to its range; `vars_constrained_elsewhere` lists variables that occur in constraints outside `facts`.
    The two steps below repeat until neither applies:

    | Step | Condition | Effect |
    |---|---|---|
    | fold | `v` in `foldable_var_ranges`, not in `vars_constrained_elsewhere`, occurs in exactly one fact | `v` and its range are removed from that fact (`with_variable_folded_exactly`) |
    | merge | the term of one fact is an integer multiple of the term of another | the two facts become one fact over the smaller term (`merged_with`) |

    Each step replaces a subformula by an equivalent one: a fold quantifies away a variable that occurs in
    one constraint, and a merge rewrites one constraint in terms of the other's term. A merge can make a
    variable occur in one fact only, which enables the next fold.

    After each step, a fact with an empty term is evaluated, a fact holding for every residue is dropped,
    and a fact with no residues makes the result unsatisfiable.
    """
    result = Exact_Folding_Result()
    remaining_var_ranges = dict(foldable_var_ranges)
    current_facts = list(facts)

    while True:
        settled_facts: List[Modular_Union_Fact] = []
        for fact in current_facts:
            if fact.residues.is_empty() or (not fact.term and not fact.residues.contains(fact.constant)):
                result.is_unsatisfiable = True
                result.facts = [fact]
                return result
            if not fact.term or fact.residues.is_full():
                continue
            settled_facts.append(fact)
        current_facts = settled_facts

        fold = _fold_one_variable_occurring_in_one_fact(current_facts, remaining_var_ranges,
                                                        vars_constrained_elsewhere)
        if fold is not None:
            current_facts, folded_var = fold
            result.folded_vars.append(folded_var)
            remaining_var_ranges.pop(folded_var)
            continue

        merged_facts = _merge_one_pair_of_facts(current_facts)
        if merged_facts is not None:
            current_facts = merged_facts
            result.merges += 1
            continue

        break

    result.facts = current_facts
    return result


def _fold_one_variable_occurring_in_one_fact(
        facts: List[Modular_Union_Fact],
        foldable_var_ranges: Dict[Var, Tuple[int, int]],
        vars_constrained_elsewhere: FrozenSet[Var]) -> Optional[Tuple[List[Modular_Union_Fact], Var]]:
    for var in sorted(foldable_var_ranges, key=lambda var: var.id):
        if var in vars_constrained_elsewhere:
            continue
        lower, upper = foldable_var_ranges[var]
        if lower > upper:
            continue
        occurrences = [index for index, fact in enumerate(facts) if fact.coefficient_of(var) != 0]
        if len(occurrences) != 1:
            continue
        folded = facts[occurrences[0]].with_variable_folded_exactly(var, lower, upper)
        if folded is None:
            continue
        updated_facts = list(facts)
        updated_facts[occurrences[0]] = folded
        return updated_facts, var
    return None


def _merge_one_pair_of_facts(facts: List[Modular_Union_Fact]) -> Optional[List[Modular_Union_Fact]]:
    for base_index, base_fact in enumerate(facts):
        for other_index, other_fact in enumerate(facts):
            if base_index == other_index:
                continue
            merged = base_fact.merged_with(other_fact)
            if merged is None:
                continue
            return [merged if index == base_index else fact
                    for index, fact in enumerate(facts) if index != other_index]
    return None


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


def encode_union_fact(fact: Modular_Union_Fact, witness: Var) -> List[ASTp_Node]:
    """
    Encode `term + constant in residues (mod M)` as conjuncts over a witness variable.

    `term + constant == witness (mod M)`, and `witness` lies in one of the intervals of `residues`: two
    hard bounds for a single interval, a disjunction of pairs of hard bounds otherwise. Every interval
    lies inside `[0, M - 1]`, so the witness names the residue unambiguously.
    """
    congruence = Congruence(vars=[var for var, _ in fact.term] + [witness],
                            coefs=[coefficient for _, coefficient in fact.term] + [-1],
                            rhs=(-fact.constant) % fact.modulus,
                            modulus=fact.modulus)
    alternatives = [_make_hard_bound(witness, lower, upper) for lower, upper in fact.residues.intervals]
    if len(alternatives) == 1:
        return [congruence, *alternatives[0]]

    disjunction = AST_Connective(referenced_vars=tuple(), type=Connective_Type.OR,
                                 children=tuple(AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND,
                                                               children=tuple(bounds))
                                                for bounds in alternatives))
    return [congruence, disjunction]


@dataclass
class Modular_Bound_Rewrite_Stats:
    blocks_examined: int = 0
    blocks_rewritten: int = 0
    blocks_refuted: int = 0
    """ Blocks replaced by False because a fact holds for no assignment. """

    congruences_eliminated: int = 0
    """ Congruences removed by solving for a determined variable (`derive_modular_bound_facts`). """

    vars_eliminated: int = 0
    """ Variables removed by solving a congruence for them. """

    vars_folded: int = 0
    """ Variables removed by `fold_facts_exactly`. """

    facts_merged: int = 0
    facts_emitted: int = 0
    intervals_emitted: int = 0
    witnesses_introduced: int = 0

    declined_unhandled_shape: int = 0
    """ Body not a conjunction, or congruences of more than one modulus. """

    declined_nothing_determined: int = 0
    """ No quantified variable is bounded, local to one congruence, and invertibly coefficiented there. """

    declined_no_congruence_saved: int = 0
    """
    After folding, at least as many congruences would come out as went in. Each emitted fact costs one
    congruence of the block's modulus and one witness variable.
    """

    def describe(self) -> str:
        return (f'examined {self.blocks_examined} blocks, rewrote {self.blocks_rewritten}, refuted '
                f'{self.blocks_refuted} (eliminated {self.congruences_eliminated} congruences and '
                f'{self.vars_eliminated} variables, folded {self.vars_folded} variables, merged '
                f'{self.facts_merged} fact pairs, emitted {self.facts_emitted} facts with '
                f'{self.intervals_emitted} intervals over {self.witnesses_introduced} witnesses); declined '
                f'{self.declined_unhandled_shape} on shape, {self.declined_nothing_determined} with nothing '
                f'determined, {self.declined_no_congruence_saved} that would have saved no congruence')


def rewrite_quantifier_with_modular_bounds(quantifier: AST_Quantifier,
                                           var_table: Dict[Var, 'VarInfo'],
                                           stats: Modular_Bound_Rewrite_Stats) -> ASTp_Node:
    """
    Rewrite one existential block into an equivalent formula, or return it unchanged.

    1. `derive_modular_bound_facts` (without folding) solves congruences for the variables they determine
       and turns each such variable's window into a single-interval fact.
    2. `fold_facts_exactly` removes the remaining bounded quantified variables that it can remove without
       approximation, merging facts into unions of intervals where one term is a multiple of another.
    3. Each remaining fact is encoded by `encode_union_fact`.

    The block is replaced by False when a fact holds for no assignment. Otherwise the rewrite is applied
    only when strictly fewer congruences come out than went in.
    """
    from amaya.preprocessing.eval import VarInfo
    from amaya.relations_structures import BoolLiteral, VariableType

    stats.blocks_examined += 1
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

    eliminated_vars = set(derivation.eliminated_vars)
    vars_constrained_elsewhere = frozenset().union(
        *(_referenced_vars_of(node) for node in (*system.other_conjuncts, *derivation.surviving_congruences)))
    foldable_var_ranges = {var: var_range for var, var_range in system.bounds.items() if var not in eliminated_vars}
    folding = fold_facts_exactly([Modular_Union_Fact.from_bound_fact(fact) for fact in derivation.facts],
                                 foldable_var_ranges, vars_constrained_elsewhere)

    if folding.is_unsatisfiable:
        logger.info('Modular bounds: the fact %s holds for no assignment; the block is False.', folding.facts[0])
        stats.blocks_refuted += 1
        return BoolLiteral(value=False)

    congruences_in = len(system.congruences)
    congruences_out = len(derivation.surviving_congruences) + len(folding.facts)
    if congruences_out >= congruences_in:
        stats.declined_no_congruence_saved += 1
        logger.debug('Modular bounds: eliminating %d and folding %d variable(s) would leave %d of %d '
                     'congruence(s); leaving the block alone.',
                     len(derivation.eliminated_vars), len(folding.folded_vars), congruences_out, congruences_in)
        return quantifier

    removed_vars = eliminated_vars | set(folding.folded_vars)
    surviving_vars = [var for var in quantifier.bound_vars if var not in removed_vars]

    conjuncts: List[ASTp_Node] = list(system.other_conjuncts)
    conjuncts.extend(derivation.surviving_congruences)
    for var in surviving_vars:
        conjuncts.extend(system.hard_bound_relations.get(var, []))

    next_var_id = max((var.id for var in var_table), default=0) + 1
    witnesses: List[Var] = []
    for index, fact in enumerate(folding.facts):
        witness = Var(id=next_var_id + index)
        var_table[witness] = VarInfo(name=f'mod_witness_{witness.id}', type=VariableType.INT, is_formula_param=False)
        witnesses.append(witness)
        conjuncts.extend(encode_union_fact(fact, witness))
        stats.intervals_emitted += len(fact.residues.intervals)

    logger.info('Modular bounds: eliminated %s, folded %s, %d congruence(s) of %d remain; facts: %s',
                ', '.join(str(var) for var in derivation.eliminated_vars) or 'nothing',
                ', '.join(str(var) for var in folding.folded_vars) or 'nothing',
                congruences_out, congruences_in, folding.facts)
    stats.blocks_rewritten += 1
    stats.congruences_eliminated += derivation.eliminated_congruences
    stats.vars_eliminated += len(derivation.eliminated_vars)
    stats.vars_folded += len(folding.folded_vars)
    stats.facts_merged += folding.merges
    stats.facts_emitted += len(folding.facts)
    stats.witnesses_introduced += len(witnesses)

    if not conjuncts:
        return BoolLiteral(value=True)
    body = conjuncts[0] if len(conjuncts) == 1 else AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND,
                                                                    children=tuple(conjuncts))
    new_bound_vars = tuple(surviving_vars) + tuple(witnesses)
    if not new_bound_vars:
        return body
    return AST_Quantifier(referenced_vars=tuple(), bound_vars=new_bound_vars, child=body)


def propagate_modular_bounds(ast: ASTp_Node, var_table: Dict[Var, 'VarInfo'],
                             stats: Optional[Modular_Bound_Rewrite_Stats] = None) -> ASTp_Node:
    """
    Rewrite every existential block of `ast` with `rewrite_quantifier_with_modular_bounds`.

    See the module docstring for the reasoning. Experimental and disabled by default; enable with
    `-O modular-bounds`.
    """
    from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars

    if stats is None:
        stats = Modular_Bound_Rewrite_Stats()

    rewritten = _rewrite_recursively(ast, var_table, stats)
    if stats.blocks_rewritten or stats.blocks_refuted:
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
