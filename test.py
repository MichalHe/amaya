from pressburger_algorithms import build_nfa_from_inequality
from pressburger_algorithms import Relation
from mtbdd_transitions import MTBDDTransitionFn, determinize_mtbdd
import timeit

var_names = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j']
var_coefs_1 = [1, 2, 3, 4, 5, 0, 0, 0, 0, 0]
var_coefs_2 = [0, 0, 0, 0, 0, 1, 2, 3, 4, 5]

ineq0 = Relation(variable_names=var_names, variable_coeficients=var_coefs_1, absolute_part=1000, operation='<=')
ineq1 = Relation(variable_names=var_names, variable_coeficients=var_coefs_2, absolute_part=-2001, operation='<=')

nfa_original0 = build_nfa_from_inequality(ineq0)
nfa_original1 = build_nfa_from_inequality(ineq1)


proj0 = nfa_original0.do_projection('a')
proj1 = nfa_original1.do_projection('d')

union = proj0.union(proj1)

mtbdd_tfn = MTBDDTransitionFn()
lt = None
for t in union.transition_fn.iter():
    if lt is None:
        lt = len(t[1])
    else:
        assert lt == len(t[1])  # Integrity checking
    mtbdd_tfn.insert_transition(t[0], t[1], t[2])

mtbdd_time = timeit.timeit(lambda: determinize_mtbdd(mtbdd_tfn, union.initial_states), number=1)
standard_time = timeit.timeit(lambda: union.determinize(), number=1)

print(mtbdd_time)
print(standard_time)

# TODO: 2) Write MTBDD_TransitionFn function which simply receives set of
#       states and returns the union mtbdd + its leaves (= one metastep in
#       determinization)
