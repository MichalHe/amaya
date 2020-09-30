This is my implementation of algorithms working with pressburger arithmetics using finite automatons.

### TODO
- [x] build nfa to solve inequalities over Z
- [x] analyze formulas to get information about the equation/inequation:
- [x] Free variables
- [x] Absolute part of the formula
- [x] variable coeficients vector
- [ ] Test whether projection produces correct symbol maps
- [ ] implement automaton intersection
- [ ] implement variable projection (quantifiers)
- [ ] solve final state uniqueness when merging automatons
- [ ] test, wheter parser recognizes variable coefs expressions correctly
- [ ] solve first formula :)

### Efficient representation of transitions between states.
##### 28.9
One of the more efficient ways about how to store transitions is to store them inside Multi Terminal BDD.
After brief investigation, there are no viable MTBDD python libraries, so I'm considering writing my own
implementation, customized for this purpose, most likely based on the pyeda library.
##### 29.9
On the other hand, analyzing the BDD I see two benefits:
1. memory efficient storage for sparse/compact boolean functions
2. quick implementation of the projection (exists quantifier)

To point 1. - we don't have sparse transition functions (except for final state in NFA over Z) -- doubtious benefits

To point 2. - I believe that the dictionary reference swapping (replacing `key#0 -> value` with `key#1 -> value`)
should be pretty straightforward. This justifies (for now) the decision not to transition from dictionary based transition
functions towards BDD.


