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
- [x] solve final state uniqueness when merging automatons
- [ ] \[WIP\] test, wheter parser recognizes variable coefs expressions correctly
- [ ] solve first formula :)


### Why are states implemented the way they are
The way of internal representation of automaton states was changed as of (1.10.2020). 
The motivation to perform this changed arised when it became obvious that plain integer,
which is used to denote state in DFA/NFA encoding will become a problem when uniting two automatons,
since it might get consumed in automaton union (set union uperation). Therefor automaton state
must hold more than just an integer value - it also requires an attribute, which would determine, that would
differentiate between two integer states, which belong to different automatons.
