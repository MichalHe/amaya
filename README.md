This is an work-in-progress implementation of algorithms working with pressburger arithmetics using finite automatons.

# How to render graphs from SMT Library language into graphviz(dot)
First of all make sure that you have installed all packages from `requirements.txt` file. It is recommended to use virtual env 
to manage python app dependencies. Afterwards run following command (replace `<your_input_file>` with the path to the file containing inequality):
```sh
python3 ./make_digraph.py -i <your_input_file>
```

By default the script reads from stdin, but by passing `-i` flag, provided file is read instead. The output is to stdout.

**Warning**: I haven't progressed as far as combining multiple inequations into one, so am quite sure a file contaning more then just one
inequation might (will) not work.

### TODO
- [x] build nfa to solve inequalities over Z
- [x] analyze formulas to get information about the equation/inequation:
- [x] Free variables
- [x] Absolute part of the formula
- [x] variable coeficients vector
- [X] Test whether projection produces correct symbol maps
- [X] implement automaton intersection
- [X] implement variable projection (quantifiers)
- [x] solve final state uniqueness when merging automatons
- [X] Implement multiplication operation in the equation evaluation.
- [X] test, wheter parser recognizes variable coefs expressions correctly
- [X] make advanced tests for automaton union
- [ ] make advanced tests for automaton intersection
- [ ] make advanced tests for automaton projection
- [ ] solve first formula :)


# Problems
- [ ] union/intersection over different NFAs with different alphabets
- [ ] 
