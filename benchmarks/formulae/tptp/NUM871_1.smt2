(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :category "industrial")
(set-info :status sat)
(assert (not (exists ((?X Int) (?Y Int) (?Z Int) (?Z1 Int) (?Z2 Int) (?Z3 Int) (?Z4 Int)) (and (= (+ ?X ?Y) ?Z1) (= (+ ?Z1 ?Z) ?Z2) (= (+ ?Z ?X) ?Z3) (= (+ ?Z3 ?Y) ?Z4) (not (= ?Z2 ?Z4))))))
(check-sat)
(exit)
