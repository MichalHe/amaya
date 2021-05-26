(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :category "industrial")
(set-info :status sat)
(assert (not (forall ((?X Int) (?Y Int) (?Z1 Int) (?Z2 Int)) (and (= (+ ?X ?Y) ?Z1) (= (- ?X ?Y) ?Z2) (< ?Z1 ?Z2)))))
(check-sat)
(exit)
