(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info :source "|
Generated by the tool Ultimate Automizer [1,2] which implements
an automata theoretic approach [3] to software verification.

This SMT script belongs to a set of SMT scripts that was generated by
applying Ultimate Automizer to benchmarks [4] from the SV-COMP 2019 [5,6].
This script might _not_ contain all SMT commands that are used by
Ultimate Automizer. In order to satisfy the restrictions of
the SMT-COMP we have to drop e.g., the commands for getting
values (resp. models), unsatisfiable cores and interpolants.

2019-04-27, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)

[1] https://ultimate.informatik.uni-freiburg.de/automizer/
[2] Matthias Heizmann, Yu-Fang Chen, Daniel Dietsch, Marius Greitschus,
     Jochen Hoenicke, Yong Li, Alexander Nutz, Betim Musa, Christian
     Schilling, Tanja Schindler, Andreas Podelski: Ultimate Automizer
     and the Search for Perfect Interpolants - (Competition Contribution).
     TACAS (2) 2018: 447-451
[3] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski: Software Model
     Checking for People Who Love Automata. CAV 2013:36-52
[4] https://github.com/sosy-lab/sv-benchmarks
[5] Dirk Beyer: Automatic Verification of C and Java Programs: SV-COMP 2019.
     TACAS (3) 2019: 133-155
[6] https://sv-comp.sosy-lab.org/2019/
|")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun |c_old(~a1~0)| () Int)
(declare-fun c_~a1~0 () Int)
(declare-fun c_~a10~0 () Int)
(declare-fun |c_main_#t~nondet2| () Int)
(declare-fun c_main_~input~0_primed () Int)
(assert (and (<= 0 (+ |c_main_#t~nondet2| 2147483648)) (= c_main_~input~0_primed |c_main_#t~nondet2|) (<= |c_main_#t~nondet2| 2147483647)))
(assert (and (exists ((v_prenex_243 Int) (v_~a1~0_482 Int)) (and (<= 23 v_~a1~0_482) (<= (mod v_prenex_243 299993) (+ c_~a1~0 300007)) (<= 0 v_prenex_243) (<= (+ (* 5 v_~a1~0_482) 517989) v_prenex_243))) (<= 3 c_~a10~0)))
(assert (not (let ((.cse0 (<= 3 c_~a10~0))) (or (and .cse0 (exists ((v_~a1~0_483 Int)) (let ((.cse1 (mod v_~a1~0_483 299993))) (and (<= |c_old(~a1~0)| v_~a1~0_483) (<= .cse1 (+ c_~a1~0 600000)) (not (= .cse1 0)) (< v_~a1~0_483 0))))) (and .cse0 (exists ((v_~a1~0_483 Int)) (and (<= |c_old(~a1~0)| v_~a1~0_483) (<= 0 v_~a1~0_483) (<= (mod v_~a1~0_483 299993) (+ c_~a1~0 300007)))))))))
(check-sat)
(exit)
