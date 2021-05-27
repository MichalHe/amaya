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
(declare-fun |old(~a29~0)| () Int)
(declare-fun ~a29~0 () Int)
(assert (not (exists ((v_~a29~0_1040 Int)) (let ((.cse0 (div v_~a29~0_1040 5))) (and (<= 0 v_~a29~0_1040) (<= v_~a29~0_1040 |old(~a29~0)|) (<= ~a29~0 (div (+ .cse0 (- 403019)) 5)) (<= 403019 .cse0))))))
(assert (not (exists ((v_~a29~0_1040 Int)) (let ((.cse0 (div v_~a29~0_1040 5))) (and (= (mod (+ .cse0 2) 5) 0) (<= ~a29~0 (div (+ .cse0 (- 403018)) 5)) (< v_~a29~0_1040 0) (<= v_~a29~0_1040 |old(~a29~0)|) (not (= (mod v_~a29~0_1040 5) 0)))))))
(assert (not (exists ((v_~a29~0_1040 Int)) (let ((.cse0 (div v_~a29~0_1040 5))) (and (<= 0 v_~a29~0_1040) (< .cse0 403019) (<= v_~a29~0_1040 |old(~a29~0)|) (<= ~a29~0 (+ (div (+ .cse0 (- 403019)) 5) 1)) (not (= 0 (mod (+ .cse0 1) 5))))))))
(assert (not (exists ((v_~a29~0_1040 Int)) (let ((.cse0 (div v_~a29~0_1040 5))) (and (<= ~a29~0 (+ (div (+ .cse0 (- 403018)) 5) 1)) (< v_~a29~0_1040 0) (<= v_~a29~0_1040 |old(~a29~0)|) (< .cse0 403018) (not (= (mod (+ .cse0 2) 5) 0)) (not (= (mod v_~a29~0_1040 5) 0)))))))
(assert (not (exists ((v_~a29~0_1040 Int)) (let ((.cse0 (div v_~a29~0_1040 5))) (and (<= v_~a29~0_1040 |old(~a29~0)|) (= 0 (mod (+ .cse0 1) 5)) (<= ~a29~0 (div (+ .cse0 (- 403019)) 5)) (= (mod v_~a29~0_1040 5) 0))))))
(assert (not (exists ((v_~a29~0_1040 Int)) (let ((.cse0 (div v_~a29~0_1040 5))) (and (<= 0 v_~a29~0_1040) (<= v_~a29~0_1040 |old(~a29~0)|) (= 0 (mod (+ .cse0 1) 5)) (<= ~a29~0 (div (+ .cse0 (- 403019)) 5)))))))
(assert (exists ((v_~a29~0_1040 Int)) (let ((.cse0 (div v_~a29~0_1040 5))) (and (< .cse0 403019) (<= v_~a29~0_1040 |old(~a29~0)|) (= (mod v_~a29~0_1040 5) 0) (<= ~a29~0 (+ (div (+ .cse0 (- 403019)) 5) 1)) (not (= 0 (mod (+ .cse0 1) 5)))))))
(check-sat)
(exit)
