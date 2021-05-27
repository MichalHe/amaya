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
(declare-fun v_main_~x~0_BEFORE_CALL_5_const_-2050951247 () Int)
(declare-fun v_main_~y~0_BEFORE_CALL_5_const_-697640528 () Int)
(declare-fun v_main_~z~0_BEFORE_CALL_5_const_655670095 () Int)
(assert (and (exists ((|v_main_#t~nondet2_7| Int) (|v_main_#t~nondet2_8| Int) (|v_main_#t~nondet2_5| Int) (|v_main_#t~nondet2_6| Int)) (= v_main_~z~0_BEFORE_CALL_5_const_655670095 (+ (* 4194304 |v_main_#t~nondet2_7|) (* 4194304 |v_main_#t~nondet2_8|) (* 4194304 |v_main_#t~nondet2_5|) (* 4194304 |v_main_#t~nondet2_6|)))) (exists ((|v_main_#t~nondet1_8| Int) (|v_main_#t~nondet1_6| Int) (|v_main_#t~nondet1_7| Int) (|v_main_#t~nondet1_5| Int)) (= (+ (* 2097152 |v_main_#t~nondet1_8|) (* 2097152 |v_main_#t~nondet1_6|) (* 2097152 |v_main_#t~nondet1_7|) (* 2097152 |v_main_#t~nondet1_5|)) v_main_~y~0_BEFORE_CALL_5_const_-697640528)) (exists ((|v_main_#t~nondet0_7| Int) (|v_main_#t~nondet0_8| Int) (|v_main_#t~nondet0_5| Int) (|v_main_#t~nondet0_6| Int)) (= v_main_~x~0_BEFORE_CALL_5_const_-2050951247 (+ (* 1048576 |v_main_#t~nondet0_7|) (* 1048576 |v_main_#t~nondet0_8|) (* 1048576 |v_main_#t~nondet0_5|) (* 1048576 |v_main_#t~nondet0_6|)))) (= (mod (+ (* 4 v_main_~x~0_BEFORE_CALL_5_const_-2050951247) (* 4294967294 v_main_~y~0_BEFORE_CALL_5_const_-697640528) v_main_~z~0_BEFORE_CALL_5_const_655670095) 4294967296) 1048576)))
(check-sat)
(exit)
