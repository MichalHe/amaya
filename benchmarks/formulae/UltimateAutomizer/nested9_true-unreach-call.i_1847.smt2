(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info
  :source |
SMT script generated by Ultimate Automizer [1,2].
Ultimate Automizer is an automatic software verification tool that implements
a new automata-theoretic approach [3].

This SMT script belongs to a set of SMT scripts that was generated by applying
Ultimate Automizer to benchmarks from the SV-COMP 2015 [4,5] which are available 
at [6].

This script does _not_ contain all SMT commands that are used by Ultimate 
Automizer while verifying a program. In order to fulfill the restrictions of
the main track at SMT-COMP this script contains only the commands that are
sufficient to reproduce one single satisfiablity check.

2015-04-30, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)


[1] https://ultimate.informatik.uni-freiburg.de/automizer/
[2] Matthias Heizmann, Daniel Dietsch, Jan Leike, Betim Musa, Andreas Podelski:
Ultimate Automizer with Array Interpolation - (Competition Contribution). 
TACAS 2015: 455-457
[3] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski: Software Model 
Checking for People Who Love Automata. CAV 2013:36-52
[4] Dirk Beyer: Software Verification and Verifiable Witnesses - (Report on 
SV-COMP 2015). TACAS 2015: 401-416
[5] http://sv-comp.sosy-lab.org/2015/
[6] https://svn.sosy-lab.org/software/sv-benchmarks/tags/svcomp15/


Made compatible to SMT-COMP rules by SMTInterpol
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun c_main_~i~6 () Int)
(declare-fun c_main_~j~6 () Int)
(declare-fun c_main_~k~6 () Int)
(assert
 (and (<= c_main_~j~6 (+ (* 2 c_main_~i~6) 1)) 
 (<= c_main_~i~6 4)
 (exists ((v_nnf_100 Int))
  (and (<= (+ v_nnf_100 4) c_main_~k~6)
  (<= c_main_~j~6 (+ (* 2 v_nnf_100) 2)) 
  (<= v_nnf_100 4))) (<= c_main_~j~6 (+ (* 2 c_main_~i~6) 2))
 (<= c_main_~i~6 3)))
(assert
 (not
 (and (<= c_main_~j~6 (+ (* 2 c_main_~i~6) 1)) 
 (<= c_main_~i~6 4)
 (exists ((v_nnf_96 Int))
  (and (<= (+ v_nnf_96 2) c_main_~k~6) 
  (<= c_main_~j~6 (+ (* 2 v_nnf_96) 2)) 
  (<= v_nnf_96 4))) (<= c_main_~i~6 3))))
(check-sat)
(exit)

