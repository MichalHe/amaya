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
(set-info :status sat)
(declare-fun ~a1~0 () Int)
(declare-fun |old(~a1~0)| () Int)
(declare-fun |old(~a10~0)| () Int)
(assert
     (not
          (and
               (exists ((v_prenex_245 Int))
                    (and (<= (+ (div v_prenex_245 5) 449582) ~a1~0) (<= |old(~a1~0)| v_prenex_245) (< 218 v_prenex_245) (<= 0 v_prenex_245)))
               (<= |old(~a10~0)| 2))))
(assert
     (not
          (and 
               (<= |old(~a10~0)| 3)
               (exists ((v_prenex_250 Int)) 
                    (and (<= 0 v_prenex_250) (<= |old(~a1~0)| v_prenex_250) (<= (+ (div v_prenex_250 5) 449582) ~a1~0) (<= (+ v_prenex_250 13) 0))))))
(assert (not (and (<= |old(~a10~0)| 3) (exists ((v_prenex_247 Int)) (and (<= (+ (div v_prenex_247 5) 449582) ~a1~0) (= 0 (mod v_prenex_247 5)) (<= |old(~a1~0)| v_prenex_247) (<= (+ v_prenex_247 13) 0))))))
(assert (not (and (<= |old(~a10~0)| 2) (exists ((v_prenex_251 Int)) (and (< 38 v_prenex_251) (<= v_prenex_251 218) (<= |old(~a1~0)| v_prenex_251) (not (= 0 (mod v_prenex_251 5))) (< v_prenex_251 0) (<= (+ (div v_prenex_251 5) 449583) ~a1~0))))))
(assert (not (and (exists ((v_prenex_246 Int)) (and (< v_prenex_246 0) (< 218 v_prenex_246) (<= |old(~a1~0)| v_prenex_246) (not (= 0 (mod v_prenex_246 5))) (<= (+ (div v_prenex_246 5) 449583) ~a1~0))) (<= |old(~a10~0)| 2))))
(assert (not (and (<= |old(~a10~0)| 2) (exists ((v_prenex_248 Int)) (and (<= |old(~a1~0)| v_prenex_248) (<= (+ (div v_prenex_248 5) 449582) ~a1~0) (= 0 (mod v_prenex_248 5)) (< 218 v_prenex_248))))))
(assert (not (and (exists ((v_~a1~0_484 Int)) (and (<= |old(~a1~0)| v_~a1~0_484) (<= 0 v_~a1~0_484) (<= v_~a1~0_484 218) (< 38 v_~a1~0_484) (<= (+ (div v_~a1~0_484 5) 449582) ~a1~0))) (<= |old(~a10~0)| 2))))
(assert 
     (exists ((v_prenex_249 Int))
          (and (< v_prenex_249 0) (not (= 0 (mod v_prenex_249 5))) (<= |old(~a1~0)| v_prenex_249) (<= (+ (div v_prenex_249 5) 449583) ~a1~0) (<= (+ v_prenex_249 13) 0))))
(assert (<= |old(~a10~0)| 3))
(check-sat)
(exit)
