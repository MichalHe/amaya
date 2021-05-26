(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info
  :source |
 Generated by PSyCO 0.1
 More info in N. P. Lopes and J. Monteiro. Weakest Precondition Synthesis for
 Compiler Optimizations, VMCAI'14.
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun W_S2_V5 () Bool)
(declare-fun W_S2_V2 () Bool)
(declare-fun W_S2_V3 () Bool)
(declare-fun W_S2_V1 () Bool)
(declare-fun W_S1_V4 () Bool)
(declare-fun W_S1_V5 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_E1_V4 () Bool)
(declare-fun R_E1_V5 () Bool)
(declare-fun R_E1_V2 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun DISJ_W_S2_R_E1 () Bool)
(declare-fun R_S2_V4 () Bool)
(declare-fun R_S2_V5 () Bool)
(declare-fun R_S2_V2 () Bool)
(declare-fun R_S2_V3 () Bool)
(declare-fun R_S2_V1 () Bool)
(declare-fun DISJ_W_S2_R_S2 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun R_S1_V5 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun DISJ_W_S2_R_S1 () Bool)
(declare-fun DISJ_W_S1_W_S2 () Bool)
(declare-fun DISJ_W_S1_R_E1 () Bool)
(declare-fun DISJ_W_S1_R_S2 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun W_S2_V4 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun R_E1_V1 () Bool)
(assert
 (let
 (($x2824
   (forall
    ((V3_0 Int) (V2_0 Int) 
     (V5_0 Int) (V4_0 Int) 
     (MW_S1_V1 Bool) (MW_S1_V3 Bool) 
     (MW_S1_V2 Bool) (MW_S1_V5 Bool) 
     (MW_S1_V4 Bool) (MW_S2_V1 Bool) 
     (MW_S2_V3 Bool) (MW_S2_V2 Bool) 
     (MW_S2_V5 Bool) (MW_S2_V4 Bool) 
     (S1_V1_!390 Int) (S1_V1_!397 Int) 
     (S2_V5_!405 Int) (S1_V3_!391 Int) 
     (S1_V3_!398 Int) (S1_V2_!392 Int) 
     (S1_V2_!399 Int) (E1_!389 Int) 
     (E1_!395 Int) (E1_!396 Int) 
     (S2_V4_!406 Int) (S1_V5_!393 Int) 
     (S1_V5_!400 Int) (S2_V1_!402 Int) 
     (S1_V4_!394 Int) (S1_V4_!401 Int) 
     (S2_V2_!404 Int) (S2_V3_!403 Int))
    (let
    (($x2597
      (and
      (= E1_!395
      (+ 1 (ite MW_S2_V1 S2_V1_!402 (ite MW_S1_V1 S1_V1_!397 E1_!396))))
      (= (ite MW_S1_V3 S1_V3_!391 V3_0)
      (ite MW_S2_V3 S2_V3_!403 (ite MW_S1_V3 S1_V3_!398 V3_0)))
      (= (ite MW_S1_V2 S1_V2_!392 V2_0)
      (ite MW_S2_V2 S2_V2_!404 (ite MW_S1_V2 S1_V2_!399 V2_0)))
      (= (ite MW_S1_V5 S1_V5_!393 V5_0)
      (ite MW_S2_V5 S2_V5_!405 (ite MW_S1_V5 S1_V5_!400 V5_0)))
      (= (ite MW_S1_V4 S1_V4_!394 V4_0)
      (ite MW_S2_V4 S2_V4_!406 (ite MW_S1_V4 S1_V4_!401 V4_0))))))
    (let
    (($x2595
      (>= (ite MW_S2_V1 S2_V1_!402 (ite MW_S1_V1 S1_V1_!397 E1_!396))
      (+ (- 1) (ite MW_S2_V2 S2_V2_!404 (ite MW_S1_V2 S1_V2_!399 V2_0))))))
    (let
    (($x2563
      (and (not (<= V2_0 E1_!389))
      (>= (ite MW_S1_V1 S1_V1_!390 E1_!389)
      (+ (- 1) (ite MW_S1_V2 S1_V2_!392 V2_0)))
      (>= E1_!395 (ite MW_S1_V2 S1_V2_!392 V2_0)) 
      (not (<= V2_0 E1_!396)) $x2595)))
    (let
    (($x2831
      (and (or (not R_E1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!391 V3_0)))
      (or (not R_E1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!392 V2_0)))
      (or (not R_E1_V5) (= V5_0 (ite MW_S1_V5 S1_V5_!393 V5_0)))
      (or (not R_E1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!394 V4_0))))))
    (let
    (($x2835
      (and
      (or (not (or (not R_S1_V1) (= E1_!389 E1_!396)))
      (= S1_V1_!390 S1_V1_!397))
      (or (not (or (not R_S1_V1) (= E1_!389 E1_!396)))
      (= S1_V3_!391 S1_V3_!398))
      (or (not (or (not R_S1_V1) (= E1_!396 E1_!389)))
      (= S1_V2_!399 S1_V2_!392)) 
      (or (not $x2831) (= E1_!389 E1_!395)) 
      (= E1_!396 E1_!389) 
      (or (not $x2831) (= E1_!396 E1_!395))
      (or (not (or (not R_S1_V1) (= E1_!389 E1_!396)))
      (= S1_V5_!393 S1_V5_!400))
      (or (not (or (not R_S1_V1) (= E1_!396 E1_!389)))
      (= S1_V4_!401 S1_V4_!394)) 
      (or (not MW_S1_V1) W_S1_V1) 
      (or (not MW_S1_V2) W_S1_V2) 
      (or (not MW_S1_V5) W_S1_V5) 
      (or (not MW_S1_V4) W_S1_V4) 
      (or (not MW_S2_V1) W_S2_V1) 
      (or (not MW_S2_V3) W_S2_V3) 
      (or (not MW_S2_V2) W_S2_V2) 
      (or (not MW_S2_V5) W_S2_V5)))) 
    (or (not $x2835) (not $x2563) $x2597)))))))))
 (let (($x90 (and W_S2_V5 R_E1_V5)))
 (let (($x89 (and W_S2_V2 R_E1_V2)))
 (let (($x88 (and W_S2_V3 R_E1_V3)))
 (let
 (($x113
   (or (and W_S2_V1 R_S2_V1) 
   (and W_S2_V3 R_S2_V3) (and W_S2_V2 R_S2_V2) 
   (and W_S2_V5 R_S2_V5) R_S2_V4)))
 (let (($x115 (= DISJ_W_S2_R_S2 (not $x113))))
 (let
 (($x110
   (or (and W_S2_V1 R_S1_V1) 
   (and W_S2_V3 R_S1_V3) (and W_S2_V2 R_S1_V2) 
   (and W_S2_V5 R_S1_V5) R_S1_V4)))
 (let (($x112 (= DISJ_W_S2_R_S1 (not $x110))))
 (let
 (($x107
   (or (and W_S1_V1 W_S2_V1) W_S2_V3 
   (and W_S1_V2 W_S2_V2) (and W_S1_V5 W_S2_V5) W_S1_V4)))
 (let (($x109 (= DISJ_W_S1_W_S2 (not $x107))))
 (let (($x51 (and W_S1_V4 R_E1_V4)))
 (let (($x49 (and W_S1_V5 R_E1_V5)))
 (let (($x47 (and W_S1_V2 R_E1_V2)))
 (let
 (($x101
   (or (and W_S1_V1 R_S2_V1) R_S2_V3 
   (and W_S1_V2 R_S2_V2) (and W_S1_V5 R_S2_V5) 
   (and W_S1_V4 R_S2_V4))))
 (let (($x103 (= DISJ_W_S1_R_S2 (not $x101))))
 (let
 (($x98
   (or (and W_S1_V1 R_S1_V1) R_S1_V3 
   (and W_S1_V2 R_S1_V2) (and W_S1_V5 R_S1_V5) 
   (and W_S1_V4 R_S1_V4))))
 (let (($x100 (= DISJ_W_S1_R_S1 (not $x98))))
 (let (($x153 (not R_E1_V1)))
 (and $x153 W_S1_V3 W_S2_V4 $x100 $x103
 (= DISJ_W_S1_R_E1 (not (or R_E1_V3 $x47 $x49 $x51))) $x109 $x112 $x115
 (= DISJ_W_S2_R_E1 (not (or $x88 $x89 $x90 R_E1_V4))) $x2824))))))))))))))))))))
(check-sat)
(exit)
