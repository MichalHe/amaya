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
(declare-fun R_E1_V4 () Bool)
(declare-fun W_S1_V4 () Bool)
(declare-fun R_E1_V5 () Bool)
(declare-fun W_S1_V5 () Bool)
(declare-fun W_S2_V5 () Bool)
(declare-fun W_S2_V2 () Bool)
(declare-fun W_S2_V3 () Bool)
(declare-fun W_S2_V1 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun R_S2_V4 () Bool)
(declare-fun R_S2_V5 () Bool)
(declare-fun R_S2_V2 () Bool)
(declare-fun R_S2_V3 () Bool)
(declare-fun R_S2_V1 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_E1_V2 () Bool)
(declare-fun DISJ_W_S2_R_E1 () Bool)
(declare-fun DISJ_W_S2_R_S2 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun R_S1_V5 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun DISJ_W_S2_R_S1 () Bool)
(declare-fun DISJ_W_S1_W_S2 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun DISJ_W_S1_R_S2 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun W_S2_V4 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun R_E1_V1 () Bool)
(declare-fun DISJ_W_S1_R_E1 () Bool)
(assert
 (let
 (($x3108
   (forall
    ((V3_0 Int) (V2_0 Int) 
     (V5_0 Int) (V4_0 Int) 
     (MW_S1_V1 Bool) (MW_S1_V3 Bool) 
     (MW_S1_V2 Bool) (MW_S1_V5 Bool) 
     (MW_S1_V4 Bool) (MW_S2_V1 Bool) 
     (MW_S2_V3 Bool) (MW_S2_V2 Bool) 
     (MW_S2_V5 Bool) (MW_S2_V4 Bool) 
     (S1_V1_!1338 Int) (S1_V1_!1349 Int) 
     (S2_V5_!1346 Int) (S2_V5_!1358 Int) 
     (S1_V3_!1339 Int) (S1_V3_!1350 Int) 
     (S1_V2_!1340 Int) (S1_V2_!1351 Int) 
     (E1_!1337 Int) (E1_!1348 Int) 
     (E1_!1354 Int) (S2_V4_!1347 Int) 
     (S2_V4_!1359 Int) (S1_V5_!1341 Int) 
     (S1_V5_!1352 Int) (S2_V1_!1343 Int) 
     (S2_V1_!1355 Int) (S1_V4_!1342 Int) 
     (S1_V4_!1353 Int) (S2_V2_!1345 Int) 
     (S2_V2_!1357 Int) (S2_V3_!1344 Int) 
     (S2_V3_!1356 Int))
    (let
    (($x2629
      (= (ite MW_S2_V4 S2_V4_!1347 (ite MW_S1_V4 S1_V4_!1342 V4_0))
      (ite MW_S2_V4 S2_V4_!1359 (ite MW_S1_V4 S1_V4_!1353 V4_0)))))
    (let
    (($x2703
      (= (ite MW_S2_V5 S2_V5_!1346 (ite MW_S1_V5 S1_V5_!1341 V5_0))
      (ite MW_S2_V5 S2_V5_!1358 (ite MW_S1_V5 S1_V5_!1352 V5_0)))))
    (let
    (($x2200
      (= (ite MW_S2_V2 S2_V2_!1345 (ite MW_S1_V2 S1_V2_!1340 V2_0))
      (ite MW_S2_V2 S2_V2_!1357 (ite MW_S1_V2 S1_V2_!1351 V2_0)))))
    (let
    (($x2625
      (= (ite MW_S2_V3 S2_V3_!1344 (ite MW_S1_V3 S1_V3_!1339 V3_0))
      (ite MW_S2_V3 S2_V3_!1356 (ite MW_S1_V3 S1_V3_!1350 V3_0)))))
    (let
    (($x2684
      (and
      (= (ite MW_S2_V1 S2_V1_!1343 (ite MW_S1_V1 S1_V1_!1338 E1_!1337))
      (ite MW_S2_V1 S2_V1_!1355 E1_!1354)) $x2625 $x2200 $x2703 $x2629)))
    (let
    (($x2524
      (>= (ite MW_S2_V1 S2_V1_!1355 E1_!1354)
      (+ (- 1) (ite MW_S2_V2 S2_V2_!1357 (ite MW_S1_V2 S1_V2_!1351 V2_0))))))
    (let
    (($x2830
      (>= (ite MW_S2_V1 S2_V1_!1343 (ite MW_S1_V1 S1_V1_!1338 E1_!1337))
      (+ (- 1) (ite MW_S2_V2 S2_V2_!1345 (ite MW_S1_V2 S1_V2_!1340 V2_0))))))
    (let
    (($x2902
      (and (not (<= V2_0 E1_!1337)) $x2830 
      (not (<= V2_0 E1_!1348))
      (>= (ite MW_S1_V1 S1_V1_!1349 E1_!1348)
      (+ (- 1) (ite MW_S1_V2 S1_V2_!1351 V2_0)))
      (not (<= (ite MW_S1_V2 S1_V2_!1351 V2_0) E1_!1354)) $x2524)))
    (let
    (($x2442
      (and
      (or (not R_S2_V1) (= E1_!1354 (ite MW_S1_V1 S1_V1_!1338 E1_!1337)))
      (or (not R_S2_V3)
      (= (ite MW_S1_V3 S1_V3_!1350 V3_0) (ite MW_S1_V3 S1_V3_!1339 V3_0)))
      (or (not R_S2_V2)
      (= (ite MW_S1_V2 S1_V2_!1351 V2_0) (ite MW_S1_V2 S1_V2_!1340 V2_0)))
      (or (not R_S2_V5)
      (= (ite MW_S1_V5 S1_V5_!1352 V5_0) (ite MW_S1_V5 S1_V5_!1341 V5_0)))
      (or (not R_S2_V4)
      (= (ite MW_S1_V4 S1_V4_!1353 V4_0) (ite MW_S1_V4 S1_V4_!1342 V4_0))))))
    (let (($x2453 (not $x2442)))
    (let
    (($x2477
      (and
      (or (not R_S2_V1) (= (ite MW_S1_V1 S1_V1_!1338 E1_!1337) E1_!1354))
      (or (not R_S2_V3)
      (= (ite MW_S1_V3 S1_V3_!1339 V3_0) (ite MW_S1_V3 S1_V3_!1350 V3_0)))
      (or (not R_S2_V2)
      (= (ite MW_S1_V2 S1_V2_!1340 V2_0) (ite MW_S1_V2 S1_V2_!1351 V2_0)))
      (or (not R_S2_V5)
      (= (ite MW_S1_V5 S1_V5_!1341 V5_0) (ite MW_S1_V5 S1_V5_!1352 V5_0)))
      (or (not R_S2_V4)
      (= (ite MW_S1_V4 S1_V4_!1342 V4_0) (ite MW_S1_V4 S1_V4_!1353 V4_0))))))
    (let
    (($x2858
      (and (or (not R_E1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!1351 V2_0)))
      (or (not R_E1_V5) (= V5_0 (ite MW_S1_V5 S1_V5_!1352 V5_0)))
      (or (not R_E1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!1353 V4_0))))))
    (let
    (($x2615
      (and
      (or (not (or (not R_S1_V1) (= E1_!1337 E1_!1348)))
      (= S1_V1_!1338 S1_V1_!1349)) 
      (or $x2453 (= S2_V5_!1358 S2_V5_!1346))
      (or (not (or (not R_S1_V1) (= E1_!1337 E1_!1348)))
      (= S1_V3_!1339 S1_V3_!1350))
      (or (not (or (not R_S1_V1) (= E1_!1337 E1_!1348)))
      (= S1_V2_!1340 S1_V2_!1351)) 
      (= E1_!1337 E1_!1348) 
      (or (not $x2858) (= E1_!1337 E1_!1354))
      (or (not $x2858) (= E1_!1348 E1_!1354))
      (or (not $x2477) (= S2_V4_!1347 S2_V4_!1359))
      (or (not (or (not R_S1_V1) (= E1_!1337 E1_!1348)))
      (= S1_V5_!1341 S1_V5_!1352)) 
      (or $x2453 (= S2_V1_!1355 S2_V1_!1343))
      (or (not (or (not R_S1_V1) (= E1_!1348 E1_!1337)))
      (= S1_V4_!1353 S1_V4_!1342))
      (or (not $x2477) (= S2_V2_!1345 S2_V2_!1357))
      (or $x2453 (= S2_V3_!1356 S2_V3_!1344)) 
      (or (not MW_S1_V1) W_S1_V1) 
      (not MW_S1_V2) (or (not MW_S1_V5) W_S1_V5) 
      (or (not MW_S1_V4) W_S1_V4) 
      (or (not MW_S2_V1) W_S2_V1) 
      (or (not MW_S2_V3) W_S2_V3) 
      (or (not MW_S2_V2) W_S2_V2) 
      (or (not MW_S2_V5) W_S2_V5)))) 
    (or (not $x2615) (not $x2902) $x2684)))))))))))))))))
 (let
 (($x3012 (not (or (and W_S2_V2 R_E1_V2) (and W_S2_V5 R_E1_V5) R_E1_V4))))
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
 (let (($x63 (and W_S1_V5 W_S2_V5)))
 (let (($x57 (and W_S1_V1 W_S2_V1)))
 (let (($x152 (not R_E1_V3)))
 (let (($x37 (and W_S1_V4 R_S2_V4)))
 (let (($x35 (and W_S1_V5 R_S2_V5)))
 (let (($x29 (and W_S1_V1 R_S2_V1)))
 (let (($x23 (and W_S1_V4 R_S1_V4)))
 (let (($x20 (and W_S1_V5 R_S1_V5)))
 (let (($x12 (and W_S1_V1 R_S1_V1)))
 (let (($x2209 (not W_S1_V2)))
 (let (($x150 (not R_E1_V1)))
 (and DISJ_W_S1_R_E1 $x150 $x2209 W_S1_V3 W_S2_V4
 (= DISJ_W_S1_R_S1 (not (or $x12 R_S1_V3 $x20 $x23)))
 (= DISJ_W_S1_R_S2 (not (or $x29 R_S2_V3 $x35 $x37))) $x152
 (= DISJ_W_S1_W_S2 (not (or $x57 W_S2_V3 $x63 W_S1_V4))) $x112 $x115
 (= DISJ_W_S2_R_E1 $x3012) $x3108 
 (not (and W_S1_V5 R_E1_V5)) 
 (not (and W_S1_V4 R_E1_V4)))))))))))))))))))))
(check-sat)
(exit)
