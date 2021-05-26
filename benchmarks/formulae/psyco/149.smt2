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
(declare-fun W_S1_V4 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun R_E1_V4 () Bool)
(declare-fun R_E1_V2 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun DISJ_W_S1_R_E1 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun R_E1_V1 () Bool)
(assert
 (let
 (($x1610
   (forall
    ((V3_0 Int) (V2_0 Int) 
     (V4_0 Int) (MW_S1_V1 Bool) 
     (MW_S1_V3 Bool) (MW_S1_V2 Bool) 
     (MW_S1_V4 Bool) (S1_V3_!764 Int) 
     (S1_V3_!768 Int) (S1_V3_!774 Int) 
     (S1_V3_!779 Int) (S1_V4_!766 Int) 
     (S1_V4_!770 Int) (S1_V4_!776 Int) 
     (S1_V4_!781 Int) (S1_V1_!763 Int) 
     (S1_V1_!767 Int) (S1_V1_!773 Int) 
     (S1_V1_!778 Int) (S1_V2_!765 Int) 
     (S1_V2_!769 Int) (S1_V2_!775 Int) 
     (S1_V2_!780 Int) (E1_!762 Int) 
     (E1_!771 Int) (E1_!772 Int) 
     (E1_!777 Int) (E1_!782 Int))
    (let
    (($x604
      (= (ite MW_S1_V1 S1_V1_!767 (+ 1 (ite MW_S1_V1 S1_V1_!763 E1_!762)))
      (+ (- 1) (ite MW_S1_V2 S1_V2_!780 V2_0)))))
    (let
    (($x1290
      (and $x604
      (= (ite MW_S1_V3 S1_V3_!768 V3_0) (ite MW_S1_V3 S1_V3_!779 V3_0))
      (= (ite MW_S1_V2 S1_V2_!769 V2_0) (ite MW_S1_V2 S1_V2_!780 V2_0))
      (= (ite MW_S1_V4 S1_V4_!770 V4_0) (ite MW_S1_V4 S1_V4_!781 V4_0)))))
    (let
    (($x1066
      (<= E1_!782
      (+ (- 1)
      (ite MW_S1_V1 S1_V1_!778
      (+ (- 1) (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0))))))))
    (let
    (($x1192
      (>= (ite MW_S1_V1 S1_V1_!767 (+ 1 (ite MW_S1_V1 S1_V1_!763 E1_!762)))
      (+ (- 1) (ite MW_S1_V2 S1_V2_!769 V2_0)))))
    (let
    (($x971
      (and (not (<= V2_0 E1_!762))
      (not
      (<= (ite MW_S1_V2 S1_V2_!765 V2_0)
      (+ 1 (ite MW_S1_V1 S1_V1_!763 E1_!762)))) $x1192
      (not (<= V2_0 E1_!771)) 
      (>= V2_0 (+ 1 E1_!772))
      (>= (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0)) (+ 1 E1_!777))
      (not $x1066))))
    (let
    (($x1871
      (and
      (or (not R_E1_V3)
      (= (ite MW_S1_V3 S1_V3_!779 V3_0) (ite MW_S1_V3 S1_V3_!774 V3_0)))
      (or (not R_E1_V2)
      (= (ite MW_S1_V2 S1_V2_!780 V2_0) (ite MW_S1_V2 S1_V2_!775 V2_0)))
      (or (not R_E1_V4)
      (= (ite MW_S1_V4 S1_V4_!781 V4_0) (ite MW_S1_V4 S1_V4_!776 V4_0))))))
    (let
    (($x1287
      (and (or (not R_E1_V3) (= (ite MW_S1_V3 S1_V3_!779 V3_0) V3_0))
      (or (not R_E1_V2) (= (ite MW_S1_V2 S1_V2_!780 V2_0) V2_0))
      (or (not R_E1_V4) (= (ite MW_S1_V4 S1_V4_!781 V4_0) V4_0)))))
    (let (($x1714 (not $x1287)))
    (let
    (($x1532
      (and (or (not R_E1_V3) (= (ite MW_S1_V3 S1_V3_!774 V3_0) V3_0))
      (or (not R_E1_V2) (= (ite MW_S1_V2 S1_V2_!775 V2_0) V2_0))
      (or (not R_E1_V4) (= (ite MW_S1_V4 S1_V4_!776 V4_0) V4_0)))))
    (let (($x1798 (not $x1532)))
    (let
    (($x1775
      (and
      (or (not R_S1_V1) (= (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0)) V2_0))
      (or (not R_S1_V3) (= (ite MW_S1_V3 S1_V3_!774 V3_0) V3_0))
      (or (not R_S1_V2) (= (ite MW_S1_V2 S1_V2_!775 V2_0) V2_0))
      (or (not R_S1_V4) (= (ite MW_S1_V4 S1_V4_!776 V4_0) V4_0)))))
    (let (($x1803 (not $x1775)))
    (let (($x102 (not R_S1_V1)))
    (let
    (($x1078
      (or $x102
      (= (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0))
      (+ 2 (ite MW_S1_V1 S1_V1_!763 E1_!762))))))
    (let
    (($x1531
      (and $x1078
      (or (not R_S1_V3)
      (= (ite MW_S1_V3 S1_V3_!774 V3_0) (ite MW_S1_V3 S1_V3_!764 V3_0)))
      (or (not R_S1_V2)
      (= (ite MW_S1_V2 S1_V2_!775 V2_0) (ite MW_S1_V2 S1_V2_!765 V2_0)))
      (or (not R_S1_V4)
      (= (ite MW_S1_V4 S1_V4_!776 V4_0) (ite MW_S1_V4 S1_V4_!766 V4_0))))))
    (let
    (($x1499
      (and (or $x102 (= (ite MW_S1_V1 S1_V1_!763 E1_!762) (+ (- 2) V2_0)))
      (or (not R_S1_V3) (= (ite MW_S1_V3 S1_V3_!764 V3_0) V3_0))
      (or (not R_S1_V2) (= (ite MW_S1_V2 S1_V2_!765 V2_0) V2_0))
      (or (not R_S1_V4) (= (ite MW_S1_V4 S1_V4_!766 V4_0) V4_0)))))
    (let (($x1771 (not $x1499)))
    (let
    (($x1626
      (and
      (or $x102
      (= E1_!762 (+ (- 1) (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0)))))
      (or (not R_S1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!774 V3_0)))
      (or (not R_S1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!775 V2_0)))
      (or (not R_S1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!776 V4_0))))))
    (let
    (($x1145
      (and (or $x102 (= E1_!762 (+ 1 (ite MW_S1_V1 S1_V1_!763 E1_!762))))
      (or (not R_S1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!764 V3_0)))
      (or (not R_S1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!765 V2_0)))
      (or (not R_S1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!766 V4_0))))))
    (let
    (($x874
      (and
      (or $x102 (= (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0)) (+ 1 E1_!762)))
      (or (not R_S1_V3) (= (ite MW_S1_V3 S1_V3_!774 V3_0) V3_0))
      (or (not R_S1_V2) (= (ite MW_S1_V2 S1_V2_!775 V2_0) V2_0))
      (or (not R_S1_V4) (= (ite MW_S1_V4 S1_V4_!776 V4_0) V4_0)))))
    (let
    (($x1749
      (and (or $x102 (= V2_0 (+ 2 (ite MW_S1_V1 S1_V1_!763 E1_!762))))
      (or (not R_S1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!764 V3_0)))
      (or (not R_S1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!765 V2_0)))
      (or (not R_S1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!766 V4_0))))))
    (let
    (($x561
      (and (or $x102 (= (ite MW_S1_V1 S1_V1_!763 E1_!762) (+ (- 1) E1_!762)))
      (or (not R_S1_V3) (= (ite MW_S1_V3 S1_V3_!764 V3_0) V3_0))
      (or (not R_S1_V2) (= (ite MW_S1_V2 S1_V2_!765 V2_0) V2_0))
      (or (not R_S1_V4) (= (ite MW_S1_V4 S1_V4_!766 V4_0) V4_0)))))
    (let
    (($x1858
      (or $x102
      (= (ite MW_S1_V1 S1_V1_!763 E1_!762)
      (+ (- 2) (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0)))))))
    (let
    (($x1564
      (and $x1858
      (or (not R_S1_V3)
      (= (ite MW_S1_V3 S1_V3_!764 V3_0) (ite MW_S1_V3 S1_V3_!774 V3_0)))
      (or (not R_S1_V2)
      (= (ite MW_S1_V2 S1_V2_!765 V2_0) (ite MW_S1_V2 S1_V2_!775 V2_0)))
      (or (not R_S1_V4)
      (= (ite MW_S1_V4 S1_V4_!766 V4_0) (ite MW_S1_V4 S1_V4_!776 V4_0))))))
    (let
    (($x1766
      (and (or $x102 (= V2_0 (ite MW_S1_V1 S1_V1_!773 (+ (- 1) V2_0))))
      (or (not R_S1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!774 V3_0)))
      (or (not R_S1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!775 V2_0)))
      (or (not R_S1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!776 V4_0))))))
    (let
    (($x1530
      (and (or (not $x561) (= S1_V3_!768 S1_V3_!764))
      (or $x1771 (= S1_V3_!768 S1_V3_!774))
      (or (not $x1564) (= S1_V3_!768 S1_V3_!779))
      (or (not (or $x102 (= V2_0 (+ 1 E1_!762)))) (= S1_V3_!774 S1_V3_!764))
      (or (not $x1766) (= S1_V3_!774 S1_V3_!779))
      (or (not $x874) (= S1_V3_!779 S1_V3_!764))
      (or (not $x1145) (= S1_V4_!766 S1_V4_!770))
      (or (not (or $x102 (= E1_!762 (+ (- 1) V2_0))))
      (= S1_V4_!766 S1_V4_!776)) 
      (or (not $x1626) (= S1_V4_!766 S1_V4_!781))
      (or $x1771 (= S1_V4_!770 S1_V4_!776))
      (or (not $x1564) (= S1_V4_!770 S1_V4_!781))
      (or $x1803 (= S1_V4_!781 S1_V4_!776))
      (or (not $x561) (= S1_V1_!767 S1_V1_!763))
      (or (not (or $x102 (= V2_0 (+ 1 E1_!762)))) (= S1_V1_!773 S1_V1_!763))
      (or (not $x1749) (= S1_V1_!773 S1_V1_!767))
      (or (not $x874) (= S1_V1_!778 S1_V1_!763))
      (or (not $x1531) (= S1_V1_!778 S1_V1_!767))
      (or $x1803 (= S1_V1_!778 S1_V1_!773))
      (or (not $x1145) (= S1_V2_!765 S1_V2_!769))
      (or (not (or $x102 (= E1_!762 (+ (- 1) V2_0))))
      (= S1_V2_!765 S1_V2_!775)) 
      (or (not $x1626) (= S1_V2_!765 S1_V2_!780))
      (or $x1771 (= S1_V2_!769 S1_V2_!775))
      (or (not $x1531) (= S1_V2_!780 S1_V2_!769))
      (or $x1803 (= S1_V2_!780 S1_V2_!775)) 
      (= E1_!771 E1_!762) 
      (= E1_!772 E1_!762) 
      (= E1_!772 E1_!771) 
      (or $x1798 (= E1_!777 E1_!762)) 
      (or $x1798 (= E1_!777 E1_!771)) 
      (or $x1798 (= E1_!777 E1_!772)) 
      (or $x1714 (= E1_!782 E1_!762)) 
      (or $x1714 (= E1_!782 E1_!771)) 
      (or $x1714 (= E1_!782 E1_!772)) 
      (or (not $x1871) (= E1_!782 E1_!777)) 
      (or (not MW_S1_V1) W_S1_V1) 
      (not MW_S1_V2) (or (not MW_S1_V4) W_S1_V4))))
    (or (not $x1530) (not $x971) $x1290))))))))))))))))))))))))))))))
 (let
 (($x1795 (not (or (and W_S1_V1 R_S1_V1) R_S1_V3 (and W_S1_V4 R_S1_V4)))))
 (let
 (($x1524
   (or (and DISJ_W_S1_R_S1 DISJ_W_S1_R_E1) 
   (and (not W_S1_V1) DISJ_W_S1_R_E1) 
   (and (not R_S1_V1) DISJ_W_S1_R_S1))))
 (let (($x518 (not W_S1_V1)))
 (let (($x1770 (or DISJ_W_S1_R_E1 $x518)))
 (let (($x522 (not W_S1_V2)))
 (let (($x70 (not R_E1_V1)))
 (and $x70 $x522 $x1770 $x1524 W_S1_V3 
 (= DISJ_W_S1_R_S1 $x1795)
 (= DISJ_W_S1_R_E1 (not (or R_E1_V3 (and W_S1_V4 R_E1_V4)))) $x1610)))))))))
(check-sat)
(exit)

