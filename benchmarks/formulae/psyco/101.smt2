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
(declare-fun R_S2_V4 () Bool)
(declare-fun R_S2_V5 () Bool)
(declare-fun R_S2_V2 () Bool)
(declare-fun R_S2_V3 () Bool)
(declare-fun R_S2_V1 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun R_S1_V5 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_E1_V2 () Bool)
(declare-fun DISJ_W_S2_R_E1 () Bool)
(declare-fun DISJ_W_S2_R_S2 () Bool)
(declare-fun DISJ_W_S2_R_S1 () Bool)
(declare-fun DISJ_W_S1_W_S2 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun DISJ_W_S1_R_S2 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun W_S2_V4 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun R_E1_V1 () Bool)
(declare-fun DISJ_W_S1_R_E1 () Bool)
(assert
 (let
 (($x5110
   (forall
    ((V3_0 Int) (V2_0 Int) 
     (V5_0 Int) (V4_0 Int) 
     (MW_S1_V1 Bool) (MW_S1_V3 Bool) 
     (MW_S1_V2 Bool) (MW_S1_V5 Bool) 
     (MW_S1_V4 Bool) (MW_S2_V1 Bool) 
     (MW_S2_V3 Bool) (MW_S2_V2 Bool) 
     (MW_S2_V5 Bool) (MW_S2_V4 Bool) 
     (S1_V1_!6442 Int) (S1_V1_!6447 Int) 
     (S1_V1_!6464 Int) (S1_V1_!6474 Int) 
     (S2_V5_!6456 Int) (S2_V5_!6461 Int) 
     (S2_V5_!6472 Int) (S2_V5_!6482 Int) 
     (S1_V3_!6443 Int) (S1_V3_!6448 Int) 
     (S1_V3_!6465 Int) (S1_V3_!6475 Int) 
     (S1_V2_!6444 Int) (S1_V2_!6449 Int) 
     (S1_V2_!6466 Int) (S1_V2_!6476 Int) 
     (E1_!6441 Int) (E1_!6452 Int) 
     (E1_!6463 Int) (S2_V4_!6457 Int) 
     (S2_V4_!6462 Int) (S2_V4_!6473 Int) 
     (S2_V4_!6483 Int) (S1_V5_!6445 Int) 
     (S1_V5_!6450 Int) (S1_V5_!6467 Int) 
     (S1_V5_!6477 Int) (S2_V1_!6453 Int) 
     (S2_V1_!6458 Int) (S2_V1_!6469 Int) 
     (S2_V1_!6479 Int) (S1_V4_!6446 Int) 
     (S1_V4_!6451 Int) (S1_V4_!6468 Int) 
     (S1_V4_!6478 Int) (S2_V2_!6455 Int) 
     (S2_V2_!6460 Int) (S2_V2_!6471 Int) 
     (S2_V2_!6481 Int) (S2_V3_!6454 Int) 
     (S2_V3_!6459 Int) (S2_V3_!6470 Int) 
     (S2_V3_!6480 Int))
    (let
    (($x2611
      (= (ite MW_S2_V4 S2_V4_!6462 (ite MW_S1_V4 S1_V4_!6451 V4_0))
      (ite MW_S2_V4 S2_V4_!6483
      (ite MW_S1_V4 S1_V4_!6478
      (ite MW_S2_V4 S2_V4_!6473 (ite MW_S1_V4 S1_V4_!6468 V4_0)))))))
    (let
    (($x3779
      (= (ite MW_S2_V5 S2_V5_!6461 (ite MW_S1_V5 S1_V5_!6450 V5_0))
      (ite MW_S2_V5 S2_V5_!6482
      (ite MW_S1_V5 S1_V5_!6477
      (ite MW_S2_V5 S2_V5_!6472 (ite MW_S1_V5 S1_V5_!6467 V5_0)))))))
    (let ((?x4224 (ite MW_S1_V2 S1_V2_!6466 V2_0)))
    (let ((?x3664 (ite MW_S2_V2 S2_V2_!6471 ?x4224)))
    (let ((?x2481 (ite MW_S1_V2 S1_V2_!6476 ?x3664)))
    (let ((?x3727 (ite MW_S2_V2 S2_V2_!6481 ?x2481)))
    (let ((?x3208 (ite MW_S1_V2 S1_V2_!6449 V2_0)))
    (let ((?x4184 (ite MW_S2_V2 S2_V2_!6460 ?x3208)))
    (let (($x3858 (= ?x4184 ?x3727)))
    (let
    (($x4130
      (= (ite MW_S2_V3 S2_V3_!6459 (ite MW_S1_V3 S1_V3_!6448 V3_0))
      (ite MW_S2_V3 S2_V3_!6480
      (ite MW_S1_V3 S1_V3_!6475
      (ite MW_S2_V3 S2_V3_!6470 (ite MW_S1_V3 S1_V3_!6465 V3_0)))))))
    (let ((?x3364 (ite MW_S1_V1 S1_V1_!6464 E1_!6463)))
    (let ((?x3808 (ite MW_S2_V1 S2_V1_!6469 ?x3364)))
    (let ((?x3750 (+ 1 ?x3808)))
    (let ((?x3590 (ite MW_S1_V1 S1_V1_!6474 ?x3750)))
    (let ((?x2995 (ite MW_S2_V1 S2_V1_!6479 ?x3590)))
    (let ((?x3574 (ite MW_S2_V1 S2_V1_!6453 E1_!6452)))
    (let ((?x2657 (+ 1 ?x3574)))
    (let ((?x3058 (ite MW_S2_V1 S2_V1_!6458 ?x2657)))
    (let (($x2870 (= ?x3058 ?x2995)))
    (let
    (($x3485
      (and (not (<= V2_0 E1_!6441))
      (not
      (<= (ite MW_S1_V2 S1_V2_!6444 V2_0)
      (+ 1 (ite MW_S1_V1 S1_V1_!6442 E1_!6441))))
      (>=
      (ite MW_S1_V1 S1_V1_!6447 (+ 1 (ite MW_S1_V1 S1_V1_!6442 E1_!6441)))
      (+ (- 1) ?x3208)) (not (<= ?x3208 E1_!6452))
      (not (<= (ite MW_S2_V2 S2_V2_!6455 ?x3208) ?x2657))
      (>= ?x3058 (+ (- 1) ?x4184)) 
      (not (<= V2_0 E1_!6463)) 
      (not (<= ?x3664 ?x3750)) 
      (>= ?x2995 (+ (- 1) ?x3727)))))
    (let (($x3236 (or (not MW_S2_V5) W_S2_V5)))
    (let (($x3809 (or (not MW_S2_V2) W_S2_V2)))
    (let (($x3261 (or (not MW_S2_V3) W_S2_V3)))
    (let (($x2820 (or (not MW_S2_V1) W_S2_V1)))
    (let (($x2511 (or (not MW_S1_V4) W_S1_V4)))
    (let (($x3174 (or (not MW_S1_V5) W_S1_V5)))
    (let (($x3229 (= S2_V3_!6470 S2_V3_!6480)))
    (let ((?x2628 (ite MW_S1_V4 S1_V4_!6468 V4_0)))
    (let ((?x2734 (ite MW_S2_V4 S2_V4_!6473 ?x2628)))
    (let ((?x3570 (ite MW_S1_V4 S1_V4_!6478 ?x2734)))
    (let (($x407 (not R_S2_V4)))
    (let (($x2789 (or $x407 (= ?x2628 ?x3570))))
    (let ((?x3011 (ite MW_S1_V5 S1_V5_!6467 V5_0)))
    (let ((?x3212 (ite MW_S2_V5 S2_V5_!6472 ?x3011)))
    (let ((?x4195 (ite MW_S1_V5 S1_V5_!6477 ?x3212)))
    (let (($x405 (not R_S2_V5)))
    (let (($x2811 (or $x405 (= ?x3011 ?x4195))))
    (let (($x403 (not R_S2_V2)))
    (let (($x2572 (or $x403 (= ?x4224 ?x2481))))
    (let ((?x3297 (ite MW_S1_V3 S1_V3_!6465 V3_0)))
    (let ((?x4222 (ite MW_S2_V3 S2_V3_!6470 ?x3297)))
    (let ((?x3057 (ite MW_S1_V3 S1_V3_!6475 ?x4222)))
    (let (($x401 (not R_S2_V3)))
    (let (($x2708 (or $x401 (= ?x3297 ?x3057))))
    (let (($x398 (not R_S2_V1)))
    (let (($x3165 (or $x398 (= ?x3364 ?x3590))))
    (let (($x3998 (not (and $x3165 $x2708 $x2572 $x2811 $x2789))))
    (let (($x4031 (= S2_V3_!6470 S2_V3_!6454)))
    (let (($x2480 (or $x407 (= ?x2628 (ite MW_S1_V4 S1_V4_!6451 V4_0)))))
    (let (($x2712 (or $x405 (= ?x3011 (ite MW_S1_V5 S1_V5_!6450 V5_0)))))
    (let (($x2665 (or $x403 (= ?x4224 ?x3208))))
    (let (($x2869 (or $x401 (= ?x3297 (ite MW_S1_V3 S1_V3_!6448 V3_0)))))
    (let (($x3527 (or $x398 (= ?x3364 E1_!6452))))
    (let (($x2497 (not (and $x3527 $x2869 $x2665 $x2712 $x2480))))
    (let (($x2988 (= S2_V3_!6459 S2_V3_!6480)))
    (let
    (($x3317
      (or $x407
      (= (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0)) ?x3570))))
    (let
    (($x4001
      (or $x405
      (= (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0)) ?x4195))))
    (let (($x2730 (or $x403 (= (ite MW_S2_V2 S2_V2_!6455 ?x3208) ?x2481))))
    (let
    (($x2688
      (or $x401
      (= (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0)) ?x3057))))
    (let
    (($x2506
      (not
      (and (or $x398 (= ?x3574 (+ (- 1) ?x3590))) $x2688 $x2730 $x4001
      $x3317))))
    (let (($x3427 (= S2_V3_!6459 S2_V3_!6470)))
    (let
    (($x2646
      (or $x407
      (= (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0)) ?x2628))))
    (let
    (($x2565
      (or $x405
      (= (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0)) ?x3011))))
    (let (($x3444 (or $x403 (= (ite MW_S2_V2 S2_V2_!6455 ?x3208) ?x4224))))
    (let
    (($x3676
      (or $x401
      (= (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0)) ?x3297))))
    (let
    (($x2604
      (not
      (and (or $x398 (= ?x3574 (+ (- 1) ?x3364))) $x3676 $x3444 $x2565
      $x2646))))
    (let (($x2451 (= S2_V3_!6459 S2_V3_!6454)))
    (let
    (($x3060
      (or $x407
      (= (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0))
      (ite MW_S1_V4 S1_V4_!6451 V4_0)))))
    (let
    (($x2918
      (or $x405
      (= (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0))
      (ite MW_S1_V5 S1_V5_!6450 V5_0)))))
    (let (($x3009 (or $x403 (= (ite MW_S2_V2 S2_V2_!6455 ?x3208) ?x3208))))
    (let
    (($x2528
      (or $x401
      (= (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0))
      (ite MW_S1_V3 S1_V3_!6448 V3_0)))))
    (let
    (($x3068
      (not
      (and (or $x398 (= ?x3574 (+ (- 1) E1_!6452))) $x2528 $x3009 $x2918
      $x3060))))
    (let (($x3348 (= S2_V3_!6454 S2_V3_!6480)))
    (let (($x2526 (or $x407 (= (ite MW_S1_V4 S1_V4_!6451 V4_0) ?x3570))))
    (let (($x2950 (or $x405 (= (ite MW_S1_V5 S1_V5_!6450 V5_0) ?x4195))))
    (let (($x2592 (or $x403 (= ?x3208 ?x2481))))
    (let (($x3267 (or $x401 (= (ite MW_S1_V3 S1_V3_!6448 V3_0) ?x3057))))
    (let (($x3177 (or $x398 (= E1_!6452 ?x3590))))
    (let (($x2722 (= S2_V2_!6481 S2_V2_!6460)))
    (let
    (($x4063
      (or $x407
      (= ?x3570 (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0))))))
    (let
    (($x3032
      (or $x405
      (= ?x4195 (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0))))))
    (let (($x3023 (or $x403 (= ?x2481 (ite MW_S2_V2 S2_V2_!6455 ?x3208)))))
    (let
    (($x2834
      (or $x401
      (= ?x3057 (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0))))))
    (let (($x2640 (= S2_V2_!6481 S2_V2_!6455)))
    (let (($x3109 (or $x407 (= ?x3570 (ite MW_S1_V4 S1_V4_!6451 V4_0)))))
    (let (($x2871 (or $x405 (= ?x4195 (ite MW_S1_V5 S1_V5_!6450 V5_0)))))
    (let (($x2683 (or $x403 (= ?x2481 ?x3208))))
    (let (($x2875 (or $x401 (= ?x3057 (ite MW_S1_V3 S1_V3_!6448 V3_0)))))
    (let (($x2695 (or $x398 (= ?x3590 E1_!6452))))
    (let (($x2990 (not (and $x2695 $x2875 $x2683 $x2871 $x3109))))
    (let (($x3097 (= S2_V2_!6471 S2_V2_!6460)))
    (let
    (($x3343
      (or $x407
      (= ?x2628 (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0))))))
    (let
    (($x3456
      (or $x405
      (= ?x3011 (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0))))))
    (let (($x2910 (or $x403 (= ?x4224 (ite MW_S2_V2 S2_V2_!6455 ?x3208)))))
    (let
    (($x2607
      (or $x401
      (= ?x3297 (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0))))))
    (let (($x4017 (= S1_V4_!6478 S1_V4_!6451)))
    (let (($x206 (not R_S1_V4)))
    (let (($x2709 (or $x206 (= ?x2734 (ite MW_S1_V4 S1_V4_!6446 V4_0)))))
    (let (($x204 (not R_S1_V5)))
    (let (($x2856 (or $x204 (= ?x3212 (ite MW_S1_V5 S1_V5_!6445 V5_0)))))
    (let (($x202 (not R_S1_V2)))
    (let (($x2650 (or $x202 (= ?x3664 (ite MW_S1_V2 S1_V2_!6444 V2_0)))))
    (let (($x200 (not R_S1_V3)))
    (let (($x2556 (or $x200 (= ?x4222 (ite MW_S1_V3 S1_V3_!6443 V3_0)))))
    (let (($x198 (not R_S1_V1)))
    (let (($x3467 (or $x198 (= ?x3808 (ite MW_S1_V1 S1_V1_!6442 E1_!6441)))))
    (let (($x3252 (not (and $x3467 $x2556 $x2650 $x2856 $x2709))))
    (let (($x3378 (= S1_V4_!6468 S1_V4_!6478)))
    (let (($x2831 (or $x206 (= V4_0 ?x2734))))
    (let (($x2748 (or $x204 (= V5_0 ?x3212))))
    (let (($x2913 (or $x202 (= V2_0 ?x3664))))
    (let (($x3392 (or $x200 (= V3_0 ?x4222))))
    (let (($x2720 (= S1_V4_!6468 S1_V4_!6451)))
    (let (($x3213 (or $x206 (= V4_0 (ite MW_S1_V4 S1_V4_!6446 V4_0)))))
    (let (($x2976 (or $x204 (= V5_0 (ite MW_S1_V5 S1_V5_!6445 V5_0)))))
    (let (($x2702 (or $x202 (= V2_0 (ite MW_S1_V2 S1_V2_!6444 V2_0)))))
    (let (($x2934 (or $x200 (= V3_0 (ite MW_S1_V3 S1_V3_!6443 V3_0)))))
    (let
    (($x2750
      (and (or $x198 (= E1_!6463 (+ 1 (ite MW_S1_V1 S1_V1_!6442 E1_!6441))))
      $x2934 $x2702 $x2976 $x3213)))
    (let (($x3557 (not (or $x198 (= E1_!6463 E1_!6441)))))
    (let (($x3455 (or $x3557 (= S1_V4_!6468 S1_V4_!6446))))
    (let (($x3906 (= S1_V4_!6446 S1_V4_!6478)))
    (let (($x2507 (= S1_V4_!6446 S1_V4_!6451)))
    (let
    (($x2660
      (and (or $x198 (= E1_!6441 (+ 1 (ite MW_S1_V1 S1_V1_!6442 E1_!6441))))
      $x2934 $x2702 $x2976 $x3213)))
    (let (($x2431 (= S1_V5_!6477 S1_V5_!6467)))
    (let (($x3682 (or $x206 (= ?x2734 V4_0))))
    (let (($x3396 (or $x204 (= ?x3212 V5_0))))
    (let (($x3401 (or $x202 (= ?x3664 V2_0))))
    (let (($x3321 (or $x200 (= ?x4222 V3_0))))
    (let
    (($x2691
      (not
      (and (or $x198 (= ?x3808 (+ (- 1) E1_!6463))) $x3321 $x3401 $x3396
      $x3682))))
    (let (($x3380 (= S1_V5_!6477 S1_V5_!6445)))
    (let
    (($x3147
      (not
      (and (or $x198 (= ?x3808 (+ (- 1) E1_!6441))) $x3321 $x3401 $x3396
      $x3682))))
    (let (($x3454 (or $x3557 (= S1_V5_!6467 S1_V5_!6445))))
    (let (($x2603 (= S2_V4_!6483 S2_V4_!6473)))
    (let (($x3181 (or $x407 (= ?x3570 ?x2628))))
    (let (($x3507 (or $x405 (= ?x4195 ?x3011))))
    (let (($x2956 (or $x403 (= ?x2481 ?x4224))))
    (let (($x2715 (or $x401 (= ?x3057 ?x3297))))
    (let (($x2458 (or $x398 (= ?x3590 ?x3364))))
    (let (($x2891 (= E1_!6452 E1_!6463)))
    (let (($x161 (not R_E1_V4)))
    (let (($x3088 (or $x161 (= (ite MW_S1_V4 S1_V4_!6451 V4_0) V4_0))))
    (let (($x159 (not R_E1_V5)))
    (let (($x3440 (or $x159 (= (ite MW_S1_V5 S1_V5_!6450 V5_0) V5_0))))
    (let (($x157 (not R_E1_V2)))
    (let (($x2776 (or $x157 (= ?x3208 V2_0))))
    (let (($x3713 (= E1_!6441 E1_!6463)))
    (let (($x4052 (= E1_!6441 E1_!6452)))
    (let (($x2566 (or $x161 (= V4_0 (ite MW_S1_V4 S1_V4_!6451 V4_0)))))
    (let (($x2656 (or $x159 (= V5_0 (ite MW_S1_V5 S1_V5_!6450 V5_0)))))
    (let (($x3506 (or $x157 (= V2_0 ?x3208))))
    (let (($x2539 (= S1_V2_!6449 S1_V2_!6476)))
    (let (($x3303 (or $x206 (= (ite MW_S1_V4 S1_V4_!6446 V4_0) ?x2734))))
    (let (($x3283 (or $x204 (= (ite MW_S1_V5 S1_V5_!6445 V5_0) ?x3212))))
    (let (($x3434 (or $x202 (= (ite MW_S1_V2 S1_V2_!6444 V2_0) ?x3664))))
    (let (($x3478 (or $x200 (= (ite MW_S1_V3 S1_V3_!6443 V3_0) ?x4222))))
    (let (($x2931 (or $x198 (= (ite MW_S1_V1 S1_V1_!6442 E1_!6441) ?x3808))))
    (let (($x2775 (= S1_V2_!6449 S1_V2_!6466)))
    (let (($x2815 (or $x206 (= (ite MW_S1_V4 S1_V4_!6446 V4_0) V4_0))))
    (let (($x2673 (or $x204 (= (ite MW_S1_V5 S1_V5_!6445 V5_0) V5_0))))
    (let (($x2922 (or $x202 (= (ite MW_S1_V2 S1_V2_!6444 V2_0) V2_0))))
    (let (($x2957 (or $x200 (= (ite MW_S1_V3 S1_V3_!6443 V3_0) V3_0))))
    (let
    (($x3315
      (and
      (or $x198 (= (ite MW_S1_V1 S1_V1_!6442 E1_!6441) (+ (- 1) E1_!6463)))
      $x2957 $x2922 $x2673 $x2815)))
    (let (($x2821 (not $x3315)))
    (let (($x3285 (= S1_V2_!6449 S1_V2_!6444)))
    (let
    (($x2925
      (and
      (or $x198 (= (ite MW_S1_V1 S1_V1_!6442 E1_!6441) (+ (- 1) E1_!6441)))
      $x2957 $x2922 $x2673 $x2815)))
    (let (($x3327 (not $x2925)))
    (let (($x3018 (not (or $x198 $x3713))))
    (let (($x2991 (or $x3018 (= S1_V2_!6444 S1_V2_!6466))))
    (let (($x2801 (= S1_V3_!6465 S1_V3_!6475)))
    (let (($x2553 (= S1_V3_!6443 S1_V3_!6475)))
    (let (($x2475 (or $x3018 (= S1_V3_!6443 S1_V3_!6465))))
    (let (($x2900 (= S2_V5_!6456 S2_V5_!6472)))
    (let (($x2453 (or $x407 (= (ite MW_S1_V4 S1_V4_!6451 V4_0) ?x2628))))
    (let (($x3924 (or $x405 (= (ite MW_S1_V5 S1_V5_!6450 V5_0) ?x3011))))
    (let (($x2886 (or $x403 (= ?x3208 ?x4224))))
    (let (($x3099 (or $x401 (= (ite MW_S1_V3 S1_V3_!6448 V3_0) ?x3297))))
    (let (($x3038 (or $x398 (= E1_!6452 ?x3364))))
    (let (($x2933 (or $x3018 (= S1_V1_!6442 S1_V1_!6464))))
    (let
    (($x3828
      (and $x2933 (or $x3327 (= S1_V1_!6447 S1_V1_!6442))
      (or $x2821 (= S1_V1_!6447 S1_V1_!6464))
      (or $x3147 (= S1_V1_!6474 S1_V1_!6442))
      (or $x3252 (= S1_V1_!6474 S1_V1_!6447))
      (or $x2691 (= S1_V1_!6474 S1_V1_!6464))
      (or (not (and $x3038 $x3099 $x2886 $x3924 $x2453)) $x2900)
      (or (not (and $x3177 $x3267 $x2592 $x2950 $x2526))
      (= S2_V5_!6456 S2_V5_!6482)) 
      (or $x3068 (= S2_V5_!6461 S2_V5_!6456))
      (or $x2604 (= S2_V5_!6461 S2_V5_!6472))
      (or $x2506 (= S2_V5_!6461 S2_V5_!6482))
      (or $x3998 (= S2_V5_!6472 S2_V5_!6482)) $x2475
      (or
      (not (and (or $x198 (= E1_!6441 ?x3750)) $x3392 $x2913 $x2748 $x2831))
      $x2553) (or $x3327 (= S1_V3_!6448 S1_V3_!6443))
      (or $x2821 (= S1_V3_!6448 S1_V3_!6465))
      (or (not (and $x2931 $x3478 $x3434 $x3283 $x3303))
      (= S1_V3_!6448 S1_V3_!6475))
      (or
      (not (and (or $x198 (= E1_!6463 ?x3750)) $x3392 $x2913 $x2748 $x2831))
      $x2801) $x2991 (or $x3327 $x3285) 
      (or $x2821 $x2775)
      (or (not (and $x2931 $x3478 $x3434 $x3283 $x3303)) $x2539)
      (or $x3147 (= S1_V2_!6476 S1_V2_!6444))
      (or $x2691 (= S1_V2_!6476 S1_V2_!6466))
      (or (not (and $x3506 $x2656 $x2566)) $x4052) $x3713
      (or (not (and $x2776 $x3440 $x3088)) $x2891)
      (or $x3068 (= S2_V4_!6462 S2_V4_!6457))
      (or $x2604 (= S2_V4_!6462 S2_V4_!6473))
      (or $x2506 (= S2_V4_!6462 S2_V4_!6483))
      (or $x2497 (= S2_V4_!6473 S2_V4_!6457))
      (or $x2990 (= S2_V4_!6483 S2_V4_!6457))
      (or (not (and $x2458 $x2715 $x2956 $x3507 $x3181)) $x2603)
      (or (not $x2660) (= S1_V5_!6445 S1_V5_!6450)) $x3454
      (or (not $x2750) (= S1_V5_!6467 S1_V5_!6450)) 
      (or $x3147 $x3380) (or $x3252 (= S1_V5_!6477 S1_V5_!6450))
      (or $x2691 $x2431) (or $x3068 (= S2_V1_!6458 S2_V1_!6453))
      (or $x2604 (= S2_V1_!6458 S2_V1_!6469))
      (or $x2506 (= S2_V1_!6458 S2_V1_!6479))
      (or $x2497 (= S2_V1_!6469 S2_V1_!6453))
      (or $x3998 (= S2_V1_!6469 S2_V1_!6479))
      (or $x2990 (= S2_V1_!6479 S2_V1_!6453)) 
      (or (not $x2660) $x2507)
      (or
      (not (and (or $x198 (= E1_!6441 ?x3750)) $x3392 $x2913 $x2748 $x2831))
      $x3906) $x3455 (or (not $x2750) $x2720)
      (or
      (not (and (or $x198 (= E1_!6463 ?x3750)) $x3392 $x2913 $x2748 $x2831))
      $x3378) (or $x3252 $x4017) 
      (or $x3068 (= S2_V2_!6460 S2_V2_!6455))
      (or $x2497 (= S2_V2_!6471 S2_V2_!6455))
      (or
      (not (and (or $x398 (= ?x3364 ?x2657)) $x2607 $x2910 $x3456 $x3343))
      $x3097) (or $x3998 (= S2_V2_!6471 S2_V2_!6481)) 
      (or $x2990 $x2640)
      (or
      (not (and (or $x398 (= ?x3590 ?x2657)) $x2834 $x3023 $x3032 $x4063))
      $x2722) (or (not (and $x3177 $x3267 $x2592 $x2950 $x2526)) $x3348)
      (or $x3068 $x2451) (or $x2604 $x3427) 
      (or $x2506 $x2988) (or $x2497 $x4031) 
      (or $x3998 $x3229) (not MW_S1_V1) 
      (not MW_S1_V2) $x3174 $x2511 $x2820 $x3261 $x3809 $x3236)))
    (or (not $x3828) (not $x3485) (and $x2870 $x4130 $x3858 $x3779 $x2611))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let
 (($x3325 (not (or (and W_S2_V2 R_E1_V2) (and W_S2_V5 R_E1_V5) R_E1_V4))))
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
 (($x3897
   (= DISJ_W_S1_W_S2 (not (or W_S2_V3 (and W_S1_V5 W_S2_V5) W_S1_V4)))))
 (let (($x155 (not R_E1_V3)))
 (let
 (($x3855 (not (or R_S2_V3 (and W_S1_V5 R_S2_V5) (and W_S1_V4 R_S2_V4)))))
 (let
 (($x2785 (not (or R_S1_V3 (and W_S1_V5 R_S1_V5) (and W_S1_V4 R_S1_V4)))))
 (let (($x2398 (not W_S2_V3)))
 (let (($x2387 (not W_S2_V2)))
 (let (($x407 (not R_S2_V4)))
 (let (($x398 (not R_S2_V1)))
 (let (($x405 (not R_S2_V5)))
 (let (($x4585 (and $x405 $x407 $x2398 DISJ_W_S2_R_S1)))
 (let (($x2390 (not W_S2_V5)))
 (let (($x401 (not R_S2_V3)))
 (let (($x4922 (and $x401 $x407 $x2390 DISJ_W_S2_R_S1)))
 (let (($x3801 (and $x407 $x2390 $x2398 DISJ_W_S2_R_S1)))
 (let (($x2942 (and DISJ_W_S1_R_S2 DISJ_W_S2_R_S1)))
 (let (($x3927 (and DISJ_W_S2_R_S1 DISJ_W_S2_R_S2)))
 (let
 (($x6996
   (or $x3927 (and $x2387 DISJ_W_S2_R_S2) $x2942
   (and $x401 (not W_S1_V4) $x2390 DISJ_W_S2_R_S1) $x3801 $x4922
   (and (not W_S2_V1) $x2387) 
   (and $x398 $x401 $x2387 $x2390 DISJ_W_S2_R_S1)
   (and $x398 $x405 $x407 $x2387 DISJ_W_S2_R_S1)
   (and $x398 $x407 $x2387 $x2390 DISJ_W_S2_R_S1)
   (and $x398 $x401 $x407 $x2387 DISJ_W_S2_R_S1)
   (and $x398 $x401 $x405 $x2387 DISJ_W_S2_R_S1)
   (and DISJ_W_S1_W_S2 DISJ_W_S2_R_S1)
   (and $x398 $x2387 $x2390 $x2398 DISJ_W_S2_R_S1)
   (and $x405 (not W_S1_V4) $x2398 DISJ_W_S2_R_S1)
   (and $x398 $x405 $x2387 $x2398 DISJ_W_S2_R_S1)
   (and $x407 (not W_S1_V5) $x2398 DISJ_W_S2_R_S1) $x4585
   (and $x398 $x407 $x2387 $x2398 DISJ_W_S2_R_S1))))
 (let
 (($x3290
   (or (and $x2387 DISJ_W_S2_R_S1 DISJ_W_S1_R_S1) 
   (and (not W_S2_V1) $x2387) 
   (and (not R_S1_V1) DISJ_W_S1_R_S1))))
 (let (($x2350 (not W_S1_V2)))
 (let (($x2301 (not W_S1_V1)))
 (let (($x153 (not R_E1_V1)))
 (and DISJ_W_S1_R_E1 $x153 $x2301 $x2350 $x3290 $x6996 W_S1_V3 W_S2_V4
 (= DISJ_W_S1_R_S1 $x2785) 
 (= DISJ_W_S1_R_S2 $x3855) $x155 $x3897 $x112 $x115 
 (= DISJ_W_S2_R_E1 $x3325) $x5110 
 (not (and W_S1_V5 R_E1_V5)) 
 (not (and W_S1_V4 R_E1_V4)))))))))))))))))))))))))))))))
(assert (let (($x3927 (and DISJ_W_S2_R_S1 DISJ_W_S2_R_S2))) (not $x3927)))
(assert
 (let (($x2390 (not W_S2_V5)))
 (let (($x2356 (not W_S1_V4)))
 (let (($x2353 (not W_S1_V5)))
 (let (($x206 (not R_S1_V4)))
 (not (and $x206 $x2353 $x2356 $x2390 DISJ_W_S1_R_S2)))))))
(assert
 (let (($x2356 (not W_S1_V4)))
 (let (($x2353 (not W_S1_V5)))
 (let (($x206 (not R_S1_V4)))
 (let (($x204 (not R_S1_V5)))
 (not (and $x204 $x206 $x2353 $x2356 DISJ_W_S1_R_S2)))))))
(assert (let (($x2942 (and DISJ_W_S1_R_S2 DISJ_W_S2_R_S1))) (not $x2942)))
(assert
 (not (and (not R_S1_V1) DISJ_W_S2_R_S1 DISJ_W_S1_W_S2 DISJ_W_S1_R_S1)))
(assert
 (let (($x2390 (not W_S2_V5)))
 (let (($x2356 (not W_S1_V4)))
 (let (($x401 (not R_S2_V3)))
 (let (($x198 (not R_S1_V1)))
 (not (and $x198 $x401 $x2356 $x2390 DISJ_W_S2_R_S1 DISJ_W_S1_R_S1)))))))
(assert
 (let (($x2398 (not W_S2_V3)))
 (let (($x2390 (not W_S2_V5)))
 (let (($x407 (not R_S2_V4)))
 (let (($x3801 (and $x407 $x2390 $x2398 DISJ_W_S2_R_S1))) (not $x3801))))))
(assert
 (let (($x2390 (not W_S2_V5)))
 (let (($x407 (not R_S2_V4)))
 (let (($x401 (not R_S2_V3)))
 (let (($x4922 (and $x401 $x407 $x2390 DISJ_W_S2_R_S1))) (not $x4922))))))
(assert
 (let (($x2398 (not W_S2_V3)))
 (let (($x2353 (not W_S1_V5)))
 (let (($x407 (not R_S2_V4)))
 (let (($x198 (not R_S1_V1)))
 (not (and $x198 $x407 $x2353 $x2398 DISJ_W_S2_R_S1 DISJ_W_S1_R_S1)))))))
(assert
 (let (($x2398 (not W_S2_V3)))
 (let (($x407 (not R_S2_V4)))
 (let (($x405 (not R_S2_V5)))
 (let (($x4585 (and $x405 $x407 $x2398 DISJ_W_S2_R_S1))) (not $x4585))))))
(check-sat)
(exit)

