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
 (($x3462
   (forall
    ((V3_0 Int) (V2_0 Int) 
     (V5_0 Int) (V4_0 Int) 
     (MW_S1_V1 Bool) (MW_S1_V3 Bool) 
     (MW_S1_V2 Bool) (MW_S1_V5 Bool) 
     (MW_S1_V4 Bool) (MW_S2_V1 Bool) 
     (MW_S2_V3 Bool) (MW_S2_V2 Bool) 
     (MW_S2_V5 Bool) (MW_S2_V4 Bool) 
     (S1_V1_!2447 Int) (S1_V1_!2457 Int) 
     (S1_V1_!2468 Int) (S2_V5_!2455 Int) 
     (S2_V5_!2465 Int) (S2_V5_!2477 Int) 
     (S2_V5_!2482 Int) (S1_V3_!2448 Int) 
     (S1_V3_!2458 Int) (S1_V3_!2469 Int) 
     (S1_V2_!2449 Int) (S1_V2_!2459 Int) 
     (S1_V2_!2470 Int) (E1_!2446 Int) 
     (E1_!2467 Int) (E1_!2473 Int) 
     (S2_V4_!2456 Int) (S2_V4_!2466 Int) 
     (S2_V4_!2478 Int) (S2_V4_!2483 Int) 
     (S1_V5_!2450 Int) (S1_V5_!2460 Int) 
     (S1_V5_!2471 Int) (S2_V1_!2452 Int) 
     (S2_V1_!2462 Int) (S2_V1_!2474 Int) 
     (S2_V1_!2479 Int) (S1_V4_!2451 Int) 
     (S1_V4_!2461 Int) (S1_V4_!2472 Int) 
     (S2_V2_!2454 Int) (S2_V2_!2464 Int) 
     (S2_V2_!2476 Int) (S2_V2_!2481 Int) 
     (S2_V3_!2453 Int) (S2_V3_!2463 Int) 
     (S2_V3_!2475 Int) (S2_V3_!2480 Int))
    (let
    (($x2590
      (=
      (ite MW_S2_V4 S2_V4_!2466
      (ite MW_S1_V4 S1_V4_!2461
      (ite MW_S2_V4 S2_V4_!2456 (ite MW_S1_V4 S1_V4_!2451 V4_0))))
      (ite MW_S2_V4 S2_V4_!2483 (ite MW_S1_V4 S1_V4_!2472 V4_0)))))
    (let
    (($x3321
      (=
      (ite MW_S2_V5 S2_V5_!2465
      (ite MW_S1_V5 S1_V5_!2460
      (ite MW_S2_V5 S2_V5_!2455 (ite MW_S1_V5 S1_V5_!2450 V5_0))))
      (ite MW_S2_V5 S2_V5_!2482 (ite MW_S1_V5 S1_V5_!2471 V5_0)))))
    (let ((?x2455 (ite MW_S1_V2 S1_V2_!2470 V2_0)))
    (let ((?x3368 (ite MW_S2_V2 S2_V2_!2481 ?x2455)))
    (let ((?x2904 (ite MW_S1_V2 S1_V2_!2449 V2_0)))
    (let ((?x2846 (ite MW_S2_V2 S2_V2_!2454 ?x2904)))
    (let ((?x3414 (ite MW_S1_V2 S1_V2_!2459 ?x2846)))
    (let ((?x2463 (ite MW_S2_V2 S2_V2_!2464 ?x3414)))
    (let (($x3497 (= ?x2463 ?x3368)))
    (let
    (($x2653
      (=
      (ite MW_S2_V3 S2_V3_!2463
      (ite MW_S1_V3 S1_V3_!2458
      (ite MW_S2_V3 S2_V3_!2453 (ite MW_S1_V3 S1_V3_!2448 V3_0))))
      (ite MW_S2_V3 S2_V3_!2480 (ite MW_S1_V3 S1_V3_!2469 V3_0)))))
    (let ((?x2975 (ite MW_S2_V1 S2_V1_!2474 E1_!2473)))
    (let ((?x3074 (+ 1 ?x2975)))
    (let ((?x3454 (ite MW_S2_V1 S2_V1_!2479 ?x3074)))
    (let ((?x3583 (ite MW_S1_V1 S1_V1_!2447 E1_!2446)))
    (let ((?x2771 (ite MW_S2_V1 S2_V1_!2452 ?x3583)))
    (let ((?x2861 (+ 1 ?x2771)))
    (let ((?x3185 (ite MW_S1_V1 S1_V1_!2457 ?x2861)))
    (let ((?x3262 (ite MW_S2_V1 S2_V1_!2462 ?x3185)))
    (let (($x3126 (= ?x3262 ?x3454)))
    (let
    (($x2492
      (and (not (<= V2_0 E1_!2446)) 
      (not (<= ?x2846 ?x2861)) 
      (>= ?x3262 (+ (- 1) ?x2463)) 
      (not (<= V2_0 E1_!2467))
      (>= (ite MW_S1_V1 S1_V1_!2468 E1_!2467) (+ (- 1) ?x2455))
      (not (<= ?x2455 E1_!2473))
      (not (<= (ite MW_S2_V2 S2_V2_!2476 ?x2455) ?x3074))
      (>= ?x3454 (+ (- 1) ?x3368)))))
    (let (($x2550 (or (not MW_S2_V5) W_S2_V5)))
    (let (($x3459 (or (not MW_S2_V2) W_S2_V2)))
    (let (($x3240 (or (not MW_S2_V3) W_S2_V3)))
    (let (($x2661 (or (not MW_S2_V1) W_S2_V1)))
    (let (($x2811 (or (not MW_S1_V4) W_S1_V4)))
    (let (($x3256 (or (not MW_S1_V5) W_S1_V5)))
    (let (($x2849 (= S2_V3_!2475 S2_V3_!2480)))
    (let (($x223 (not R_S2_V4)))
    (let
    (($x2709
      (or $x223
      (= (ite MW_S1_V4 S1_V4_!2472 V4_0)
      (ite MW_S2_V4 S2_V4_!2478 (ite MW_S1_V4 S1_V4_!2472 V4_0))))))
    (let (($x221 (not R_S2_V5)))
    (let
    (($x3071
      (or $x221
      (= (ite MW_S1_V5 S1_V5_!2471 V5_0)
      (ite MW_S2_V5 S2_V5_!2477 (ite MW_S1_V5 S1_V5_!2471 V5_0))))))
    (let (($x219 (not R_S2_V2)))
    (let (($x3020 (or $x219 (= ?x2455 (ite MW_S2_V2 S2_V2_!2476 ?x2455)))))
    (let (($x217 (not R_S2_V3)))
    (let
    (($x2645
      (or $x217
      (= (ite MW_S1_V3 S1_V3_!2469 V3_0)
      (ite MW_S2_V3 S2_V3_!2475 (ite MW_S1_V3 S1_V3_!2469 V3_0))))))
    (let
    (($x2987
      (not
      (and (or (not R_S2_V1) (= E1_!2473 ?x3074)) $x2645 $x3020 $x3071
      $x2709))))
    (let (($x2801 (= S2_V3_!2475 S2_V3_!2463)))
    (let ((?x2991 (ite MW_S1_V4 S1_V4_!2451 V4_0)))
    (let ((?x2923 (ite MW_S2_V4 S2_V4_!2456 ?x2991)))
    (let ((?x3255 (ite MW_S1_V4 S1_V4_!2461 ?x2923)))
    (let ((?x3637 (ite MW_S1_V4 S1_V4_!2472 V4_0)))
    (let (($x2702 (or $x223 (= ?x3637 ?x3255))))
    (let ((?x3355 (ite MW_S1_V5 S1_V5_!2450 V5_0)))
    (let ((?x2614 (ite MW_S2_V5 S2_V5_!2455 ?x3355)))
    (let ((?x3545 (ite MW_S1_V5 S1_V5_!2460 ?x2614)))
    (let ((?x3303 (ite MW_S1_V5 S1_V5_!2471 V5_0)))
    (let (($x3551 (or $x221 (= ?x3303 ?x3545))))
    (let (($x3307 (or $x219 (= ?x2455 ?x3414))))
    (let ((?x3384 (ite MW_S1_V3 S1_V3_!2448 V3_0)))
    (let ((?x2870 (ite MW_S2_V3 S2_V3_!2453 ?x3384)))
    (let ((?x3272 (ite MW_S1_V3 S1_V3_!2458 ?x2870)))
    (let ((?x2679 (ite MW_S1_V3 S1_V3_!2469 V3_0)))
    (let (($x3399 (or $x217 (= ?x2679 ?x3272))))
    (let (($x215 (not R_S2_V1)))
    (let (($x3421 (or $x215 (= E1_!2473 ?x3185))))
    (let (($x2694 (= S2_V3_!2475 S2_V3_!2453)))
    (let (($x2711 (or $x223 (= ?x3637 ?x2991))))
    (let (($x2752 (or $x221 (= ?x3303 ?x3355))))
    (let (($x2891 (or $x219 (= ?x2455 ?x2904))))
    (let (($x2680 (or $x217 (= ?x2679 ?x3384))))
    (let (($x2995 (or $x215 (= E1_!2473 ?x3583))))
    (let (($x2742 (not (and $x2995 $x2680 $x2891 $x2752 $x2711))))
    (let (($x3098 (= S2_V3_!2463 S2_V3_!2480)))
    (let (($x3543 (or $x223 (= ?x3255 (ite MW_S2_V4 S2_V4_!2478 ?x3637)))))
    (let (($x2571 (or $x221 (= ?x3545 (ite MW_S2_V5 S2_V5_!2477 ?x3303)))))
    (let (($x2520 (or $x219 (= ?x3414 (ite MW_S2_V2 S2_V2_!2476 ?x2455)))))
    (let (($x3119 (or $x217 (= ?x3272 (ite MW_S2_V3 S2_V3_!2475 ?x2679)))))
    (let
    (($x3081
      (not (and (or $x215 (= ?x3185 ?x3074)) $x3119 $x2520 $x2571 $x3543))))
    (let (($x3601 (= S2_V3_!2463 S2_V3_!2453)))
    (let (($x2888 (or $x223 (= ?x3255 ?x2991))))
    (let (($x3524 (or $x221 (= ?x3545 ?x3355))))
    (let (($x2856 (or $x219 (= ?x3414 ?x2904))))
    (let (($x2777 (or $x217 (= ?x3272 ?x3384))))
    (let (($x3107 (or $x215 (= ?x3185 ?x3583))))
    (let (($x3562 (not (and $x3107 $x2777 $x2856 $x3524 $x2888))))
    (let (($x3196 (= S2_V3_!2453 S2_V3_!2480)))
    (let (($x2205 (or $x223 (= ?x2991 (ite MW_S2_V4 S2_V4_!2478 ?x3637)))))
    (let (($x3132 (or $x221 (= ?x3355 (ite MW_S2_V5 S2_V5_!2477 ?x3303)))))
    (let (($x3353 (or $x219 (= ?x2904 (ite MW_S2_V2 S2_V2_!2476 ?x2455)))))
    (let (($x4130 (or $x217 (= ?x3384 (ite MW_S2_V3 S2_V3_!2475 ?x2679)))))
    (let
    (($x3291
      (not (and (or $x215 (= ?x3583 ?x3074)) $x4130 $x3353 $x3132 $x2205))))
    (let (($x3632 (= S2_V2_!2481 S2_V2_!2476)))
    (let (($x3743 (or $x223 (= (ite MW_S2_V4 S2_V4_!2478 ?x3637) ?x3637))))
    (let (($x3325 (or $x221 (= (ite MW_S2_V5 S2_V5_!2477 ?x3303) ?x3303))))
    (let (($x3978 (or $x219 (= (ite MW_S2_V2 S2_V2_!2476 ?x2455) ?x2455))))
    (let (($x3434 (or $x217 (= (ite MW_S2_V3 S2_V3_!2475 ?x2679) ?x2679))))
    (let
    (($x4079
      (or
      (not
      (and (or $x215 (= ?x2975 (+ (- 1) E1_!2473))) $x3434 $x3978 $x3325
      $x3743)) $x3632)))
    (let (($x4012 (= S2_V2_!2481 S2_V2_!2464)))
    (let (($x3946 (or $x223 (= (ite MW_S2_V4 S2_V4_!2478 ?x3637) ?x3255))))
    (let (($x3990 (or $x221 (= (ite MW_S2_V5 S2_V5_!2477 ?x3303) ?x3545))))
    (let (($x3224 (or $x219 (= (ite MW_S2_V2 S2_V2_!2476 ?x2455) ?x3414))))
    (let (($x3139 (or $x217 (= (ite MW_S2_V3 S2_V3_!2475 ?x2679) ?x3272))))
    (let
    (($x3162
      (or
      (not
      (and (or $x215 (= ?x2975 (+ (- 1) ?x3185))) $x3139 $x3224 $x3990
      $x3946)) $x4012)))
    (let (($x3948 (= S2_V2_!2464 S2_V2_!2476)))
    (let (($x3867 (or $x223 (= ?x3255 ?x3637))))
    (let (($x3893 (or $x221 (= ?x3545 ?x3303))))
    (let (($x2978 (or $x219 (= ?x3414 ?x2455))))
    (let (($x3774 (or $x217 (= ?x3272 ?x2679))))
    (let (($x2768 (or $x215 (= ?x3185 E1_!2473))))
    (let (($x3555 (not (and $x2768 $x3774 $x2978 $x3893 $x3867))))
    (let (($x3969 (= S2_V2_!2454 S2_V2_!2476)))
    (let (($x4110 (or $x223 (= ?x2991 ?x3637))))
    (let (($x2944 (or $x221 (= ?x3355 ?x3303))))
    (let (($x3431 (or $x219 (= ?x2904 ?x2455))))
    (let (($x4243 (or $x217 (= ?x3384 ?x2679))))
    (let (($x3861 (or $x215 (= ?x3583 E1_!2473))))
    (let (($x3884 (= S2_V2_!2454 S2_V2_!2464)))
    (let (($x3997 (or $x223 (= ?x2991 ?x3255))))
    (let (($x3179 (or $x221 (= ?x3355 ?x3545))))
    (let (($x3662 (or $x219 (= ?x2904 ?x3414))))
    (let (($x4030 (or $x217 (= ?x3384 ?x3272))))
    (let (($x2481 (or $x215 (= ?x3583 ?x3185))))
    (let (($x3217 (= S1_V4_!2472 S1_V4_!2461)))
    (let (($x210 (not R_S1_V4)))
    (let (($x3767 (or $x210 (= V4_0 ?x2923))))
    (let (($x208 (not R_S1_V5)))
    (let (($x3690 (or $x208 (= V5_0 ?x2614))))
    (let (($x206 (not R_S1_V2)))
    (let (($x4056 (or $x206 (= V2_0 ?x2846))))
    (let (($x204 (not R_S1_V3)))
    (let (($x3737 (or $x204 (= V3_0 ?x2870))))
    (let
    (($x3803
      (not
      (and (or (not R_S1_V1) (= E1_!2467 ?x2861)) $x3737 $x4056 $x3690
      $x3767))))
    (let
    (($x3500
      (or (not (or (not R_S1_V1) (= E1_!2446 E1_!2467)))
      (= S1_V4_!2451 S1_V4_!2472))))
    (let (($x4117 (= S1_V4_!2451 S1_V4_!2461)))
    (let
    (($x3933
      (or
      (not
      (and (or (not R_S1_V1) (= E1_!2446 ?x2861)) $x3737 $x4056 $x3690
      $x3767)) $x4117)))
    (let (($x4279 (not (or (not R_S1_V1) (= E1_!2467 E1_!2446)))))
    (let (($x4277 (or $x4279 (= S1_V5_!2471 S1_V5_!2450))))
    (let (($x3913 (= S1_V5_!2450 S1_V5_!2460)))
    (let
    (($x4059
      (or
      (not
      (and (or (not R_S1_V1) (= E1_!2446 ?x2861)) $x3737 $x4056 $x3690
      $x3767)) $x3913)))
    (let (($x3592 (= S2_V4_!2483 S2_V4_!2456)))
    (let (($x3928 (or $x223 (= (ite MW_S2_V4 S2_V4_!2478 ?x3637) ?x2991))))
    (let (($x3634 (or $x221 (= (ite MW_S2_V5 S2_V5_!2477 ?x3303) ?x3355))))
    (let (($x3758 (or $x219 (= (ite MW_S2_V2 S2_V2_!2476 ?x2455) ?x2904))))
    (let (($x3896 (or $x217 (= (ite MW_S2_V3 S2_V3_!2475 ?x2679) ?x3384))))
    (let
    (($x3164
      (or
      (not
      (and (or $x215 (= ?x2975 (+ (- 1) ?x3583))) $x3896 $x3758 $x3634
      $x3928)) $x3592)))
    (let (($x4160 (= E1_!2467 E1_!2473)))
    (let (($x158 (not R_E1_V4)))
    (let (($x4054 (or $x158 (= V4_0 ?x3637))))
    (let (($x156 (not R_E1_V5)))
    (let (($x3916 (or $x156 (= V5_0 ?x3303))))
    (let (($x154 (not R_E1_V2)))
    (let (($x3959 (or $x154 (= V2_0 ?x2455))))
    (let (($x3835 (= E1_!2467 E1_!2446)))
    (let (($x3299 (or $x4279 (= S1_V2_!2470 S1_V2_!2449))))
    (let (($x3800 (= S1_V2_!2459 S1_V2_!2470)))
    (let (($x2809 (or $x210 (= ?x2923 V4_0))))
    (let (($x4106 (or $x208 (= ?x2614 V5_0))))
    (let (($x4060 (or $x206 (= ?x2846 V2_0))))
    (let (($x3831 (or $x204 (= ?x2870 V3_0))))
    (let
    (($x4166
      (and (or (not R_S1_V1) (= ?x2771 (+ (- 1) E1_!2467))) $x3831 $x4060
      $x4106 $x2809)))
    (let (($x3863 (= S1_V2_!2459 S1_V2_!2449)))
    (let
    (($x3877
      (and (or (not R_S1_V1) (= ?x2771 (+ (- 1) E1_!2446))) $x3831 $x4060
      $x4106 $x2809)))
    (let (($x3922 (not $x3877)))
    (let (($x4089 (or $x4279 (= S1_V3_!2469 S1_V3_!2448))))
    (let (($x3408 (= S2_V5_!2482 S2_V5_!2477)))
    (let
    (($x3064
      (or
      (not
      (and (or $x215 (= ?x2975 (+ (- 1) E1_!2473))) $x3434 $x3978 $x3325
      $x3743)) $x3408)))
    (let (($x3234 (or $x4279 (= S1_V1_!2468 S1_V1_!2447))))
    (let
    (($x2690
      (and (or $x3922 (= S1_V1_!2457 S1_V1_!2447)) $x3234
      (or $x3803 (= S1_V1_!2468 S1_V1_!2457))
      (or (not (and $x2481 $x4030 $x3662 $x3179 $x3997))
      (= S2_V5_!2455 S2_V5_!2465))
      (or (not (and $x3861 $x4243 $x3431 $x2944 $x4110))
      (= S2_V5_!2455 S2_V5_!2477)) 
      (or $x3291 (= S2_V5_!2455 S2_V5_!2482))
      (or $x3555 (= S2_V5_!2465 S2_V5_!2477))
      (or $x3081 (= S2_V5_!2465 S2_V5_!2482)) $x3064
      (or $x3922 (= S1_V3_!2458 S1_V3_!2448))
      (or (not $x4166) (= S1_V3_!2458 S1_V3_!2469)) $x4089 
      (or $x3922 $x3863) (or (not $x4166) $x3800) $x3299
      (or (not (and $x3959 $x3916 $x4054)) (= E1_!2446 E1_!2473)) $x3835
      (or (not (and $x3959 $x3916 $x4054)) $x4160)
      (or $x3562 (= S2_V4_!2466 S2_V4_!2456))
      (or $x3555 (= S2_V4_!2466 S2_V4_!2478))
      (or $x3081 (= S2_V4_!2466 S2_V4_!2483))
      (or $x2742 (= S2_V4_!2478 S2_V4_!2456))
      (or $x2987 (= S2_V4_!2478 S2_V4_!2483)) $x3164 $x4059 $x4277
      (or $x3803 (= S1_V5_!2471 S1_V5_!2460))
      (or $x3291 (= S2_V1_!2452 S2_V1_!2479))
      (or $x3562 (= S2_V1_!2462 S2_V1_!2452))
      (or $x3081 (= S2_V1_!2462 S2_V1_!2479))
      (or $x2742 (= S2_V1_!2474 S2_V1_!2452))
      (or (not (and $x3421 $x3399 $x3307 $x3551 $x2702))
      (= S2_V1_!2474 S2_V1_!2462)) 
      (or $x2987 (= S2_V1_!2474 S2_V1_!2479)) $x3933 $x3500
      (or $x3803 $x3217)
      (or (not (and $x2481 $x4030 $x3662 $x3179 $x3997)) $x3884)
      (or (not (and $x3861 $x4243 $x3431 $x2944 $x4110)) $x3969)
      (or $x3291 (= S2_V2_!2454 S2_V2_!2481)) 
      (or $x3555 $x3948) $x3162 $x4079 
      (or $x3291 $x3196) (or $x3562 $x3601) 
      (or $x3081 $x3098) (or $x2742 $x2694)
      (or (not (and $x3421 $x3399 $x3307 $x3551 $x2702)) $x2801)
      (or $x2987 $x2849) (not MW_S1_V1) 
      (not MW_S1_V2) $x3256 $x2811 $x2661 $x3240 $x3459 $x2550)))
    (or (not $x2690) (not $x2492) (and $x3126 $x2653 $x3497 $x3321 $x2590)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let
 (($x2925 (not (or (and W_S2_V2 R_E1_V2) (and W_S2_V5 R_E1_V5) R_E1_V4))))
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
 (($x3189
   (= DISJ_W_S1_W_S2 (not (or W_S2_V3 (and W_S1_V5 W_S2_V5) W_S1_V4)))))
 (let (($x152 (not R_E1_V3)))
 (let
 (($x2996 (not (or R_S2_V3 (and W_S1_V5 R_S2_V5) (and W_S1_V4 R_S2_V4)))))
 (let
 (($x3405 (not (or R_S1_V3 (and W_S1_V5 R_S1_V5) (and W_S1_V4 R_S1_V4)))))
 (let (($x2259 (not W_S2_V2)))
 (let (($x2253 (not W_S2_V1)))
 (let (($x3338 (and $x2253 $x2259)))
 (let
 (($x3621
   (or (and $x2259 DISJ_W_S2_R_S1 DISJ_W_S1_R_S1) $x3338
   (and (not R_S1_V1) DISJ_W_S1_R_S1))))
 (let (($x2209 (not W_S1_V2)))
 (let (($x2206 (not W_S1_V1)))
 (let (($x150 (not R_E1_V1)))
 (and DISJ_W_S1_R_E1 $x150 $x2206 $x2209 $x3621 W_S1_V3 W_S2_V4
 (= DISJ_W_S1_R_S1 $x3405) 
 (= DISJ_W_S1_R_S2 $x2996) $x152 $x3189 $x112 $x115 
 (= DISJ_W_S2_R_E1 $x2925) $x3462 
 (not (and W_S1_V5 R_E1_V5)) 
 (not (and W_S1_V4 R_E1_V4)))))))))))))))))))))
(assert (not (and DISJ_W_S2_R_S1 DISJ_W_S2_R_S2)))
(assert (not (and (not W_S2_V2) DISJ_W_S2_R_S2)))
(assert (not (and DISJ_W_S1_R_S2 DISJ_W_S2_R_S1)))
(assert (not (and (not R_S2_V3) (not R_S2_V4) (not W_S2_V5) DISJ_W_S2_R_S1)))
(assert
 (let (($x2259 (not W_S2_V2)))
 (let (($x2253 (not W_S2_V1)))
 (let (($x3338 (and $x2253 $x2259))) (not $x3338)))))
(assert (not (and (not R_S2_V3) (not W_S1_V4) (not W_S2_V5) DISJ_W_S2_R_S1)))
(assert (not (and DISJ_W_S1_W_S2 DISJ_W_S2_R_S1)))
(assert (not (and (not R_S2_V4) (not W_S2_V5) (not W_S2_V3) DISJ_W_S2_R_S1)))
(assert (not (and (not R_S2_V4) (not W_S1_V5) (not W_S2_V3) DISJ_W_S2_R_S1)))
(assert (not (and (not R_S2_V5) (not R_S2_V4) (not W_S2_V3) DISJ_W_S2_R_S1)))
(assert (not (and (not R_S2_V5) (not W_S1_V4) (not W_S2_V3) DISJ_W_S2_R_S1)))
(assert
 (let (($x2259 (not W_S2_V2)))
 (let (($x223 (not R_S2_V4)))
 (let (($x217 (not R_S2_V3)))
 (let (($x215 (not R_S2_V1)))
 (not (and $x215 $x217 $x223 $x2259 DISJ_W_S2_R_S1)))))))
(assert
 (let (($x2285 (not W_S2_V3)))
 (let (($x2259 (not W_S2_V2)))
 (let (($x223 (not R_S2_V4)))
 (let (($x215 (not R_S2_V1)))
 (let (($x6276 (and $x215 $x223 $x2259 $x2285 DISJ_W_S2_R_S1))) (not $x6276)))))))
(check-sat)
(exit)

