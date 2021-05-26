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
(declare-fun R_E1_V6 () Bool)
(declare-fun W_S1_V6 () Bool)
(declare-fun R_E2_V6 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun R_S1_V6 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun R_S1_V5 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_E2_V4 () Bool)
(declare-fun R_E2_V2 () Bool)
(declare-fun R_E1_V5 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun R_E2_V5 () Bool)
(declare-fun W_S1_V5 () Bool)
(declare-fun W_S1_V4 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun R_E1_V1 () Bool)
(declare-fun R_E2_V3 () Bool)
(declare-fun R_E2_V1 () Bool)
(declare-fun DISJ_W_S1_R_E1 () Bool)
(declare-fun DISJ_W_S1_R_E2 () Bool)
(assert
 (let (($x56 (and W_S1_V6 R_E1_V6)))
 (let (($x63586 (not $x56)))
 (let (($x24 (and W_S1_V6 R_E2_V6)))
 (let (($x63056 (not $x24)))
 (let
 (($x63315
   (forall
    ((V2_0 Int) (V5_0 Int) 
     (V4_0 Int) (V6_0 Int) 
     (MW_S1_V1 Bool) (MW_S1_V3 Bool) 
     (MW_S1_V2 Bool) (MW_S1_V5 Bool) 
     (MW_S1_V4 Bool) (MW_S1_V6 Bool) 
     (S1_V1_!8487 Int) (S1_V1_!8493 Int) 
     (S1_V1_!8500 Int) (S1_V1_!8509 Int) 
     (S1_V1_!8515 Int) (S1_V3_!8488 Int) 
     (S1_V3_!8494 Int) (S1_V3_!8501 Int) 
     (S1_V3_!8510 Int) (S1_V3_!8516 Int) 
     (S1_V2_!8489 Int) (S1_V2_!8495 Int) 
     (S1_V2_!8502 Int) (S1_V2_!8511 Int) 
     (S1_V2_!8517 Int) (E1_!8484 Int) 
     (E1_!8506 Int) (E1_!8508 Int) 
     (S1_V5_!8490 Int) (S1_V5_!8496 Int) 
     (S1_V5_!8503 Int) (S1_V5_!8512 Int) 
     (S1_V5_!8518 Int) (E2_!8485 Int) 
     (E2_!8486 Int) (E2_!8499 Int) 
     (E2_!8507 Int) (S1_V4_!8491 Int) 
     (S1_V4_!8497 Int) (S1_V4_!8504 Int) 
     (S1_V4_!8513 Int) (S1_V4_!8519 Int) 
     (S1_V6_!8492 Int) (S1_V6_!8498 Int) 
     (S1_V6_!8505 Int) (S1_V6_!8514 Int) 
     (S1_V6_!8520 Int))
    (let ((?x60012 (ite MW_S1_V6 S1_V6_!8520 V6_0)))
    (let ((?x59876 (ite MW_S1_V6 S1_V6_!8505 V6_0)))
    (let (($x59892 (= ?x59876 ?x60012)))
    (let ((?x62448 (ite MW_S1_V4 S1_V4_!8519 V4_0)))
    (let ((?x64645 (ite MW_S1_V4 S1_V4_!8504 V4_0)))
    (let (($x64070 (= ?x64645 ?x62448)))
    (let ((?x62472 (ite MW_S1_V5 S1_V5_!8518 V5_0)))
    (let ((?x62960 (ite MW_S1_V5 S1_V5_!8503 V5_0)))
    (let (($x64411 (= ?x62960 ?x62472)))
    (let ((?x60036 (ite MW_S1_V2 S1_V2_!8517 V2_0)))
    (let ((?x62642 (ite MW_S1_V2 S1_V2_!8502 V2_0)))
    (let (($x62687 (= ?x62642 ?x60036)))
    (let ((?x63428 (ite MW_S1_V3 S1_V3_!8516 E2_!8507)))
    (let ((?x64967 (ite MW_S1_V3 S1_V3_!8501 E2_!8499)))
    (let (($x63026 (= ?x64967 ?x63428)))
    (let ((?x64311 (ite MW_S1_V1 S1_V1_!8509 E1_!8508)))
    (let ((?x60890 (+ 1 ?x64311)))
    (let ((?x60071 (ite MW_S1_V1 S1_V1_!8515 ?x60890)))
    (let ((?x64139 (ite MW_S1_V1 S1_V1_!8493 E1_!8484)))
    (let ((?x61172 (+ 1 ?x64139)))
    (let ((?x62354 (ite MW_S1_V1 S1_V1_!8500 ?x61172)))
    (let (($x63313 (= ?x62354 ?x60071)))
    (let (($x62988 (and $x63313 $x63026 $x62687 $x64411 $x64070 $x59892)))
    (let ((?x64915 (+ (- 1) ?x62448)))
    (let (($x64754 (>= ?x63428 ?x64915)))
    (let ((?x64772 (+ (- 1) ?x60036)))
    (let (($x64144 (>= ?x60071 ?x64772)))
    (let ((?x62483 (ite MW_S1_V2 S1_V2_!8511 V2_0)))
    (let (($x63016 (<= ?x62483 ?x60890)))
    (let (($x63678 (not $x63016)))
    (let (($x61449 (<= V2_0 E1_!8508)))
    (let (($x62761 (not $x61449)))
    (let (($x63359 (<= V4_0 E2_!8507)))
    (let (($x64255 (not $x63359)))
    (let (($x59908 (<= V2_0 E1_!8506)))
    (let (($x62749 (not $x59908)))
    (let ((?x62849 (+ (- 1) ?x62642)))
    (let (($x63371 (>= ?x62354 ?x62849)))
    (let ((?x62966 (+ (- 1) ?x64645)))
    (let (($x63451 (>= ?x64967 ?x62966)))
    (let ((?x62947 (ite MW_S1_V4 S1_V4_!8497 V4_0)))
    (let (($x64436 (<= ?x62947 E2_!8499)))
    (let (($x63625 (not $x64436)))
    (let ((?x62375 (ite MW_S1_V2 S1_V2_!8495 V2_0)))
    (let (($x62873 (<= ?x62375 ?x61172)))
    (let (($x64774 (not $x62873)))
    (let ((?x62675 (+ (- 1) ?x62947)))
    (let ((?x64140 (ite MW_S1_V3 S1_V3_!8488 E2_!8486)))
    (let ((?x63780 (+ 1 ?x64140)))
    (let ((?x64240 (ite MW_S1_V3 S1_V3_!8494 ?x63780)))
    (let (($x64182 (>= ?x64240 ?x62675)))
    (let ((?x64511 (ite MW_S1_V4 S1_V4_!8491 V4_0)))
    (let (($x64748 (<= ?x64511 ?x63780)))
    (let (($x64194 (not $x64748)))
    (let (($x63050 (<= V4_0 E2_!8486)))
    (let (($x60909 (not $x63050)))
    (let (($x60946 (<= V2_0 E1_!8484)))
    (let (($x63727 (not $x60946)))
    (let (($x61017 (<= V4_0 E2_!8485)))
    (let (($x61403 (not $x61017)))
    (let
    (($x62573
      (and $x61403 $x63727 $x60909 $x64194 $x64182 $x64774 $x63625 $x63451
      $x63371 $x62749 $x64255 $x62761 $x63678 $x64144 $x64754)))
    (let (($x64977 (not $x62573)))
    (let (($x64510 (not MW_S1_V6)))
    (let (($x64171 (or $x64510 W_S1_V6)))
    (let (($x62772 (not MW_S1_V4)))
    (let (($x64147 (not MW_S1_V2)))
    (let (($x64325 (not MW_S1_V3)))
    (let (($x62498 (or $x64325 W_S1_V3)))
    (let (($x63897 (not MW_S1_V1)))
    (let (($x64641 (or $x63897 W_S1_V1)))
    (let (($x64205 (= S1_V6_!8520 S1_V6_!8514)))
    (let ((?x63733 (ite MW_S1_V6 S1_V6_!8514 V6_0)))
    (let (($x62268 (= ?x63733 V6_0)))
    (let (($x207 (not R_S1_V6)))
    (let (($x61279 (or $x207 $x62268)))
    (let ((?x64830 (ite MW_S1_V4 S1_V4_!8513 V4_0)))
    (let (($x64551 (= ?x64830 V4_0)))
    (let (($x205 (not R_S1_V4)))
    (let (($x63713 (or $x205 $x64551)))
    (let ((?x64187 (ite MW_S1_V5 S1_V5_!8512 V5_0)))
    (let (($x62629 (= ?x64187 V5_0)))
    (let (($x203 (not R_S1_V5)))
    (let (($x63293 (or $x203 $x62629)))
    (let (($x62800 (= ?x62483 V2_0)))
    (let (($x201 (not R_S1_V2)))
    (let (($x61485 (or $x201 $x62800)))
    (let ((?x64096 (ite MW_S1_V3 S1_V3_!8510 E2_!8507)))
    (let (($x60980 (= ?x64096 E2_!8507)))
    (let (($x199 (not R_S1_V3)))
    (let (($x63663 (or $x199 $x60980)))
    (let ((?x59988 (+ (- 1) E1_!8508)))
    (let (($x63070 (= ?x64311 ?x59988)))
    (let (($x197 (not R_S1_V1)))
    (let (($x61351 (or $x197 $x63070)))
    (let (($x62464 (and $x61351 $x63663 $x61485 $x63293 $x63713 $x61279)))
    (let (($x62880 (not $x62464)))
    (let (($x63944 (or $x62880 $x64205)))
    (let (($x62266 (= S1_V6_!8520 S1_V6_!8492)))
    (let (($x64406 (= ?x64096 E2_!8486)))
    (let (($x64167 (or $x199 $x64406)))
    (let ((?x60191 (+ (- 1) E1_!8484)))
    (let (($x63900 (= ?x64311 ?x60191)))
    (let (($x63998 (or $x197 $x63900)))
    (let (($x64028 (and $x63998 $x64167 $x61485 $x63293 $x63713 $x61279)))
    (let (($x64135 (not $x64028)))
    (let (($x63815 (or $x64135 $x62266)))
    (let (($x64598 (= S1_V6_!8505 S1_V6_!8520)))
    (let ((?x63242 (ite MW_S1_V6 S1_V6_!8498 V6_0)))
    (let (($x61234 (= ?x63242 ?x63733)))
    (let (($x64590 (or $x207 $x61234)))
    (let (($x63441 (= ?x62947 ?x64830)))
    (let (($x61385 (or $x205 $x63441)))
    (let ((?x64769 (ite MW_S1_V5 S1_V5_!8496 V5_0)))
    (let (($x61122 (= ?x64769 ?x64187)))
    (let (($x62575 (or $x203 $x61122)))
    (let (($x62830 (= ?x62375 ?x62483)))
    (let (($x64418 (or $x201 $x62830)))
    (let (($x64159 (= E2_!8499 ?x64096)))
    (let (($x59856 (or $x199 $x64159)))
    (let (($x62397 (= ?x64139 ?x64311)))
    (let (($x60901 (or $x197 $x62397)))
    (let (($x61057 (and $x60901 $x59856 $x64418 $x62575 $x61385 $x64590)))
    (let (($x63584 (not $x61057)))
    (let (($x64750 (or $x63584 $x64598)))
    (let (($x60952 (= S1_V6_!8505 S1_V6_!8514)))
    (let (($x63349 (= ?x63242 V6_0)))
    (let (($x63795 (or $x207 $x63349)))
    (let (($x60080 (= ?x62947 V4_0)))
    (let (($x62328 (or $x205 $x60080)))
    (let (($x63789 (= ?x64769 V5_0)))
    (let (($x62824 (or $x203 $x63789)))
    (let (($x64229 (= ?x62375 V2_0)))
    (let (($x62563 (or $x201 $x64229)))
    (let (($x59879 (= E2_!8499 E2_!8507)))
    (let (($x60155 (or $x199 $x59879)))
    (let (($x63124 (= ?x64139 ?x59988)))
    (let (($x64001 (or $x197 $x63124)))
    (let (($x62821 (and $x64001 $x60155 $x62563 $x62824 $x62328 $x63795)))
    (let (($x64736 (not $x62821)))
    (let (($x64373 (or $x64736 $x60952)))
    (let (($x62680 (= S1_V6_!8505 S1_V6_!8498)))
    (let ((?x63195 (ite MW_S1_V6 S1_V6_!8492 V6_0)))
    (let (($x64485 (= ?x63242 ?x63195)))
    (let (($x62787 (or $x207 $x64485)))
    (let (($x60944 (= ?x62947 ?x64511)))
    (let (($x63394 (or $x205 $x60944)))
    (let ((?x62350 (ite MW_S1_V5 S1_V5_!8490 V5_0)))
    (let (($x62750 (= ?x64769 ?x62350)))
    (let (($x61321 (or $x203 $x62750)))
    (let ((?x64163 (ite MW_S1_V2 S1_V2_!8489 V2_0)))
    (let (($x62351 (= ?x62375 ?x64163)))
    (let (($x63240 (or $x201 $x62351)))
    (let (($x63896 (= E2_!8499 ?x63780)))
    (let (($x62398 (or $x199 $x63896)))
    (let ((?x64223 (ite MW_S1_V1 S1_V1_!8487 E1_!8484)))
    (let ((?x64148 (+ (- 1) ?x64223)))
    (let (($x62876 (= ?x64139 ?x64148)))
    (let (($x63414 (or $x197 $x62876)))
    (let (($x62582 (and $x63414 $x62398 $x63240 $x61321 $x63394 $x62787)))
    (let (($x62833 (not $x62582)))
    (let (($x63622 (or $x62833 $x62680)))
    (let (($x62660 (= S1_V6_!8505 S1_V6_!8492)))
    (let (($x63200 (= E2_!8499 E2_!8486)))
    (let (($x61016 (or $x199 $x63200)))
    (let (($x63844 (= ?x64139 ?x60191)))
    (let (($x64476 (or $x197 $x63844)))
    (let (($x63243 (and $x64476 $x61016 $x62563 $x62824 $x62328 $x63795)))
    (let (($x59909 (not $x63243)))
    (let (($x63002 (or $x59909 $x62660)))
    (let (($x64655 (= S1_V6_!8498 S1_V6_!8520)))
    (let (($x63814 (= ?x63195 ?x63733)))
    (let (($x62469 (or $x207 $x63814)))
    (let (($x60131 (= ?x64511 ?x64830)))
    (let (($x61493 (or $x205 $x60131)))
    (let (($x64832 (= ?x62350 ?x64187)))
    (let (($x62513 (or $x203 $x64832)))
    (let (($x62705 (= ?x64163 ?x62483)))
    (let (($x64322 (or $x201 $x62705)))
    (let ((?x63566 (+ (- 1) ?x64096)))
    (let (($x64306 (= ?x64140 ?x63566)))
    (let (($x62913 (or $x199 $x64306)))
    (let (($x62955 (= ?x64223 ?x60890)))
    (let (($x64121 (or $x197 $x62955)))
    (let (($x61059 (and $x64121 $x62913 $x64322 $x62513 $x61493 $x62469)))
    (let (($x64628 (not $x61059)))
    (let (($x62909 (or $x64628 $x64655)))
    (let (($x64783 (= S1_V6_!8498 S1_V6_!8514)))
    (let (($x64160 (= ?x63195 V6_0)))
    (let (($x62270 (or $x207 $x64160)))
    (let (($x63635 (= ?x64511 V4_0)))
    (let (($x64372 (or $x205 $x63635)))
    (let (($x62825 (= ?x62350 V5_0)))
    (let (($x61072 (or $x203 $x62825)))
    (let (($x59886 (= ?x64163 V2_0)))
    (let (($x64456 (or $x201 $x59886)))
    (let ((?x62292 (+ (- 1) E2_!8507)))
    (let (($x59996 (= ?x64140 ?x62292)))
    (let (($x62323 (or $x199 $x59996)))
    (let (($x63798 (= ?x64223 E1_!8508)))
    (let (($x64014 (or $x197 $x63798)))
    (let (($x63215 (and $x64014 $x62323 $x64456 $x61072 $x64372 $x62270)))
    (let (($x62918 (not $x63215)))
    (let (($x63641 (or $x62918 $x64783)))
    (let (($x64771 (= S1_V6_!8498 S1_V6_!8492)))
    (let ((?x63516 (+ (- 1) E2_!8486)))
    (let (($x63184 (= ?x64140 ?x63516)))
    (let (($x61198 (or $x199 $x63184)))
    (let (($x60044 (= ?x64223 E1_!8484)))
    (let (($x60153 (or $x197 $x60044)))
    (let (($x64054 (and $x60153 $x61198 $x64456 $x61072 $x64372 $x62270)))
    (let (($x63612 (not $x64054)))
    (let (($x61124 (or $x63612 $x64771)))
    (let (($x64708 (= S1_V6_!8492 S1_V6_!8514)))
    (let (($x61437 (= E2_!8486 E2_!8507)))
    (let (($x63627 (or $x199 $x61437)))
    (let (($x64287 (= E1_!8484 E1_!8508)))
    (let (($x64561 (or $x197 $x64287)))
    (let (($x62829 (and $x64561 $x63627)))
    (let (($x63304 (not $x62829)))
    (let (($x63876 (or $x63304 $x64708)))
    (let (($x64430 (= S1_V4_!8519 S1_V4_!8513)))
    (let (($x63919 (or $x62880 $x64430)))
    (let (($x62726 (= S1_V4_!8519 S1_V4_!8504)))
    (let (($x61329 (= ?x63733 ?x63242)))
    (let (($x62861 (or $x207 $x61329)))
    (let (($x61216 (= ?x64830 ?x62947)))
    (let (($x62937 (or $x205 $x61216)))
    (let (($x64394 (= ?x64187 ?x64769)))
    (let (($x61094 (or $x203 $x64394)))
    (let (($x61005 (= ?x62483 ?x62375)))
    (let (($x62708 (or $x201 $x61005)))
    (let (($x63701 (= ?x64096 E2_!8499)))
    (let (($x62435 (or $x199 $x63701)))
    (let (($x62746 (= ?x64311 ?x64139)))
    (let (($x63675 (or $x197 $x62746)))
    (let (($x63022 (and $x63675 $x62435 $x62708 $x61094 $x62937 $x62861)))
    (let (($x60267 (not $x63022)))
    (let (($x64290 (or $x60267 $x62726)))
    (let (($x59882 (= S1_V4_!8519 S1_V4_!8497)))
    (let (($x61445 (= ?x63733 ?x63195)))
    (let (($x61029 (or $x207 $x61445)))
    (let (($x64890 (= ?x64830 ?x64511)))
    (let (($x62588 (or $x205 $x64890)))
    (let (($x60918 (= ?x64187 ?x62350)))
    (let (($x63861 (or $x203 $x60918)))
    (let (($x64654 (= ?x62483 ?x64163)))
    (let (($x64045 (or $x201 $x64654)))
    (let (($x63629 (= ?x64096 ?x63780)))
    (let (($x61339 (or $x199 $x63629)))
    (let (($x62844 (= ?x64311 ?x64148)))
    (let (($x64265 (or $x197 $x62844)))
    (let (($x61375 (and $x64265 $x61339 $x64045 $x63861 $x62588 $x61029)))
    (let (($x63121 (not $x61375)))
    (let (($x62646 (or $x63121 $x59882)))
    (let (($x63750 (= S1_V4_!8519 S1_V4_!8491)))
    (let (($x63773 (or $x64135 $x63750)))
    (let (($x64251 (= S1_V4_!8513 S1_V4_!8504)))
    (let (($x63618 (= V6_0 ?x63242)))
    (let (($x64239 (or $x207 $x63618)))
    (let (($x60285 (= V4_0 ?x62947)))
    (let (($x64285 (or $x205 $x60285)))
    (let (($x63597 (= V5_0 ?x64769)))
    (let (($x64847 (or $x203 $x63597)))
    (let (($x63774 (= V2_0 ?x62375)))
    (let (($x62330 (or $x201 $x63774)))
    (let (($x62752 (= E2_!8507 E2_!8499)))
    (let (($x64893 (or $x199 $x62752)))
    (let (($x60018 (= E1_!8508 ?x61172)))
    (let (($x63624 (or $x197 $x60018)))
    (let (($x63087 (and $x63624 $x64893 $x62330 $x64847 $x64285 $x64239)))
    (let (($x64431 (not $x63087)))
    (let (($x63809 (or $x64431 $x64251)))
    (let (($x59998 (= S1_V4_!8513 S1_V4_!8491)))
    (let (($x64404 (= E2_!8507 E2_!8486)))
    (let (($x64177 (or $x199 $x64404)))
    (let (($x62508 (= E1_!8508 E1_!8484)))
    (let (($x59853 (or $x197 $x62508)))
    (let (($x64123 (and $x59853 $x64177)))
    (let (($x63426 (not $x64123)))
    (let (($x59875 (or $x63426 $x59998)))
    (let (($x64198 (= S1_V4_!8504 S1_V4_!8491)))
    (let (($x62273 (or $x59909 $x64198)))
    (let (($x60002 (= S1_V4_!8497 S1_V4_!8513)))
    (let (($x60289 (or $x62918 $x60002)))
    (let (($x63870 (= S1_V4_!8497 S1_V4_!8504)))
    (let (($x64191 (= ?x63195 ?x63242)))
    (let (($x63588 (or $x207 $x64191)))
    (let (($x63246 (= ?x64511 ?x62947)))
    (let (($x64521 (or $x205 $x63246)))
    (let (($x61273 (= ?x62350 ?x64769)))
    (let (($x64534 (or $x203 $x61273)))
    (let (($x62395 (= ?x64163 ?x62375)))
    (let (($x64345 (or $x201 $x62395)))
    (let ((?x60227 (+ (- 1) E2_!8499)))
    (let (($x63452 (= ?x64140 ?x60227)))
    (let (($x62984 (or $x199 $x63452)))
    (let (($x63979 (= ?x64223 ?x61172)))
    (let (($x62818 (or $x197 $x63979)))
    (let (($x62278 (and $x62818 $x62984 $x64345 $x64534 $x64521 $x63588)))
    (let (($x62635 (not $x62278)))
    (let (($x62925 (or $x62635 $x63870)))
    (let (($x64172 (= S1_V4_!8497 S1_V4_!8491)))
    (let (($x61186 (or $x63612 $x64172)))
    (let (($x138 (not R_E2_V6)))
    (let (($x62382 (or $x138 $x63618)))
    (let (($x136 (not R_E2_V4)))
    (let (($x59934 (or $x136 $x60285)))
    (let (($x132 (not R_E2_V2)))
    (let (($x63159 (or $x132 $x63774)))
    (let (($x59880 (and $x63159 $x59934 $x62382)))
    (let (($x64567 (not $x59880)))
    (let (($x63783 (or $x64567 $x62752)))
    (let (($x63175 (= E2_!8507 E2_!8485)))
    (let (($x61268 (or $x138 $x63349)))
    (let (($x64737 (or $x136 $x60080)))
    (let (($x59865 (or $x132 $x64229)))
    (let (($x63819 (and $x59865 $x64737 $x61268)))
    (let (($x61271 (not $x63819)))
    (let (($x62949 (or $x61271 $x63200)))
    (let (($x64361 (= E2_!8485 E2_!8499)))
    (let (($x61246 (or $x64567 $x64361)))
    (let (($x63410 (= E2_!8485 E2_!8486)))
    (let (($x64789 (= S1_V5_!8518 S1_V5_!8503)))
    (let (($x59964 (or $x60267 $x64789)))
    (let (($x60052 (= S1_V5_!8518 S1_V5_!8490)))
    (let (($x61068 (or $x64135 $x60052)))
    (let (($x60987 (= S1_V5_!8512 S1_V5_!8518)))
    (let (($x64450 (= V6_0 ?x63733)))
    (let (($x60997 (or $x207 $x64450)))
    (let (($x60960 (= V4_0 ?x64830)))
    (let (($x63488 (or $x205 $x60960)))
    (let (($x63075 (= V5_0 ?x64187)))
    (let (($x61289 (or $x203 $x63075)))
    (let (($x63725 (= V2_0 ?x62483)))
    (let (($x63145 (or $x201 $x63725)))
    (let (($x62355 (= E2_!8507 ?x64096)))
    (let (($x64907 (or $x199 $x62355)))
    (let (($x60930 (= E1_!8508 ?x60890)))
    (let (($x62703 (or $x197 $x60930)))
    (let (($x62788 (and $x62703 $x64907 $x63145 $x61289 $x63488 $x60997)))
    (let (($x62936 (not $x62788)))
    (let (($x60912 (or $x62936 $x60987)))
    (let (($x62576 (= S1_V5_!8512 S1_V5_!8503)))
    (let (($x62986 (or $x64431 $x62576)))
    (let (($x63209 (= S1_V5_!8512 S1_V5_!8490)))
    (let (($x63705 (or $x63426 $x63209)))
    (let (($x64482 (= S1_V5_!8496 S1_V5_!8518)))
    (let (($x63932 (or $x64628 $x64482)))
    (let (($x64549 (= S1_V5_!8496 S1_V5_!8512)))
    (let (($x62836 (or $x62918 $x64549)))
    (let (($x64797 (= S1_V5_!8496 S1_V5_!8503)))
    (let (($x64286 (or $x62635 $x64797)))
    (let (($x64230 (= S1_V5_!8496 S1_V5_!8490)))
    (let (($x59947 (or $x63612 $x64230)))
    (let (($x63832 (= S1_V5_!8490 S1_V5_!8503)))
    (let (($x62607 (= E2_!8486 E2_!8499)))
    (let (($x62612 (or $x199 $x62607)))
    (let (($x63934 (= E1_!8484 ?x61172)))
    (let (($x63806 (or $x197 $x63934)))
    (let (($x63548 (and $x63806 $x62612 $x62330 $x64847 $x64285 $x64239)))
    (let (($x60209 (not $x63548)))
    (let (($x61192 (or $x60209 $x63832)))
    (let (($x63912 (= E1_!8508 E1_!8506)))
    (let (($x63975 (= E1_!8484 E1_!8506)))
    (let (($x60962 (= S1_V2_!8517 S1_V2_!8495)))
    (let (($x60060 (or $x63121 $x60962)))
    (let (($x62954 (= S1_V2_!8517 S1_V2_!8489)))
    (let (($x63813 (or $x64135 $x62954)))
    (let (($x61136 (= S1_V2_!8511 S1_V2_!8517)))
    (let (($x63407 (or $x62936 $x61136)))
    (let (($x62345 (= S1_V2_!8511 S1_V2_!8495)))
    (let (($x62689 (= V6_0 ?x63195)))
    (let (($x63129 (or $x207 $x62689)))
    (let (($x63765 (= V4_0 ?x64511)))
    (let (($x61377 (or $x205 $x63765)))
    (let (($x62764 (= V5_0 ?x62350)))
    (let (($x61457 (or $x203 $x62764)))
    (let (($x63073 (= V2_0 ?x64163)))
    (let (($x62496 (or $x201 $x63073)))
    (let (($x62783 (= E2_!8507 ?x63780)))
    (let (($x63568 (or $x199 $x62783)))
    (let (($x64807 (= E1_!8508 ?x64223)))
    (let (($x61276 (or $x197 $x64807)))
    (let (($x64619 (and $x61276 $x63568 $x62496 $x61457 $x61377 $x63129)))
    (let (($x63514 (not $x64619)))
    (let (($x62725 (or $x63514 $x62345)))
    (let (($x63585 (= S1_V2_!8511 S1_V2_!8489)))
    (let (($x63633 (or $x63426 $x63585)))
    (let (($x60968 (= S1_V2_!8502 S1_V2_!8517)))
    (let (($x63651 (or $x63584 $x60968)))
    (let (($x61425 (= S1_V2_!8502 S1_V2_!8511)))
    (let (($x64005 (or $x64736 $x61425)))
    (let (($x60118 (= S1_V2_!8502 S1_V2_!8495)))
    (let (($x62928 (or $x62833 $x60118)))
    (let (($x60067 (= S1_V2_!8502 S1_V2_!8489)))
    (let (($x64898 (or $x59909 $x60067)))
    (let (($x63321 (= S1_V2_!8489 S1_V2_!8495)))
    (let (($x59929 (= E2_!8486 ?x63780)))
    (let (($x62859 (or $x199 $x59929)))
    (let (($x60088 (= E1_!8484 ?x64223)))
    (let (($x63810 (or $x197 $x60088)))
    (let (($x63729 (and $x63810 $x62859 $x62496 $x61457 $x61377 $x63129)))
    (let (($x62683 (not $x63729)))
    (let (($x62757 (or $x62683 $x63321)))
    (let (($x63950 (= S1_V3_!8516 S1_V3_!8501)))
    (let (($x64985 (or $x60267 $x63950)))
    (let (($x64532 (= S1_V3_!8516 S1_V3_!8488)))
    (let (($x60099 (or $x64135 $x64532)))
    (let (($x62544 (= S1_V3_!8510 S1_V3_!8516)))
    (let (($x60207 (or $x62936 $x62544)))
    (let (($x60241 (= S1_V3_!8510 S1_V3_!8501)))
    (let (($x63785 (or $x64431 $x60241)))
    (let (($x62415 (= S1_V3_!8510 S1_V3_!8494)))
    (let (($x63208 (or $x63514 $x62415)))
    (let (($x62471 (= S1_V3_!8510 S1_V3_!8488)))
    (let (($x63992 (or $x63426 $x62471)))
    (let (($x62352 (= S1_V3_!8494 S1_V3_!8516)))
    (let (($x62409 (or $x64628 $x62352)))
    (let (($x64697 (= S1_V3_!8494 S1_V3_!8501)))
    (let (($x63601 (or $x62635 $x64697)))
    (let (($x63993 (= S1_V3_!8494 S1_V3_!8488)))
    (let (($x63943 (or $x63612 $x63993)))
    (let (($x64659 (= S1_V3_!8488 S1_V3_!8501)))
    (let (($x62847 (or $x60209 $x64659)))
    (let (($x63704 (= S1_V1_!8515 S1_V1_!8509)))
    (let (($x60149 (or $x62880 $x63704)))
    (let (($x63649 (= S1_V1_!8515 S1_V1_!8500)))
    (let (($x61317 (or $x60267 $x63649)))
    (let (($x59962 (= S1_V1_!8515 S1_V1_!8493)))
    (let (($x62565 (or $x63121 $x59962)))
    (let (($x64580 (= S1_V1_!8500 S1_V1_!8509)))
    (let (($x62981 (or $x64736 $x64580)))
    (let (($x63249 (= S1_V1_!8500 S1_V1_!8493)))
    (let (($x61067 (or $x62833 $x63249)))
    (let (($x62530 (= S1_V1_!8493 S1_V1_!8509)))
    (let (($x64131 (or $x62918 $x62530)))
    (let (($x63962 (= S1_V1_!8487 S1_V1_!8515)))
    (let (($x63777 (= E2_!8486 ?x64096)))
    (let (($x62371 (or $x199 $x63777)))
    (let (($x64822 (= E1_!8484 ?x60890)))
    (let (($x64850 (or $x197 $x64822)))
    (let (($x60237 (and $x64850 $x62371 $x63145 $x61289 $x63488 $x60997)))
    (let (($x60910 (not $x60237)))
    (let (($x61196 (or $x60910 $x63962)))
    (let (($x62735 (= S1_V1_!8487 S1_V1_!8509)))
    (let (($x63020 (or $x63304 $x62735)))
    (let (($x64638 (= S1_V1_!8487 S1_V1_!8500)))
    (let (($x64712 (or $x60209 $x64638)))
    (let (($x63769 (= S1_V1_!8487 S1_V1_!8493)))
    (let (($x62511 (or $x62683 $x63769)))
    (let
    (($x63929
      (and $x62511 $x64712 $x63020 $x61196 $x64131 $x61067 $x62981 $x62565
      $x61317 $x60149 $x62847 $x63943 $x63601 $x62409 $x63992 $x63208 $x63785
      $x60207 $x60099 $x64985 $x62757 $x64898 $x62928 $x64005 $x63651 $x63633
      $x62725 $x63407 $x63813 $x60060 $x63975 $x64287 $x63912 $x61192 $x59947
      $x64286 $x62836 $x63932 $x63705 $x62986 $x60912 $x61068 $x59964 $x63410
      $x61246 $x62949 $x63175 $x64404 $x63783 $x61186 $x62925 $x60289 $x62273
      $x59875 $x63809 $x63773 $x62646 $x64290 $x63919 $x63876 $x61124 $x63641
      $x62909 $x63002 $x63622 $x64373 $x64750 $x63815 $x63944 $x64641 $x62498
      $x64147 $x62772 $x64171)))
    (let (($x63590 (not $x63929))) (or $x63590 $x64977 $x62988))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let (($x119 (not R_E1_V5)))
 (let (($x40 (and W_S1_V6 R_S1_V6)))
 (let (($x32 (and W_S1_V3 R_S1_V3)))
 (let (($x30 (and W_S1_V1 R_S1_V1)))
 (let (($x61291 (or $x30 $x32 R_S1_V5 $x40)))
 (let (($x63623 (not $x61291)))
 (let (($x63652 (= DISJ_W_S1_R_S1 $x63623)))
 (let (($x134 (not R_E2_V5)))
 (let (($x199 (not R_S1_V3)))
 (let (($x59792 (not W_S1_V3)))
 (let (($x62785 (or DISJ_W_S1_R_S1 $x59792 $x199)))
 (let (($x59788 (not W_S1_V1)))
 (let (($x63884 (or DISJ_W_S1_R_S1 $x59788)))
 (let (($x59799 (not W_S1_V4)))
 (let (($x59796 (not W_S1_V2)))
 (let (($x115 (not R_E1_V3)))
 (let (($x113 (not R_E1_V1)))
 (let (($x130 (not R_E2_V3)))
 (let (($x128 (not R_E2_V1)))
 (and DISJ_W_S1_R_E2 DISJ_W_S1_R_E1 $x128 $x130 $x113 $x115 $x59796 $x59799
 $x63884 $x62785 W_S1_V5 $x134 $x63652 $x119 $x63315 $x63056 $x63586))))))))))))))))))))))))))
(assert (not DISJ_W_S1_R_S1))
(check-sat)
(exit)

