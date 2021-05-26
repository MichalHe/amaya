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
 (let (($x63693 (not $x56)))
 (let (($x24 (and W_S1_V6 R_E2_V6)))
 (let (($x60114 (not $x24)))
 (let
 (($x63605
   (forall
    ((V2_0 Int) (V5_0 Int) 
     (V4_0 Int) (V6_0 Int) 
     (MW_S1_V1 Bool) (MW_S1_V3 Bool) 
     (MW_S1_V2 Bool) (MW_S1_V5 Bool) 
     (MW_S1_V4 Bool) (MW_S1_V6 Bool) 
     (S1_V1_!8171 Int) (S1_V1_!8178 Int) 
     (S1_V1_!8187 Int) (S1_V1_!8193 Int) 
     (S1_V3_!8172 Int) (S1_V3_!8179 Int) 
     (S1_V3_!8188 Int) (S1_V3_!8194 Int) 
     (S1_V2_!8173 Int) (S1_V2_!8180 Int) 
     (S1_V2_!8189 Int) (S1_V2_!8195 Int) 
     (E1_!8168 Int) (E1_!8184 Int) 
     (E1_!8186 Int) (S1_V5_!8174 Int) 
     (S1_V5_!8181 Int) (S1_V5_!8190 Int) 
     (S1_V5_!8196 Int) (E2_!8169 Int) 
     (E2_!8170 Int) (E2_!8177 Int) 
     (E2_!8185 Int) (S1_V4_!8175 Int) 
     (S1_V4_!8182 Int) (S1_V4_!8191 Int) 
     (S1_V4_!8197 Int) (S1_V6_!8176 Int) 
     (S1_V6_!8183 Int) (S1_V6_!8192 Int) 
     (S1_V6_!8198 Int))
    (let ((?x63224 (ite MW_S1_V6 S1_V6_!8198 V6_0)))
    (let ((?x64999 (ite MW_S1_V6 S1_V6_!8183 V6_0)))
    (let (($x64189 (= ?x64999 ?x63224)))
    (let ((?x62759 (ite MW_S1_V4 S1_V4_!8197 V4_0)))
    (let ((?x63837 (ite MW_S1_V4 S1_V4_!8182 V4_0)))
    (let (($x60996 (= ?x63837 ?x62759)))
    (let ((?x62706 (ite MW_S1_V5 S1_V5_!8196 V5_0)))
    (let ((?x61007 (ite MW_S1_V5 S1_V5_!8181 V5_0)))
    (let (($x60060 (= ?x61007 ?x62706)))
    (let ((?x63641 (ite MW_S1_V2 S1_V2_!8195 V2_0)))
    (let ((?x63685 (ite MW_S1_V2 S1_V2_!8180 V2_0)))
    (let (($x62791 (= ?x63685 ?x63641)))
    (let ((?x63518 (ite MW_S1_V3 S1_V3_!8194 E2_!8185)))
    (let ((?x60944 (ite MW_S1_V3 S1_V3_!8179 E2_!8177)))
    (let (($x64468 (= ?x60944 ?x63518)))
    (let ((?x64737 (ite MW_S1_V1 S1_V1_!8187 E1_!8186)))
    (let ((?x63809 (+ 1 ?x64737)))
    (let ((?x63701 (ite MW_S1_V1 S1_V1_!8193 ?x63809)))
    (let ((?x60175 (ite MW_S1_V1 S1_V1_!8171 E1_!8168)))
    (let ((?x63851 (+ 1 ?x60175)))
    (let ((?x60271 (ite MW_S1_V1 S1_V1_!8178 ?x63851)))
    (let (($x63834 (= ?x60271 ?x63701)))
    (let (($x63950 (and $x63834 $x64468 $x62791 $x60060 $x60996 $x64189)))
    (let ((?x60183 (+ (- 1) ?x62759)))
    (let (($x61024 (>= ?x63518 ?x60183)))
    (let ((?x61493 (+ (- 1) ?x63641)))
    (let (($x63616 (>= ?x63701 ?x61493)))
    (let ((?x64241 (ite MW_S1_V2 S1_V2_!8189 V2_0)))
    (let (($x63622 (<= ?x64241 ?x63809)))
    (let (($x64979 (not $x63622)))
    (let (($x63817 (<= V2_0 E1_!8186)))
    (let (($x62994 (not $x63817)))
    (let (($x63703 (<= V4_0 E2_!8185)))
    (let (($x60044 (not $x63703)))
    (let (($x61012 (<= V2_0 E1_!8184)))
    (let (($x63209 (not $x61012)))
    (let ((?x64406 (+ (- 1) ?x63685)))
    (let (($x63911 (>= ?x60271 ?x64406)))
    (let ((?x62628 (+ (- 1) ?x63837)))
    (let (($x63521 (>= ?x60944 ?x62628)))
    (let ((?x63390 (ite MW_S1_V4 S1_V4_!8175 V4_0)))
    (let (($x64133 (<= ?x63390 E2_!8177)))
    (let (($x63181 (not $x64133)))
    (let ((?x62571 (ite MW_S1_V2 S1_V2_!8173 V2_0)))
    (let (($x63514 (<= ?x62571 ?x63851)))
    (let (($x63567 (not $x63514)))
    (let ((?x61441 (+ (- 1) ?x63390)))
    (let ((?x63687 (ite MW_S1_V3 S1_V3_!8172 E2_!8170)))
    (let (($x63776 (>= ?x63687 ?x61441)))
    (let (($x61385 (<= V4_0 E2_!8170)))
    (let (($x63161 (not $x61385)))
    (let (($x64895 (<= V2_0 E1_!8168)))
    (let (($x63040 (not $x64895)))
    (let (($x64914 (<= V4_0 E2_!8169)))
    (let (($x61016 (not $x64914)))
    (let
    (($x63128
      (and $x61016 $x63040 $x63161 $x63776 $x63567 $x63181 $x63521 $x63911
      $x63209 $x60044 $x62994 $x64979 $x63616 $x61024)))
    (let (($x64536 (not $x63128)))
    (let (($x61467 (not MW_S1_V6)))
    (let (($x63240 (or $x61467 W_S1_V6)))
    (let (($x64218 (not MW_S1_V4)))
    (let (($x60251 (not MW_S1_V2)))
    (let (($x61305 (not MW_S1_V3)))
    (let (($x64262 (or $x61305 W_S1_V3)))
    (let (($x63426 (not MW_S1_V1)))
    (let (($x63944 (or $x63426 W_S1_V1)))
    (let (($x62537 (= S1_V6_!8198 S1_V6_!8192)))
    (let ((?x62593 (ite MW_S1_V6 S1_V6_!8192 V6_0)))
    (let (($x63619 (= ?x62593 V6_0)))
    (let (($x207 (not R_S1_V6)))
    (let (($x62549 (or $x207 $x63619)))
    (let ((?x62447 (ite MW_S1_V4 S1_V4_!8191 V4_0)))
    (let (($x63109 (= ?x62447 V4_0)))
    (let (($x205 (not R_S1_V4)))
    (let (($x62351 (or $x205 $x63109)))
    (let ((?x63543 (ite MW_S1_V5 S1_V5_!8190 V5_0)))
    (let (($x63588 (= ?x63543 V5_0)))
    (let (($x203 (not R_S1_V5)))
    (let (($x61172 (or $x203 $x63588)))
    (let (($x63759 (= ?x64241 V2_0)))
    (let (($x201 (not R_S1_V2)))
    (let (($x64716 (or $x201 $x63759)))
    (let ((?x63756 (ite MW_S1_V3 S1_V3_!8188 E2_!8185)))
    (let (($x60189 (= ?x63756 E2_!8185)))
    (let (($x199 (not R_S1_V3)))
    (let (($x63319 (or $x199 $x60189)))
    (let ((?x64703 (+ (- 1) E1_!8186)))
    (let (($x63832 (= ?x64737 ?x64703)))
    (let (($x197 (not R_S1_V1)))
    (let (($x62725 (or $x197 $x63832)))
    (let (($x63352 (and $x62725 $x63319 $x64716 $x61172 $x62351 $x62549)))
    (let (($x63876 (not $x63352)))
    (let (($x62335 (or $x63876 $x62537)))
    (let (($x62887 (= S1_V6_!8198 S1_V6_!8183)))
    (let ((?x63935 (ite MW_S1_V6 S1_V6_!8176 V6_0)))
    (let (($x61375 (= ?x62593 ?x63935)))
    (let (($x62407 (or $x207 $x61375)))
    (let (($x64375 (= ?x62447 ?x63390)))
    (let (($x60127 (or $x205 $x64375)))
    (let ((?x63750 (ite MW_S1_V5 S1_V5_!8174 V5_0)))
    (let (($x63661 (= ?x63543 ?x63750)))
    (let (($x62513 (or $x203 $x63661)))
    (let (($x59882 (= ?x64241 ?x62571)))
    (let (($x61233 (or $x201 $x59882)))
    (let (($x64021 (= ?x63756 E2_!8177)))
    (let (($x61229 (or $x199 $x64021)))
    (let (($x62306 (= ?x64737 ?x60175)))
    (let (($x63029 (or $x197 $x62306)))
    (let (($x62853 (and $x63029 $x61229 $x61233 $x62513 $x60127 $x62407)))
    (let (($x63208 (not $x62853)))
    (let (($x64086 (or $x63208 $x62887)))
    (let (($x62606 (= S1_V6_!8198 S1_V6_!8176)))
    (let (($x63507 (= ?x63756 E2_!8170)))
    (let (($x59994 (or $x199 $x63507)))
    (let ((?x62957 (+ (- 1) E1_!8168)))
    (let (($x62476 (= ?x64737 ?x62957)))
    (let (($x62272 (or $x197 $x62476)))
    (let (($x61018 (and $x62272 $x59994 $x64716 $x61172 $x62351 $x62549)))
    (let (($x62851 (not $x61018)))
    (let (($x62825 (or $x62851 $x62606)))
    (let (($x61435 (= S1_V6_!8192 S1_V6_!8183)))
    (let (($x64668 (= V6_0 ?x63935)))
    (let (($x63691 (or $x207 $x64668)))
    (let (($x63823 (= V4_0 ?x63390)))
    (let (($x62797 (or $x205 $x63823)))
    (let (($x62506 (= V5_0 ?x63750)))
    (let (($x61265 (or $x203 $x62506)))
    (let (($x63228 (= V2_0 ?x62571)))
    (let (($x62917 (or $x201 $x63228)))
    (let (($x59863 (= E2_!8185 E2_!8177)))
    (let (($x60008 (or $x199 $x59863)))
    (let (($x62666 (= E1_!8186 ?x63851)))
    (let (($x62776 (or $x197 $x62666)))
    (let (($x62292 (and $x62776 $x60008 $x62917 $x61265 $x62797 $x63691)))
    (let (($x62382 (not $x62292)))
    (let (($x62652 (or $x62382 $x61435)))
    (let (($x63962 (= S1_V6_!8192 S1_V6_!8176)))
    (let (($x62350 (= E2_!8185 E2_!8170)))
    (let (($x61289 (or $x199 $x62350)))
    (let (($x62955 (= E1_!8186 E1_!8168)))
    (let (($x63263 (or $x197 $x62955)))
    (let (($x63213 (and $x63263 $x61289)))
    (let (($x63143 (not $x63213)))
    (let (($x64889 (or $x63143 $x63962)))
    (let (($x63180 (= S1_V6_!8176 S1_V6_!8183)))
    (let (($x63943 (= E2_!8170 E2_!8177)))
    (let (($x64373 (or $x199 $x63943)))
    (let (($x64063 (= E1_!8168 ?x63851)))
    (let (($x62930 (or $x197 $x64063)))
    (let (($x59933 (and $x62930 $x64373 $x62917 $x61265 $x62797 $x63691)))
    (let (($x64446 (not $x59933)))
    (let (($x63105 (or $x64446 $x63180)))
    (let (($x64744 (= S1_V4_!8197 S1_V4_!8182)))
    (let (($x62844 (or $x63208 $x64744)))
    (let (($x64205 (= S1_V4_!8191 S1_V4_!8197)))
    (let (($x63980 (= V6_0 ?x62593)))
    (let (($x63954 (or $x207 $x63980)))
    (let (($x61263 (= V4_0 ?x62447)))
    (let (($x60207 (or $x205 $x61263)))
    (let (($x63088 (= V5_0 ?x63543)))
    (let (($x63191 (or $x203 $x63088)))
    (let (($x61339 (= V2_0 ?x64241)))
    (let (($x62877 (or $x201 $x61339)))
    (let (($x64769 (= E2_!8185 ?x63756)))
    (let (($x59886 (or $x199 $x64769)))
    (let (($x61118 (= E1_!8186 ?x63809)))
    (let (($x61134 (or $x197 $x61118)))
    (let (($x63212 (and $x61134 $x59886 $x62877 $x63191 $x60207 $x63954)))
    (let (($x64345 (not $x63212)))
    (let (($x61068 (or $x64345 $x64205)))
    (let (($x63604 (= S1_V4_!8191 S1_V4_!8182)))
    (let (($x60891 (or $x62382 $x63604)))
    (let (($x62909 (= S1_V4_!8175 S1_V4_!8197)))
    (let (($x63542 (= E2_!8170 ?x63756)))
    (let (($x62637 (or $x199 $x63542)))
    (let (($x62928 (= E1_!8168 ?x63809)))
    (let (($x62565 (or $x197 $x62928)))
    (let (($x63803 (and $x62565 $x62637 $x62877 $x63191 $x60207 $x63954)))
    (let (($x63589 (not $x63803)))
    (let (($x63779 (or $x63589 $x62909)))
    (let (($x63648 (= S1_V4_!8175 S1_V4_!8191)))
    (let (($x62269 (= E2_!8170 E2_!8185)))
    (let (($x64598 (or $x199 $x62269)))
    (let (($x63813 (= E1_!8168 E1_!8186)))
    (let (($x63811 (or $x197 $x63813)))
    (let (($x62712 (and $x63811 $x64598)))
    (let (($x60118 (not $x62712)))
    (let (($x63601 (or $x60118 $x63648)))
    (let (($x62801 (= S1_V4_!8175 S1_V4_!8182)))
    (let (($x63218 (or $x64446 $x62801)))
    (let (($x138 (not R_E2_V6)))
    (let (($x63164 (or $x138 $x64668)))
    (let (($x136 (not R_E2_V4)))
    (let (($x64755 (or $x136 $x63823)))
    (let (($x132 (not R_E2_V2)))
    (let (($x62867 (or $x132 $x63228)))
    (let (($x64630 (and $x62867 $x64755 $x63164)))
    (let (($x62847 (not $x64630)))
    (let (($x64590 (or $x62847 $x59863)))
    (let (($x59873 (= E2_!8185 E2_!8169)))
    (let (($x63623 (= E2_!8177 E2_!8170)))
    (let (($x63875 (= ?x63935 V6_0)))
    (let (($x63705 (or $x138 $x63875)))
    (let (($x63221 (= ?x63390 V4_0)))
    (let (($x64785 (or $x136 $x63221)))
    (let (($x63568 (= ?x62571 V2_0)))
    (let (($x63242 (or $x132 $x63568)))
    (let (($x63453 (and $x63242 $x64785 $x63705)))
    (let (($x62783 (not $x63453)))
    (let (($x60014 (or $x62783 $x63623)))
    (let (($x64169 (= E2_!8177 E2_!8169)))
    (let (($x64650 (or $x62783 $x64169)))
    (let (($x60962 (= E2_!8170 E2_!8169)))
    (let (($x64659 (= S1_V5_!8196 S1_V5_!8181)))
    (let (($x64135 (or $x63208 $x64659)))
    (let (($x63929 (= S1_V5_!8190 S1_V5_!8196)))
    (let (($x62329 (or $x64345 $x63929)))
    (let (($x64034 (= S1_V5_!8190 S1_V5_!8181)))
    (let (($x63778 (or $x62382 $x64034)))
    (let (($x62612 (= S1_V5_!8174 S1_V5_!8196)))
    (let (($x63724 (or $x63589 $x62612)))
    (let (($x60115 (= S1_V5_!8174 S1_V5_!8190)))
    (let (($x63862 (or $x60118 $x60115)))
    (let (($x62508 (= S1_V5_!8174 S1_V5_!8181)))
    (let (($x65137 (or $x64446 $x62508)))
    (let (($x64014 (= E1_!8184 E1_!8186)))
    (let (($x64870 (= E1_!8184 E1_!8168)))
    (let (($x62614 (= S1_V2_!8195 S1_V2_!8180)))
    (let (($x63947 (or $x63208 $x62614)))
    (let (($x62353 (= S1_V2_!8189 S1_V2_!8195)))
    (let (($x62391 (or $x64345 $x62353)))
    (let (($x62451 (= S1_V2_!8189 S1_V2_!8180)))
    (let (($x63585 (or $x62382 $x62451)))
    (let (($x63041 (= S1_V2_!8173 S1_V2_!8195)))
    (let (($x64322 (or $x63589 $x63041)))
    (let (($x62836 (= S1_V2_!8173 S1_V2_!8189)))
    (let (($x64295 (or $x60118 $x62836)))
    (let (($x60924 (= S1_V2_!8173 S1_V2_!8180)))
    (let (($x59964 (or $x64446 $x60924)))
    (let (($x60050 (= S1_V3_!8194 S1_V3_!8172)))
    (let (($x64277 (or $x62851 $x60050)))
    (let (($x64029 (= S1_V3_!8188 S1_V3_!8194)))
    (let (($x64532 (or $x64345 $x64029)))
    (let (($x63121 (= S1_V3_!8188 S1_V3_!8172)))
    (let (($x63166 (or $x63143 $x63121)))
    (let (($x62734 (= S1_V3_!8179 S1_V3_!8194)))
    (let (($x62667 (= ?x63935 ?x62593)))
    (let (($x63902 (or $x207 $x62667)))
    (let (($x63844 (= ?x63390 ?x62447)))
    (let (($x62809 (or $x205 $x63844)))
    (let (($x64557 (= ?x63750 ?x63543)))
    (let (($x64184 (or $x203 $x64557)))
    (let (($x62552 (= ?x62571 ?x64241)))
    (let (($x59876 (or $x201 $x62552)))
    (let (($x64223 (= E2_!8177 ?x63756)))
    (let (($x63870 (or $x199 $x64223)))
    (let (($x63330 (= ?x60175 ?x64737)))
    (let (($x62338 (or $x197 $x63330)))
    (let (($x63450 (and $x62338 $x63870 $x59876 $x64184 $x62809 $x63902)))
    (let (($x63022 (not $x63450)))
    (let (($x59920 (or $x63022 $x62734)))
    (let (($x61309 (= S1_V3_!8179 S1_V3_!8188)))
    (let (($x62817 (or $x207 $x63875)))
    (let (($x63630 (or $x205 $x63221)))
    (let (($x63519 (= ?x63750 V5_0)))
    (let (($x63991 (or $x203 $x63519)))
    (let (($x62740 (or $x201 $x63568)))
    (let (($x63915 (= E2_!8177 E2_!8185)))
    (let (($x64830 (or $x199 $x63915)))
    (let (($x62346 (= ?x60175 ?x64703)))
    (let (($x64697 (or $x197 $x62346)))
    (let (($x62396 (and $x64697 $x64830 $x62740 $x63991 $x63630 $x62817)))
    (let (($x62645 (not $x62396)))
    (let (($x59856 (or $x62645 $x61309)))
    (let (($x62541 (= S1_V3_!8179 S1_V3_!8172)))
    (let (($x64580 (or $x199 $x63623)))
    (let (($x63473 (= ?x60175 ?x62957)))
    (let (($x60223 (or $x197 $x63473)))
    (let (($x64035 (and $x60223 $x64580 $x62740 $x63991 $x63630 $x62817)))
    (let (($x63471 (not $x64035)))
    (let (($x64740 (or $x63471 $x62541)))
    (let (($x63539 (= S1_V1_!8187 S1_V1_!8193)))
    (let (($x62331 (or $x64345 $x63539)))
    (let (($x61321 (= S1_V1_!8178 S1_V1_!8193)))
    (let (($x62594 (or $x63022 $x61321)))
    (let (($x63099 (= S1_V1_!8178 S1_V1_!8187)))
    (let (($x64316 (or $x62645 $x63099)))
    (let (($x64687 (= S1_V1_!8171 S1_V1_!8193)))
    (let (($x63753 (or $x63589 $x64687)))
    (let (($x62925 (= S1_V1_!8171 S1_V1_!8187)))
    (let (($x61011 (or $x60118 $x62925)))
    (let (($x65110 (= S1_V1_!8171 S1_V1_!8178)))
    (let (($x64005 (or $x64446 $x65110)))
    (let
    (($x64356
      (and $x64005 $x61011 $x63753 $x64316 $x62594 $x62331 $x64740 $x59856
      $x59920 $x63166 $x64532 $x64277 $x59964 $x64295 $x64322 $x63585 $x62391
      $x63947 $x64870 $x64014 $x62955 $x65137 $x63862 $x63724 $x63778 $x62329
      $x64135 $x60962 $x64650 $x60014 $x59873 $x62350 $x64590 $x63218 $x63601
      $x63779 $x60891 $x61068 $x62844 $x63105 $x64889 $x62652 $x62825 $x64086
      $x62335 $x63944 $x64262 $x60251 $x64218 $x63240)))
    (let (($x61186 (not $x64356))) (or $x61186 $x64536 $x63950))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let (($x119 (not R_E1_V5)))
 (let (($x40 (and W_S1_V6 R_S1_V6)))
 (let (($x32 (and W_S1_V3 R_S1_V3)))
 (let (($x30 (and W_S1_V1 R_S1_V1)))
 (let (($x62805 (or $x30 $x32 R_S1_V5 $x40)))
 (let (($x63342 (not $x62805)))
 (let (($x63034 (= DISJ_W_S1_R_S1 $x63342)))
 (let (($x134 (not R_E2_V5)))
 (let (($x59788 (not W_S1_V1)))
 (let (($x63884 (or DISJ_W_S1_R_S1 $x59788)))
 (let (($x59799 (not W_S1_V4)))
 (let (($x59796 (not W_S1_V2)))
 (let (($x115 (not R_E1_V3)))
 (let (($x113 (not R_E1_V1)))
 (let (($x130 (not R_E2_V3)))
 (let (($x128 (not R_E2_V1)))
 (and DISJ_W_S1_R_E2 DISJ_W_S1_R_E1 $x128 $x130 $x113 $x115 $x59796 $x59799
 $x63884 W_S1_V5 $x134 $x63034 $x119 $x63605 $x60114 $x63693)))))))))))))))))))))))
(assert (not DISJ_W_S1_R_S1))
(check-sat)
(exit)
