(set-info :status unknown)
(declare-fun |c_old(~a1~0)| () Int)
(declare-fun c_~a1~0 () Int)
(declare-fun c_~a10~0 () Int)
(assert
     (exists ((v_~a1~0_483 Int))
          (and
               (<= |c_old(~a1~0)| v_~a1~0_483)
               (<= (mod v_~a1~0_483 21) (+ c_~a1~0 600000))
               (not (= (mod v_~a1~0_483 21) 0))
               (< v_~a1~0_483 0))))
(check-sat)
