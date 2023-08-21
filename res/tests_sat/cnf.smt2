(set-info :smt-lib-version 2.6)
(set-logic ALL)


(declare-fun B () Bool)

(declare-fun A () Bool)



(assert (= A (not B)))
(assert (= B false))

(check-sat)
(exit)
