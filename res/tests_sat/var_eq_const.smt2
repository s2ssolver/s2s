(set-logic QF_S)


(declare-fun a () String)

(assert (= a "A"))

(check-sat)

