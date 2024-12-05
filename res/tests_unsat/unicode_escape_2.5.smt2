(set-logic QF_S)


(declare-fun x () String)
(declare-fun y () String)

(assert (= x "\x68"))
(assert (= y "h"))
(assert (= x y))


(check-sat)
