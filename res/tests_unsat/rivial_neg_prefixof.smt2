
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (not (str.prefixof x (str.++ x y))))
(check-sat)