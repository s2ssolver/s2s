(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.* (re.++ (str.to_re "a") (re.+ (str.to_re "b"))))))
(assert (= (str.to_int x) (- 1)))
(check-sat)

(exit)
