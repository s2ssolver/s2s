
(set-logic QF_SLIA)


(declare-const x String)
(assert (str.in_re x (re.* (str.to_re "A"))))
(assert (str.in_re x (re.* (str.to_re "ABC"))))
(assert (> (str.len x) 0))
(check-sat)


