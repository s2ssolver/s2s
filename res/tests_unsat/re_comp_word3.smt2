(set-logic QF_S)
(declare-const X String)
(assert (not (str.in_re X (re.union (str.to_re "0") (re.comp (str.to_re "0"))))))
(check-sat)
