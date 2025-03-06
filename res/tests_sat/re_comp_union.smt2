(set-logic QF_S)
(declare-const X String)
(assert (str.in_re X (re.++ (re.+ (re.comp (re.union (str.to_re "") (str.to_re "c")))) (str.to_re "{"))))
(check-sat)
