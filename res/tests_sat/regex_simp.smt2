(declare-const X String)
(assert (str.in_re X (re.++ (str.to_re "x") ((_ re.loop 4 4) (re.union (str.to_re "e") (str.to_re "d"))) (str.to_re "x"))))
(check-sat)
