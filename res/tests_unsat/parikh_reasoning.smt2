(set-logic QF_SLIA)
(declare-const z1 String)
(declare-const t1 String)
(declare-const z2 String)
(declare-const x2 String)
(declare-const x1 String)
(assert (= (str.++ z1 "ba" t1 z2 "dc" x2 "dcxa" x1) (str.++ "ba" z1 t1 "cd" z2 x1 "abdc" x2)))
(check-sat)

