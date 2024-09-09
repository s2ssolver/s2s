(set-logic QF_SLIA)
(declare-fun H () String)

(assert (= (str.++  "ceeeffaaaa" H "fbbbbca" H "aeecdeff" H "fcb" H "eea" H "ebaa")  (str.++  H "eeeffaaaacfbbbbca" H "aee" H "deff" H "f" H "b" H "eea" H "ebaa") ))
(assert (>=(* (str.len H) 20) 20))
(check-sat)
(get-model)
