
(set-logic ALL)

(declare-fun X () String)
(declare-fun Y () String)

(assert (not (= (str.++  X Y) (str.++ X Y))))
(check-sat)
(exit)
