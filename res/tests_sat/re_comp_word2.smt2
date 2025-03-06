(declare-const X String)
(assert (str.in_re X (re.++ (str.to_re "/filename=") (re.* (re.comp (str.to_re "\x0a"))) (str.to_re ".mks/i\x0a"))))
(check-sat)
