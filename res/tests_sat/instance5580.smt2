(declare-const X String)
; /^SSID=[a-zA-Z\d]{43}\x3B\x20A=[0-3]$/C
(assert (str.in_re X (re.++ (str.to_re "/SSID=") ((_ re.loop 43 43) (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9"))) (str.to_re "; A=") (re.range "0" "3") (str.to_re "/C\x0a"))))
(check-sat)
