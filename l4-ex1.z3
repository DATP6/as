(declare-const x0 Bool)
(declare-const x1 Bool)

(declare-const x0p Bool)
(declare-const x1p Bool)

; not c<3
(assert (= x1p x0))
(assert (= x0p (not (or x1 x0))))

; not c<2
;(assert (not x1))
;(assert x1p)

(check-sat)
(get-model)
