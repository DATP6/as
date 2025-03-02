(set-option :produce-models true)

;;; Appetizers
(declare-datatypes () ((Appetizer MF FF SS HW MS SP)))

;; Weights
(declare-const w1 Int)
(declare-const w2 Int)
(declare-const w3 Int)
(declare-const w4 Int)
(declare-const w5 Int)
(declare-const w6 Int)

;;; Price - Appetizers is a custom type
(declare-fun price (Appetizer) Real)

;;; Function/constant definition using constraints
; Price of each option 
(assert (and
(= (price MF) 2.15)
(= (price FF) 2.75)
(= (price SS) 3.35)
(= (price HW) 3.55)
(= (price MS) 4.20)
(= (price SP) 5.80)
))

;;; Assume non-negative weights for each dish  
(assert (and (>= w1 0) (>= w2 0) (>= w3 0) (>= w4 0) (>= w5 0) (>= w6 0)))


; Sum of options
(assert (=(+ 
(* (price MF) w1) 
(* (price FF) w2) 
(* (price SS) w3) 
(* (price HW) w4) 
(* (price MS) w5) 
(* (price SP) w6)) 	15.05))


;; check and print model
(check-sat)
(get-model)