(set-option :produce-models true)

(declare-datatypes () ((Group  g1 g2 g3 g4 g5)))
(declare-datatypes () ((Supervisor A B C D)))

(declare-fun preference (Group Supervisor) Int)
(declare-fun capacity (Supervisor) Int)
(declare-fun assigned (Group Supervisor) Bool)


(assert (= (preference g1 A) 1))
(assert (= (preference g1 B) 2))
(assert (= (preference g1 C) 3))
(assert (= (preference g1 D) 4))

(assert (= (preference g2 A) 3))
(assert (= (preference g2 B) 4))
(assert (= (preference g2 C) 2))
(assert (= (preference g2 D) 1))


(assert (= (preference g3 A) 4))
(assert (= (preference g3 B) 1))
(assert (= (preference g3 C) 3))
(assert (= (preference g3 D) 2))


(assert (= (preference g4 A) 4))
(assert (= (preference g4 B) 1))
(assert (= (preference g4 C) 2))
(assert (= (preference g4 D) 3))


(assert (= (preference g5 A) 3))
(assert (= (preference g5 B) 1))
(assert (= (preference g5 C) 2))
(assert (= (preference g5 D) 4))


(assert (= (capacity A) 2))
(assert (= (capacity B) 2))
(assert (= (capacity C) 1))
(assert (= (capacity D) 1))

;;; TODO: Add constraints
; First condition
(assert (
    forall ((g Group)) (
        exists ((s Supervisor)) (
            assigned g s
        )
    )
))

(assert
    (forall ((g Group) (s Supervisor) (t Supervisor)) (=> 
        (and (assigned g s) (assigned g t))
        (= s t)
    ))
)

; Second condition
(assert
    (forall ((s Supervisor)) (exists ((g Group)) (assigned g s)))
)

; Third condition

(assert (forall ((s Supervisor))
    ; capacity is 1
    (=> (= (capacity s) 1)
        ; Check condition
        (forall ((g Group) (gg Group))
            (=> 
                (and (assigned g s) (assigned gg s))
                (= g gg)
            )
        )
    )
))

(assert (forall ((s Supervisor))
    ; capacity is 2
    (=> (= (capacity s) 2) 
        ; Check condition
        (forall ((g Group) (gg Group) (ggg Group)) 
            (=> 
                (and (assigned g s) (assigned gg s) (assigned ggg s))
                (not (distinct g gg ggg))
            )
        )
    )
))

; Fourth condition
(assert
    (forall ((g Group) (s Supervisor)) (=> (assigned g s) (<= (preference g s) 2)))
)

;; check and print model
(check-sat)

(echo "group 1:")
(get-value ((assigned g1 A) (assigned g1 B) (assigned g1 C) (assigned g1 D)))

(echo "group 2:")
(get-value ((assigned g2 A) (assigned g2 B) (assigned g2 C) (assigned g2 D)))

(echo "group 3:")
(get-value ((assigned g3 A) (assigned g3 B) (assigned g3 C) (assigned g3 D)))

(echo "group 4:")
(get-value ((assigned g4 A) (assigned g4 B) (assigned g4 C) (assigned g4 D)))

(echo "group 5:")
(get-value ((assigned g5 A) (assigned g5 B) (assigned g5 C) (assigned g5 D)))

(get-model)

(echo "")

