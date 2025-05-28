(define (domain hamiltonian)
  (:requirements :typing :conditional-effects :action-costs)
  (:types vertex - object)
  (:predicates 
     (connected ?x ?y)
     (visited ?x)
     (at ?x)
  )

  (:functions 
    (path-length ?from ?to - vertex) - number
    (total-cost) - number
  )

  (:action visit
    :parameters (?from ?to - vertex)
    :precondition (and
      (at ?from)
      (not (visited ?to))
      (connected ?from ?to)
    )
    :effect (and
      (at ?to)
      (not (at ?from))
      (visited ?to)
      (increase (total-cost) (path-length ?from ?to))
    )
  )
)
