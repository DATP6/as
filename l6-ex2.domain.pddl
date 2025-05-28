(define (domain lightup)
  (:types
      xpos ;; x positions in the grid
      ypos ;; y positions in the grid
      num  ;; numbers from 0 to 4 to count the number of light bulbs
  )

  (:predicates
      ; You may, or may not, use / modify / remove any one of the following
      ; predicates:

      ;; n2 = n1 + 1
      (increment ?n1 ?n2 - num)

      ;; (?x1, ?y1) is (horizontally or vertically) adjacent to (?x2, ?y2)
      (adjacent ?x - xpos ?y - ypos ?x2 - xpos ?y2 - ypos)

      ;; ?x2 is right of ?x1
      (right ?x1 ?x2 - xpos)

      ;; ?y2 is below of ?y1
      (below ?y1 ?y2 - ypos)

      ;; cell (?x, ?y) is lit-up
      (lit ?x - xpos ?y - ypos)

      ;; cell (?x, ?y) is black
      (black ?x - xpos ?y - ypos)

      ;; ?n many light bulbs are vertically or horizontally adjacent to (?x, ?y)
      ;; (may be only defined for the relevant black cells)
      (surrounded ?x - xpos ?y - ypos ?n - num)

      ; TODO (optional): additional predicate go in here
  )

  ; (:functions
  ;   ()
  ; )
  ;; Place light bulb at given coordinate
  (:action place-bulb
    :parameters (?x - xpos ?y - ypos)
    :precondition (and
        (not (lit ?x ?y))
        (not (black ?x ?y))
        ; We don't check if adjecent cells are already properly surrounded
        ; Instead, that is left to the goal state
    )
    :effect (and
      (forall (?x2 - xpos ?y2 - ypos)
        ; Mega cursed way of increasing surrounded
        (forall (?n1 ?n2 - num)
          (when 
            (and
              (increment ?n1 ?n2)
              (adjacent ?x ?y ?x2 ?y2)
              (surrounded ?x2 ?y2 ?n1)
            )
          f  (and
              (not (surrounded ?x2 ?y2 ?n1))
              (surrounded ?x2 ?y2 ?n2)
            )
          )
        )
        ; 
      )
    )
  )
)
