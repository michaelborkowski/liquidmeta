(fixpoint "--rewrite")
(fixpoint "--save")

(constant ack (func(0, [(int), (int), (int)])))

(define ack (n : (int),  x : (int)) : (int) = { 
  (if (n = 0) then (x + 2) else (if (x = 0) then 2 else (ack (n - 1) (ack n (x - 1))))) 
})

(constraint
  (and
    (forall ((x int) (x == 0))
      (forall ((l int) (l < x + 2))
        ((x + l < ack 1 x))
      )
    )
    (forall ((x int) (x > 0))
      (forall ((l int) (l < x + 2))
        ((((x - 1) + (l - 1) < ack 1 (x-1)) => (x + l < ack 1 x)))
      )
    )
  )
)
