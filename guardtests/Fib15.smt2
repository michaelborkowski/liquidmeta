(fixpoint "--rewrite")
(fixpoint "--save")

(constant fib  (func(0, [int, int])))

(define fib(n : int) : int = { if (n <= 2) then (1) else (fib (n-2) + fib (n-1)) })

(constraint 
   (forall ((x int) (x == 15 || x == 15)) 
       (( (fib x) = 610 ))
   )
)
