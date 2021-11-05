(fixpoint "--rewrite")
(fixpoint "--save")

(data Vec 1 = [
  | VNil  { }
  | VCons { head : @(0), tail : Vec @(0)}
])


(constant app (func(2, [(Vec @(0)), (Vec @(0)), (Vec @(0))])))

(define app(xs: (Vec @(0)), ys: (Vec @(0))) : (Vec @(0)) = {
  if (is$VNil xs) then ys else (VCons (head xs) (app (tail xs) ys))
})


(constraint
  (and
    (forall ((ys (Vec @(0))) (true))
      (forall ((zs (Vec @(0))) (true))
        ((app VNil (app ys zs) = app (app VNil ys) zs))
      )
    )
    (forall ((x @(0)) (true))
      (forall ((xs (Vec @(0))) (true))
        (forall ((ys (Vec @(0))) (true))
          (forall ((zs (Vec @(0))) (true))
            (((app (VCons x xs) (app ys zs) = app (app (VCons x xs) ys) zs)))
          )
        )
      )
    )
  )
)
