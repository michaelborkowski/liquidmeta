me:
check(gamma, e, t) : Prop
synth(gamma, e) : option Type


Today

Ranjit Jhala  to  Everyone 3:45 PM
Check(Gamma, e, t) => C
Forall G, e, t . Let C = Check(Gamma, e, t). IF Valid(C) THEN G |- e : t

Ranjit Jhala  to  Everyone 3:46 PM (Edited)
`G |- e : t`   [POPL]

G |- e << t   [NEW]
G |- e >> t   [NEW]

You  to  Everyone 3:47 PM
forall .... : G |- e << t then G |- e : t

Ranjit Jhala  to  Everyone 3:47 PM (Edited)
* FORALL G,e,t. IF G |- e << t  THEN G |- e : t
* FORALL G,e,t. IF G |- e >> t  THEN G |- e : t

Ranjit Jhala  to  Everyone 3:49 PM
* Forall G, e, t . Let C = Check(Gamma, e, t). IF Valid(C) THEN G |- e << t
CHECK(Gamma, e, t) ==> Option(G |- e << t)
ORACLE :: Gamma => P => Q => Bool
Gamma |- P => Q

Ranjit Jhala  to  Everyone 3:54 PM
```
type Oracle = g:Gamma -> p:Expr -> q:Expr -> Option ( g |- p => q )
```
Check :: Oracle -> g:Gamma -> e: Expr -> t: Type -> Option ( g |- e << t )
Synth :: Oracle -> g:Gamma -> e: Expr -> Option (exists t. g |- e >> t )