{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsSubstitution where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings

{-@ lem_union_subset :: a:S.Set Vname -> { b:S.Set Vname | Set_sub a b}
        ->  c:S.Set Vname -> { pf:_ | Set_sub (Set_cup c a) (Set_cup c b) } @-}
lem_union_subset :: S.Set Vname -> S.Set Vname -> S.Set Vname -> Proof
lem_union_subset a b c = ()

---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION
---------------------------------------------------------------------------

-- Lemmas. The set of Values is closed under substitution.
{-@ lem_subFV_value :: y:Vname -> v_y:Value -> v:Value -> { pf:_ | isValue (subFV y v_y v) } @-}
lem_subFV_value :: Vname -> Expr -> Expr -> Proof
lem_subFV_value y v_y (Bc _)          = ()
lem_subFV_value y v_y (Ic _)          = ()
lem_subFV_value y v_y (Prim _)        = ()
lem_subFV_value y v_y (FV x) 
    | x == y    = () 
    | otherwise = () 
lem_subFV_value y v_y (BV i)          = ()
lem_subFV_value y v_y (Lambda   e)    = ()
lem_subFV_value y v_y (LambdaT   k e) = ()

{-@ lem_subFV_notin :: x:Vname -> v:Value -> { e:Expr | not (Set_mem x (fv e)) } 
                               -> { pf:_ | subFV x v e == e } / [esize e] @-}
lem_subFV_notin :: Vname -> Expr -> Expr -> Proof
lem_subFV_notin x v (Bc b)           = ()
lem_subFV_notin x v (Ic n)           = ()
lem_subFV_notin x v (Prim c)         = ()
lem_subFV_notin x v (BV i)           = ()
lem_subFV_notin x v (FV y)           = ()
lem_subFV_notin x v e@(Lambda   e')  = () ? lem_subFV_notin x v e'
lem_subFV_notin x v (App e1 e2)      = () ? lem_subFV_notin x v e1
                                          ? lem_subFV_notin x v e2
lem_subFV_notin x v (LambdaT   k e') = () ? lem_subFV_notin x v e'
lem_subFV_notin x v (AppT e t)       = () ? lem_subFV_notin x v e
                                          ? lem_tsubFV_notin x v t
lem_subFV_notin x v e@(Let   ew e')  = () ? lem_subFV_notin x v ew
                                          ? lem_subFV_notin x v e'
lem_subFV_notin x v (Annot e' t)     = () ? lem_subFV_notin x v e'
                                          ? lem_tsubFV_notin x v t

{-@ lem_unbind_lc :: x:Vname -> { e:Expr | isLC e } -> { pf:_ | unbind x e == e } / [esize e] @-} 
lem_unbind_lc :: Vname -> Expr -> Proof
lem_unbind_lc x e = lem_open_at_lc_at 0 x 0 0 e

{-@ lem_open_at_lc_at :: j:Index -> x:Vname -> { kx:Index | j >= kx } -> ka:Index 
        -> { e:Expr | isLC_at kx ka e } -> { pf:_ | open_at j x e = e } / [esize e] @-}
lem_open_at_lc_at :: Index -> Vname -> Index -> Index -> Expr -> Proof
lem_open_at_lc_at j x kx ka (Bc _)          = ()
lem_open_at_lc_at j x kx ka (Ic _)          = ()
lem_open_at_lc_at j x kx ka (Prim _)        = ()
lem_open_at_lc_at j x kx ka (BV w)          = ()
lem_open_at_lc_at j x kx ka (FV _)          = ()
lem_open_at_lc_at j x kx ka (Lambda e)
                = () ? lem_open_at_lc_at (j+1) x (kx+1) ka e
lem_open_at_lc_at j x kx ka (App e e')      
                = () ? lem_open_at_lc_at j     x kx     ka e 
                     ? lem_open_at_lc_at j     x kx     ka e'
lem_open_at_lc_at j x kx ka (LambdaT k e) 
                = () ? lem_open_at_lc_at j     x kx     (ka+1) e
lem_open_at_lc_at j x kx ka (AppT e t)      
                = () ? lem_open_at_lc_at   j   x kx     ka e
                     ? lem_openT_at_lct_at j   x kx     ka t
lem_open_at_lc_at j x kx ka (Let ew e)
                = () ? lem_open_at_lc_at   j   x kx     ka ew
                     ? lem_open_at_lc_at (j+1) x (kx+1) ka e
lem_open_at_lc_at j x kx ka (Annot e t)     
                = () ? lem_open_at_lc_at   j   x kx     ka e
                     ? lem_openT_at_lct_at j   x kx     ka t  

{-@ lem_open_tv_at_lc_at :: j:Index -> a:Vname -> kx:Index -> { ka:Index | j >= ka } 
        -> { e:Expr | isLC_at kx ka e } -> { pf:_ | open_tv_at j a e = e } / [esize e] @-}
lem_open_tv_at_lc_at :: Index -> Vname -> Index -> Index -> Expr -> Proof
lem_open_tv_at_lc_at j a kx ka (Bc _)          = ()
lem_open_tv_at_lc_at j a kx ka (Ic _)          = ()
lem_open_tv_at_lc_at j a kx ka (Prim _)        = ()
lem_open_tv_at_lc_at j a kx ka (BV w)          = ()
lem_open_tv_at_lc_at j a kx ka (FV _)          = ()
lem_open_tv_at_lc_at j a kx ka (Lambda e)
                = () ? lem_open_tv_at_lc_at   j   a (kx+1) ka e
lem_open_tv_at_lc_at j a kx ka (App e e')      
                = () ? lem_open_tv_at_lc_at   j   a kx ka e 
                     ? lem_open_tv_at_lc_at   j   a kx ka e'
lem_open_tv_at_lc_at j a kx ka (LambdaT k e) 
                = () ? lem_open_tv_at_lc_at (j+1) a kx (ka+1) e
lem_open_tv_at_lc_at j a kx ka (AppT e t)      
                = () ? lem_open_tv_at_lc_at   j   a kx ka e
                     ? lem_open_tvT_at_lct_at j   a kx ka t
lem_open_tv_at_lc_at j a kx ka (Let ew e)
                = () ? lem_open_tv_at_lc_at   j   a kx ka ew
                     ? lem_open_tv_at_lc_at   j   a (kx+1) ka e
lem_open_tv_at_lc_at j a kx ka (Annot e t)     
                = () ? lem_open_tv_at_lc_at   j   a kx ka e
                     ? lem_open_tvT_at_lct_at j   a kx ka t  

{-@ lem_subBV_lc :: v:Value -> { e:Expr | isLC e } -> { pf:_ | subBV v e == e } / [esize e] @-} 
lem_subBV_lc :: Expr -> Expr -> Proof
lem_subBV_lc v e = lem_subBV_at_lc_at 0 v 0 0 e

{-@ lem_subBV_at_lc_at :: j:Index -> v:Value -> { kx:Index | j >= kx } -> ka:Index 
        -> { e:Expr | isLC_at kx ka e } -> { pf:_ | subBV_at j v e = e } / [esize e] @-}
lem_subBV_at_lc_at :: Index -> Expr -> Index -> Index -> Expr -> Proof
lem_subBV_at_lc_at j v kx ka (Bc _)          = ()
lem_subBV_at_lc_at j v kx ka (Ic _)          = ()
lem_subBV_at_lc_at j v kx ka (Prim _)        = ()
lem_subBV_at_lc_at j v kx ka (BV w)          = ()
lem_subBV_at_lc_at j v kx ka (FV _)          = ()
lem_subBV_at_lc_at j v kx ka (Lambda e)
                = () ? lem_subBV_at_lc_at (j+1) v (kx+1) ka e
lem_subBV_at_lc_at j v kx ka (App e e')      
                = () ? lem_subBV_at_lc_at j     v kx     ka e 
                     ? lem_subBV_at_lc_at j     v kx     ka e'
lem_subBV_at_lc_at j v kx ka (LambdaT k e) 
                = () ? lem_subBV_at_lc_at j     v kx     (ka+1) e
lem_subBV_at_lc_at j v kx ka (AppT e t)      
                = () ? lem_subBV_at_lc_at   j   v kx     ka e
                     ? lem_tsubBV_at_lct_at j   v kx     ka t
lem_subBV_at_lc_at j v kx ka (Let ew e)
                = () ? lem_subBV_at_lc_at   j   v kx     ka ew
                     ? lem_subBV_at_lc_at (j+1) v (kx+1) ka e
lem_subBV_at_lc_at j v kx ka (Annot e t)     
                = () ? lem_subBV_at_lc_at   j   v kx     ka e
                     ? lem_tsubBV_at_lct_at j   v kx     ka t  

{-@ lem_subBTV_at_lc_at :: j:Index -> t_a:UserType -> kx:Index -> { ka:Index | j >= ka }
        -> { e:Expr | isLC_at kx ka e } -> { pf:_ | subBTV_at j t_a e = e } / [esize e] @-}
lem_subBTV_at_lc_at :: Index -> Type -> Index -> Index -> Expr -> Proof
lem_subBTV_at_lc_at j t_a kx ka (Bc _)          = ()
lem_subBTV_at_lc_at j t_a kx ka (Ic _)          = ()
lem_subBTV_at_lc_at j t_a kx ka (Prim _)        = ()
lem_subBTV_at_lc_at j t_a kx ka (BV w)          = ()
lem_subBTV_at_lc_at j t_a kx ka (FV _)          = ()
lem_subBTV_at_lc_at j t_a kx ka (Lambda e)
                = () ? lem_subBTV_at_lc_at j     t_a (kx+1) ka e
lem_subBTV_at_lc_at j t_a kx ka (App e e')      
                = () ? lem_subBTV_at_lc_at j     t_a kx     ka e 
                     ? lem_subBTV_at_lc_at j     t_a kx     ka e'
lem_subBTV_at_lc_at j t_a kx ka (LambdaT k e) 
                = () ? lem_subBTV_at_lc_at (j+1) t_a kx     (ka+1) e
lem_subBTV_at_lc_at j t_a kx ka (AppT e t)      
                = () ? lem_subBTV_at_lc_at   j   t_a kx     ka e
                     ? lem_tsubBTV_at_lct_at j   t_a kx     ka t
lem_subBTV_at_lc_at j t_a kx ka (Let ew e)
                = () ? lem_subBTV_at_lc_at   j   t_a kx     ka ew
                     ? lem_subBTV_at_lc_at   j   t_a (kx+1) ka e
lem_subBTV_at_lc_at j t_a kx ka (Annot e t)     
                = () ? lem_subBTV_at_lc_at   j   t_a kx     ka e
                     ? lem_tsubBTV_at_lct_at j   t_a kx     ka t  

{-@ lem_subBV_is_unbind :: y:Vname -> e:Expr
        -> { pf:_ | subBV (FV y) e == unbind y e } / [esize e] @-}
lem_subBV_is_unbind :: Vname -> Expr -> Proof
lem_subBV_is_unbind y e = lem_subBV_at_is_open_at 0 y e

{-@ lem_subBV_at_is_open_at :: j:Index -> y:Vname -> e:Expr
        -> { pf:_ | subBV_at j (FV y) e == open_at j y e } / [esize e] @-}
lem_subBV_at_is_open_at :: Index -> Vname -> Expr -> Proof
lem_subBV_at_is_open_at j y (Bc b)             = ()
lem_subBV_at_is_open_at j y (Ic n)             = ()
lem_subBV_at_is_open_at j y (Prim c)           = ()
lem_subBV_at_is_open_at j y (BV i) | i == j    = ()
                                   | otherwise = ()
lem_subBV_at_is_open_at j y (FV x)             = ()
lem_subBV_at_is_open_at j y (Lambda e)         = lem_subBV_at_is_open_at (j+1) y e
lem_subBV_at_is_open_at j y (App e e')         = lem_subBV_at_is_open_at j     y e
                                               ? lem_subBV_at_is_open_at j     y e'
lem_subBV_at_is_open_at j y (LambdaT k e)      = lem_subBV_at_is_open_at j     y e
lem_subBV_at_is_open_at j y (AppT e t)         = lem_subBV_at_is_open_at j     y e
                                               ? lem_tsubBV_at_is_openT_at j   y t
lem_subBV_at_is_open_at j y (Let ex e)         = lem_subBV_at_is_open_at j     y ex
                                               ? lem_subBV_at_is_open_at (j+1) y e
lem_subBV_at_is_open_at j y (Annot e t)        = lem_subBV_at_is_open_at j     y e
                                               ? lem_tsubBV_at_is_openT_at j   y t

{-@ lem_subFV_unbind :: y:Vname -> v:Value -> { e:Expr | not (Set_mem y (fv e)) }
        -> { pf:_ | subBV v e == subFV y v (unbind y e) } / [esize e] @-}
lem_subFV_unbind :: Vname -> Expr -> Expr -> Proof
lem_subFV_unbind y v e = lem_subFV_open_at 0 y v e

{-@ lem_subFV_open_at :: j:Index -> y:Vname -> v:Value -> { e:Expr | not (Set_mem y (fv e)) }
        -> { pf:_ | subBV_at j v e == subFV y v (open_at j y e) } / [esize e] @-}
lem_subFV_open_at :: Index -> Vname -> Expr -> Expr -> Proof
lem_subFV_open_at j y v (Bc b)             = ()
lem_subFV_open_at j y v (Ic n)             = ()
lem_subFV_open_at j y v (Prim c)           = ()
lem_subFV_open_at j y v (BV i) | i == j    = ()
                               | otherwise = () 
lem_subFV_open_at j y v (FV w)             = ()
lem_subFV_open_at j y v (Lambda e')        = () ? lem_subFV_open_at (j+1) y v e'
lem_subFV_open_at j y v (App e1 e2)        = () ? lem_subFV_open_at j y v e1
                                                ? lem_subFV_open_at j y v e2
lem_subFV_open_at j y v (LambdaT k e')     = () ? lem_subFV_open_at j y v e'
lem_subFV_open_at j y v (AppT e t)         = () ? lem_subFV_open_at j y v e
                                                ? lem_tsubFV_openT_at j y v t
lem_subFV_open_at j y v e@(Let ew e')      = () ? lem_subFV_open_at j y v ew
                                                ? lem_subFV_open_at (j+1) y v e'
lem_subFV_open_at j y v (Annot e' t)       = () ? lem_subFV_open_at j y v e'
                                                ? lem_tsubFV_openT_at j y v t

{-@ lem_commute_subFV_unbind :: x:Vname -> { v:Value | isLC v } -> { y:Vname | y != x } -> e:Expr
        -> { pf:_ | subFV x v (unbind y e) == unbind y (subFV x v e) } / [esize e] @-}
lem_commute_subFV_unbind :: Vname -> Expr -> Vname -> Expr -> Proof
lem_commute_subFV_unbind x v y e = lem_commute_subFV_open_at x v 0 y e

{-@ lem_commute_subFV_open_at :: x:Vname -> { v:Value | isLC v } -> j:Index -> { y:Vname | y != x }
        -> e:Expr -> { pf:_ | subFV x v (open_at j y e) = open_at j y (subFV x v e) } / [esize e] @-}
lem_commute_subFV_open_at :: Vname -> Expr -> Index -> Vname -> Expr -> Proof
lem_commute_subFV_open_at x v j y (Bc b)       = ()
lem_commute_subFV_open_at x v j y (Ic n)       = ()
lem_commute_subFV_open_at x v j y (Prim p)     = ()
lem_commute_subFV_open_at x v j y (BV k) 
  | j == k    = () 
  | otherwise = ()
lem_commute_subFV_open_at x v j y (FV w)       
  | x == w    = () ? lem_open_at_lc_at j y 0 0 v
  | otherwise = ()
lem_commute_subFV_open_at x v j y (Lambda e)
              = () ? lem_commute_subFV_open_at x v (j+1) y e
lem_commute_subFV_open_at x v j y (App e e')
              = () ? lem_commute_subFV_open_at x v j     y e
                   ? lem_commute_subFV_open_at x v j     y e'
lem_commute_subFV_open_at x v j y (LambdaT k e)
              = () ? lem_commute_subFV_open_at x v j     y e
lem_commute_subFV_open_at x v j y (AppT e t)
              = () ? lem_commute_subFV_open_at   x v j   y e
                   ? lem_commute_tsubFV_openT_at x v j   y t
lem_commute_subFV_open_at x v j y (Let ew e)
              = () ? lem_commute_subFV_open_at x v j     y ew
                   ? lem_commute_subFV_open_at x v (j+1) y e
lem_commute_subFV_open_at x v j y (Annot e t)
              = () ? lem_commute_subFV_open_at   x v j   y e
                   ? lem_commute_tsubFV_openT_at x v j   y t

{-@ lem_commute_subFV_subBV :: v:Value -> y:Vname -> { v_y:Value | isLC v_y } -> e:Expr
        -> { pf:_ | subFV y v_y (subBV v e) == subBV (subFV y v_y v) (subFV y v_y e) } @-}
lem_commute_subFV_subBV :: Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV v y v_y e = lem_commute_subFV_subBV_at 0 v y v_y e

{-@ lem_commute_subFV_subBV_at :: j:Index -> v:Value -> y:Vname -> { v_y:Value | isLC v_y } -> e:Expr
      -> { pf:_ | subFV y v_y (subBV_at j v e) == subBV_at j (subFV y v_y v) (subFV y v_y e) } 
       / [esize e] @-}
lem_commute_subFV_subBV_at :: Index -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV_at j v y v_y (Bc b)       = ()
lem_commute_subFV_subBV_at j v y v_y (Ic n)       = ()
lem_commute_subFV_subBV_at j v y v_y (Prim p)     = ()
lem_commute_subFV_subBV_at j v y v_y (BV k) 
  | j == k    = ()
  | otherwise = ()
lem_commute_subFV_subBV_at j v y v_y (FV w)       
  | y == w    = () ? lem_subBV_at_lc_at j (subFV y v_y v) 0 0 v_y
  | otherwise = ()
lem_commute_subFV_subBV_at j v y v_y (Lambda e)
              = () ? lem_commute_subFV_subBV_at (j+1) v y v_y e
lem_commute_subFV_subBV_at j v y v_y (App e e')
              = () ? lem_commute_subFV_subBV_at j v y v_y e
                   ? lem_commute_subFV_subBV_at j v y v_y e'
lem_commute_subFV_subBV_at j v y v_y (LambdaT k e)
              = () ? lem_commute_subFV_subBV_at   j v y v_y e
lem_commute_subFV_subBV_at j v y v_y (AppT e t)
              = () ? lem_commute_subFV_subBV_at   j v y v_y e
                   ? lem_commute_tsubFV_tsubBV_at j v y v_y t
lem_commute_subFV_subBV_at j v y v_y (Let ew e)
              = () ? lem_commute_subFV_subBV_at j     v y v_y ew
                   ? lem_commute_subFV_subBV_at (j+1) v y v_y e
lem_commute_subFV_subBV_at j v y v_y (Annot e t)
              = () ? lem_commute_subFV_subBV_at   j v y v_y e
                   ? lem_commute_tsubFV_tsubBV_at j v y v_y t

{-@ lem_commute_subFV_unbind_tv :: x:Vname -> { v:Value | isLC v } -> { a:Vname | a != x } -> e:Expr
        -> { pf:_ | subFV x v (unbind_tv a e) == unbind_tv a (subFV x v e) } / [esize e] @-}
lem_commute_subFV_unbind_tv :: Vname -> Expr -> Vname -> Expr -> Proof
lem_commute_subFV_unbind_tv x v a e = lem_commute_subFV_open_tv_at x v 0 a e

{-@ lem_commute_subFV_open_tv_at :: x:Vname -> { v:Value | isLC v } -> j:Index -> { a:Vname | a != x }
        -> e:Expr -> { pf:_ | subFV x v (open_tv_at j a e) = open_tv_at j a (subFV x v e) } / [esize e] @-}
lem_commute_subFV_open_tv_at :: Vname -> Expr -> Index -> Vname -> Expr -> Proof
lem_commute_subFV_open_tv_at x v j a (Bc b)       = ()
lem_commute_subFV_open_tv_at x v j a (Ic n)       = ()
lem_commute_subFV_open_tv_at x v j a (Prim p)     = ()
lem_commute_subFV_open_tv_at x v j a (BV k)       = ()
lem_commute_subFV_open_tv_at x v j a (FV w)       
  | x == w    = () ? lem_open_tv_at_lc_at j a 0 0 v
  | otherwise = ()
lem_commute_subFV_open_tv_at x v j a (Lambda e)
              = () ? lem_commute_subFV_open_tv_at x v j     a e
lem_commute_subFV_open_tv_at x v j a (App e e')
              = () ? lem_commute_subFV_open_tv_at x v j     a e
                   ? lem_commute_subFV_open_tv_at x v j     a e'
lem_commute_subFV_open_tv_at x v j a (LambdaT k e)
              = () ? lem_commute_subFV_open_tv_at x v (j+1) a e
lem_commute_subFV_open_tv_at x v j a (AppT e t)
              = () ? lem_commute_subFV_open_tv_at   x v j   a e
                   ? lem_commute_tsubFV_open_tvT_at x v j   a t
lem_commute_subFV_open_tv_at x v j a (Let ew e)
              = () ? lem_commute_subFV_open_tv_at x v j     a ew
                   ? lem_commute_subFV_open_tv_at x v j     a e
lem_commute_subFV_open_tv_at x v j a (Annot e t)
              = () ? lem_commute_subFV_open_tv_at   x v j   a e
                   ? lem_commute_tsubFV_open_tvT_at x v j   a t

{-@ lem_commute_subFV_subBTV_at :: j:Index -> t_a:UserType  -> y:Vname -> { v_y:Value | isLC v_y } 
      -> e:Expr
      -> { pf:_ | subFV y v_y (subBTV_at j t_a e) == subBTV_at j (tsubFV y v_y t_a) (subFV y v_y e) } 
       / [esize e] @-}
lem_commute_subFV_subBTV_at :: Index -> Type -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBTV_at j t_a y v_y (Bc b)       = ()
lem_commute_subFV_subBTV_at j t_a y v_y (Ic n)       = ()
lem_commute_subFV_subBTV_at j t_a y v_y (Prim p)     = ()
lem_commute_subFV_subBTV_at j t_a y v_y (BV w)       = ()
lem_commute_subFV_subBTV_at j t_a y v_y (FV w)       
  | y == w    = () ? lem_subBTV_at_lc_at j (tsubFV y v_y t_a) 0 0 v_y
  | otherwise = ()
lem_commute_subFV_subBTV_at j t_a y v_y (Lambda e)
              = () ? lem_commute_subFV_subBTV_at j t_a y v_y e
lem_commute_subFV_subBTV_at j t_a y v_y (App e e')
              = () ? lem_commute_subFV_subBTV_at j t_a y v_y e
                   ? lem_commute_subFV_subBTV_at j t_a y v_y e'
lem_commute_subFV_subBTV_at j t_a y v_y (LambdaT k e)
              = () ? lem_commute_subFV_subBTV_at (j+1) t_a y v_y e
lem_commute_subFV_subBTV_at j t_a y v_y (AppT e t)
              = () ? lem_commute_subFV_subBTV_at   j t_a y v_y e
                   ? lem_commute_tsubFV_tsubBTV_at j t_a y v_y t
lem_commute_subFV_subBTV_at j t_a y v_y (Let ew e)
              = () ? lem_commute_subFV_subBTV_at j t_a y v_y ew
                   ? lem_commute_subFV_subBTV_at j t_a y v_y e
lem_commute_subFV_subBTV_at j t_a y v_y (Annot e t)
              = () ? lem_commute_subFV_subBTV_at   j t_a y v_y e
                   ? lem_commute_tsubFV_tsubBTV_at j t_a y v_y t

------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in TERMS
------------------------------------------------------------------------------

{-@ lem_subFTV_notin :: a:Vname -> t:UserType -> { e:Expr | not (Set_mem a (ftv e)) } 
                                -> { pf:_ | subFTV a t e == e } / [esize e] @-}
lem_subFTV_notin :: Vname -> Type -> Expr -> Proof
lem_subFTV_notin a t (Bc b)         = ()
lem_subFTV_notin a t (Ic n)         = ()
lem_subFTV_notin a t (Prim c)       = ()
lem_subFTV_notin a t (BV y)         = ()
lem_subFTV_notin a t (FV y)         = ()
lem_subFTV_notin a t e@(Lambda e')  = () ? lem_subFTV_notin  a t e'
lem_subFTV_notin a t (App e1 e2)    = () ? lem_subFTV_notin  a t e1
                                         ? lem_subFTV_notin  a t e2
lem_subFTV_notin a t (LambdaT  k e) = () ? lem_subFTV_notin  a t e
lem_subFTV_notin a t (AppT e' t')   = () ? lem_subFTV_notin  a t e'
                                         ? lem_tsubFTV_notin a t t'  
lem_subFTV_notin a t e@(Let ew e')  = () ? lem_subFTV_notin  a t ew
                                         ? lem_subFTV_notin  a t e'
lem_subFTV_notin a t (Annot e' t')  = () ? lem_subFTV_notin  a t e'
                                         ? lem_tsubFTV_notin a t t'

{-@ lem_subFTV_unbind_tv :: a':Vname -> t:UserType -> { e:Expr | not (Set_mem a' (ftv e)) }
      -> { pf:_ | subBTV t e == subFTV a' t (unbind_tv a' e) } / [esize e] @-}
lem_subFTV_unbind_tv :: Vname -> Type -> Expr -> Proof
lem_subFTV_unbind_tv a t e = lem_subFTV_open_tv_at 0 a t e

{-@ lem_subFTV_open_tv_at :: j:Index -> a':Vname -> t:UserType 
      -> { e:Expr | not (Set_mem a' (ftv e)) }
      -> { pf:_ | subBTV_at j t e == subFTV a' t (open_tv_at j a' e) } / [esize e] @-}
lem_subFTV_open_tv_at :: Index -> Vname -> Type -> Expr -> Proof
lem_subFTV_open_tv_at j a' t (Bc b)         = ()
lem_subFTV_open_tv_at j a' t (Ic n)         = ()
lem_subFTV_open_tv_at j a' t (Prim c)       = ()
lem_subFTV_open_tv_at j a' t (BV w)         = ()
lem_subFTV_open_tv_at j a' t (FV w)         = ()
lem_subFTV_open_tv_at j a' t (Lambda e')    = () ? lem_subFTV_open_tv_at j a' t e'
lem_subFTV_open_tv_at j a' t (App e1 e2)    = () ? lem_subFTV_open_tv_at j a' t e1
                                                 ? lem_subFTV_open_tv_at j a' t e2
lem_subFTV_open_tv_at j a' t (LambdaT k e') = () ? lem_subFTV_open_tv_at (j+1) a' t e'
lem_subFTV_open_tv_at j a' t (AppT e' t')   = () ? lem_subFTV_open_tv_at j a' t e'  
                                                 ? lem_tsubFTV_open_tvT_at j a' t t'
lem_subFTV_open_tv_at j a' t (Let ew e')    = () ? lem_subFTV_open_tv_at j a' t ew
                                                 ? lem_subFTV_open_tv_at j a' t e'
lem_subFTV_open_tv_at j a' t (Annot e' t')  = () ? lem_subFTV_open_tv_at   j a' t e'
                                                 ? lem_tsubFTV_open_tvT_at j a' t t'

{-@ lem_commute_subFTV_unbind :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> { y:Vname | y != a } -> e:Expr
        -> { pf:_ | subFTV a t_a (unbind y e) == unbind y (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV_unbind :: Vname -> Type -> Vname -> Expr -> Proof
lem_commute_subFTV_unbind a t_a y e = lem_commute_subFTV_open_at a t_a 0 y e

{-@ lem_commute_subFTV_open_at :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> j:Index -> { y:Vname | y != a } -> e:Expr 
        -> { pf:_ | subFTV a t_a (open_at j y e) = open_at j y (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV_open_at :: Vname -> Type -> Index -> Vname -> Expr -> Proof
lem_commute_subFTV_open_at a t_a j y (Bc b)       = ()
lem_commute_subFTV_open_at a t_a j y (Ic n)       = ()
lem_commute_subFTV_open_at a t_a j y (Prim p)     = ()
lem_commute_subFTV_open_at a t_a j y (BV k) 
  | j == k    = () 
  | otherwise = ()
lem_commute_subFTV_open_at a t_a j y (FV w)       = ()
lem_commute_subFTV_open_at a t_a j y (Lambda e)
              = () ? lem_commute_subFTV_open_at a t_a (j+1) y e
lem_commute_subFTV_open_at a t_a j y (App e e')
              = () ? lem_commute_subFTV_open_at a t_a j     y e
                   ? lem_commute_subFTV_open_at a t_a j     y e'
lem_commute_subFTV_open_at a t_a j y (LambdaT k e)
              = () ? lem_commute_subFTV_open_at a t_a j     y e
lem_commute_subFTV_open_at a t_a j y (AppT e t)
              = () ? lem_commute_subFTV_open_at   a t_a j   y e
                   ? lem_commute_tsubFTV_openT_at a t_a j   y t
lem_commute_subFTV_open_at a t_a j y (Let ew e)
              = () ? lem_commute_subFTV_open_at a t_a j     y ew
                   ? lem_commute_subFTV_open_at a t_a (j+1) y e
lem_commute_subFTV_open_at a t_a j y (Annot e t)
              = () ? lem_commute_subFTV_open_at   a t_a j   y e
                   ? lem_commute_tsubFTV_openT_at a t_a j   y t

{-@ lem_commute_subFTV_unbind_tv :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> { a':Vname | a' != a } -> e:Expr
        -> { pf:_ | subFTV a t_a (unbind_tv a' e) == unbind_tv a' (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV_unbind_tv :: Vname -> Type -> Vname -> Expr -> Proof
lem_commute_subFTV_unbind_tv a t_a a' e = lem_commute_subFTV_open_tv_at a t_a 0 a' e

{-@ lem_commute_subFTV_open_tv_at :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> j:Index -> { a':Vname | a' != a } -> e:Expr 
        -> { pf:_ | subFTV a t_a (open_tv_at j a' e) = open_tv_at j a' (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV_open_tv_at :: Vname -> Type -> Index -> Vname -> Expr -> Proof
lem_commute_subFTV_open_tv_at a t_a j a' (Bc b)       = ()
lem_commute_subFTV_open_tv_at a t_a j a' (Ic n)       = ()
lem_commute_subFTV_open_tv_at a t_a j a' (Prim p)     = ()
lem_commute_subFTV_open_tv_at a t_a j a' (BV k)       = ()
lem_commute_subFTV_open_tv_at a t_a j a' (FV w)       = ()
lem_commute_subFTV_open_tv_at a t_a j a' (Lambda e)
              = () ? lem_commute_subFTV_open_tv_at a t_a j     a' e
lem_commute_subFTV_open_tv_at a t_a j a' (App e e')
              = () ? lem_commute_subFTV_open_tv_at a t_a j     a' e
                   ? lem_commute_subFTV_open_tv_at a t_a j     a' e'
lem_commute_subFTV_open_tv_at a t_a j a' (LambdaT k e)
              = () ? lem_commute_subFTV_open_tv_at a t_a (j+1) a' e
lem_commute_subFTV_open_tv_at a t_a j a' (AppT e t)
              = () ? lem_commute_subFTV_open_tv_at   a t_a j   a' e
                   ? lem_commute_tsubFTV_open_tvT_at a t_a j   a' t
lem_commute_subFTV_open_tv_at a t_a j a' (Let ew e)
              = () ? lem_commute_subFTV_open_tv_at a t_a j     a' ew
                   ? lem_commute_subFTV_open_tv_at a t_a j     a' e
lem_commute_subFTV_open_tv_at a t_a j a' (Annot e t)
              = () ? lem_commute_subFTV_open_tv_at   a t_a j   a' e
                   ? lem_commute_tsubFTV_open_tvT_at a t_a j   a' t

------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in TERMS
------------------------------------------------------------------------------

{-@ lem_commute_subFTV_subBV_at :: j:Index -> v:Value 
        -> a:Vname -> { t_a:UserType | isLCT t_a } -> e:Expr
        -> { pf:_ | subFTV a t_a (subBV_at j v e) == subBV_at j (subFTV a t_a v) (subFTV a t_a e) } 
         / [esize e] @-}
lem_commute_subFTV_subBV_at :: Index -> Expr -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBV_at j v a t_a (Bc b)       = ()
lem_commute_subFTV_subBV_at j v a t_a (Ic n)       = ()
lem_commute_subFTV_subBV_at j v a t_a (Prim p)     = ()
lem_commute_subFTV_subBV_at j v a t_a (BV k) 
  | j == k    = () -- ? lem_subFV_notin y v_y (BV x)
  | otherwise = ()
lem_commute_subFTV_subBV_at j v a t_a (FV w)       = () 
lem_commute_subFTV_subBV_at j v a t_a (Lambda e)
              = () ? lem_commute_subFTV_subBV_at (j+1) v a t_a e
lem_commute_subFTV_subBV_at j v a t_a (App e e')
              = () ? lem_commute_subFTV_subBV_at j v a t_a e
                   ? lem_commute_subFTV_subBV_at j v a t_a e'
lem_commute_subFTV_subBV_at j v a t_a (LambdaT k e)
              = () ? lem_commute_subFTV_subBV_at j v a t_a e
lem_commute_subFTV_subBV_at j v a t_a (AppT e t) 
              = () ? lem_commute_subFTV_subBV_at   j v a t_a e
                   ? lem_commute_tsubFTV_tsubBV_at j v a t_a t
lem_commute_subFTV_subBV_at j v a t_a (Let ew e)
              = () ? lem_commute_subFTV_subBV_at j v a t_a ew
                   ? lem_commute_subFTV_subBV_at (j+1) v a t_a e
lem_commute_subFTV_subBV_at j v a t_a (Annot e t)
              = () ? lem_commute_subFTV_subBV_at   j v a t_a e
                   ? lem_commute_tsubFTV_tsubBV_at j v a t_a t


{-@ lem_commute_subFTV_subBTV_at :: j:Index -> t1:UserType
        -> a:Vname -> { t_a:UserType | isLCT t_a } -> e:Expr
        -> { pf:_ | subFTV a t_a (subBTV_at j t1 e) == subBTV_at j (tsubFTV a t_a t1) (subFTV a t_a e) }
         / [esize e] @-}
lem_commute_subFTV_subBTV_at :: Index -> Type -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBTV_at j t1 a t_a (Bc b)       = ()
lem_commute_subFTV_subBTV_at j t1 a t_a (Ic n)       = ()
lem_commute_subFTV_subBTV_at j t1 a t_a (Prim p)     = ()
lem_commute_subFTV_subBTV_at j t1 a t_a (BV w)       = ()
lem_commute_subFTV_subBTV_at j t1 a t_a (FV w)       = () 
lem_commute_subFTV_subBTV_at j t1 a t_a (Lambda e)
              = () ? lem_commute_subFTV_subBTV_at j t1 a t_a e
lem_commute_subFTV_subBTV_at j t1 a t_a (App e e')
              = () ? lem_commute_subFTV_subBTV_at j t1 a t_a e
                   ? lem_commute_subFTV_subBTV_at j t1 a t_a e'
lem_commute_subFTV_subBTV_at j t1 a t_a (LambdaT k e)
              = () ? lem_commute_subFTV_subBTV_at (j+1) t1 a t_a e
lem_commute_subFTV_subBTV_at j t1 a t_a (AppT e t) 
              = () ? lem_commute_subFTV_subBTV_at   j t1 a t_a e
                   ? lem_commute_tsubFTV_tsubBTV_at j t1 a t_a t
lem_commute_subFTV_subBTV_at j t1 a t_a (Let ew e)
              = () ? lem_commute_subFTV_subBTV_at j t1 a t_a ew
                   ? lem_commute_subFTV_subBTV_at j t1 a t_a e
lem_commute_subFTV_subBTV_at j t1 a t_a (Annot e t)
              = () ? lem_commute_subFTV_subBTV_at   j t1 a t_a e
                   ? lem_commute_tsubFTV_tsubBTV_at j t1 a t_a t

----------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TERM VARIABLES in PREDICATES
----------------------------------------------------------------------------------

{-@ lem_psubFV_notin :: x:Vname -> v:Value -> { ps:Preds | not (Set_mem x (fvP ps)) }
                                -> { pf:_ | psubFV x v ps == ps } / [predsize ps] @-}
lem_psubFV_notin :: Vname -> Expr -> Preds -> Proof
lem_psubFV_notin x v PEmpty       = ()
lem_psubFV_notin x v (PCons p ps) =    lem_subFV_notin x v p
                                     ? lem_psubFV_notin x v ps

{-@ lem_psubFTV_notin :: a:Vname -> t_a:UserType -> { ps:Preds | not (Set_mem a (ftvP ps)) }
                                 -> { pf:_ | psubFTV a t_a ps == ps } / [predsize ps] @-}
lem_psubFTV_notin :: Vname -> Type -> Preds -> Proof
lem_psubFTV_notin a t_a PEmpty       = ()
lem_psubFTV_notin a t_a (PCons p ps) =    lem_subFTV_notin  a t_a p
                                        ? lem_psubFTV_notin a t_a ps

{-@ lem_openP_at_lcp_at :: j:Index -> x:Vname -> { kx:Index | j >= kx } -> ka:Index 
        -> { ps:Preds | isLCP_at kx ka ps } -> { pf:_ | openP_at j x ps = ps } / [predsize ps] @-}
lem_openP_at_lcp_at :: Index -> Vname -> Index -> Index -> Preds -> Proof
lem_openP_at_lcp_at j x kx ka PEmpty       = ()
lem_openP_at_lcp_at j x kx ka (PCons p ps) = () ? lem_open_at_lc_at   j x kx ka p
                                                ? lem_openP_at_lcp_at j x kx ka ps

{-@ lem_psubBV_at_lcp_at :: j:Index -> v:Value -> { kx:Index | j >= kx } -> ka:Index 
        -> { ps:Preds | isLCP_at kx ka ps } -> { pf:_ | psubBV_at j v ps = ps } / [predsize ps] @-}
lem_psubBV_at_lcp_at :: Index -> Expr -> Index -> Index -> Preds -> Proof
lem_psubBV_at_lcp_at j v kx ka PEmpty       = ()
lem_psubBV_at_lcp_at j v kx ka (PCons p ps) = () ? lem_subBV_at_lc_at   j v kx ka p
                                                 ? lem_psubBV_at_lcp_at j v kx ka ps

{-@ lem_open_tvP_at_lcp_at :: j:Index -> a:Vname -> kx:Index -> { ka:Index | j >= ka } 
        -> { ps:Preds | isLCP_at kx ka ps } -> { pf:_ | open_tvP_at j a ps = ps } / [predsize ps] @-}
lem_open_tvP_at_lcp_at :: Index -> Vname -> Index -> Index -> Preds -> Proof
lem_open_tvP_at_lcp_at j a kx ka PEmpty       = ()
lem_open_tvP_at_lcp_at j a kx ka (PCons p ps) = () ? lem_open_tv_at_lc_at   j a kx ka p
                                                   ? lem_open_tvP_at_lcp_at j a kx ka ps

{-@ lem_psubBTV_at_lcp_at :: j:Index -> t_a:UserType -> kx:Index -> { ka:Index | j >= ka } 
        -> { ps:Preds | isLCP_at kx ka ps } -> { pf:_ | psubBTV_at j t_a ps = ps } / [predsize ps] @-}
lem_psubBTV_at_lcp_at :: Index -> Type -> Index -> Index -> Preds -> Proof
lem_psubBTV_at_lcp_at j t_a kx ka PEmpty       = ()
lem_psubBTV_at_lcp_at j t_a kx ka (PCons p ps) = () ? lem_subBTV_at_lc_at   j t_a kx ka p
                                                    ? lem_psubBTV_at_lcp_at j t_a kx ka ps

{-@ lem_psubBV_at_is_openP_at :: j:Index -> y:Vname -> ps:Preds
        -> { pf:_ | psubBV_at j (FV y) ps == openP_at j y ps } / [predsize ps] @-}
lem_psubBV_at_is_openP_at :: Index -> Vname -> Preds -> Proof
lem_psubBV_at_is_openP_at j y PEmpty       = ()
lem_psubBV_at_is_openP_at j y (PCons p ps) = lem_subBV_at_is_open_at   j y p
                                           ? lem_psubBV_at_is_openP_at j y ps

{-@ lem_psubFV_openP_at :: j:Index -> y:Vname -> v:Value -> { ps:Preds | not (Set_mem y (fvP ps)) }
        -> { pf:_ | psubBV_at j v ps == psubFV y v (openP_at j y ps) } / [predsize ps] @-}
lem_psubFV_openP_at :: Index -> Vname -> Expr -> Preds -> Proof
lem_psubFV_openP_at j y v (PEmpty)       = ()
lem_psubFV_openP_at j y v (PCons p ps)   = () ? lem_subFV_open_at j y v p
                                              ? lem_psubFV_openP_at j y v ps

{-@ lem_psubFTV_open_tvP_at :: j:Index -> a:Vname -> t_a:UserType 
        -> { ps:Preds | not (Set_mem a (ftvP ps)) }
        -> { pf:_ | psubBTV_at j t_a ps == psubFTV a t_a (open_tvP_at j a ps) } / [predsize ps] @-}
lem_psubFTV_open_tvP_at :: Index -> Vname -> Type -> Preds -> Proof
lem_psubFTV_open_tvP_at j a t_a (PEmpty)       = ()
lem_psubFTV_open_tvP_at j a t_a (PCons p ps)   = () ? lem_subFTV_open_tv_at   j a t_a p
                                                    ? lem_psubFTV_open_tvP_at j a t_a ps

{-@ lem_commute_psubFV_unbindP :: x:Vname -> { v:Value | isLC v } -> { y:Vname | x != y } -> ps:Preds
        -> { pf:_ | psubFV x v (unbindP y ps) = unbindP y (psubFV x v ps) } / [predsize ps] @-}
lem_commute_psubFV_unbindP :: Vname -> Expr -> Vname -> Preds -> Proof
lem_commute_psubFV_unbindP x v y PEmpty       = ()
lem_commute_psubFV_unbindP x v y (PCons p ps) = () ? lem_commute_subFV_unbind   x v y p
                                                   ? lem_commute_psubFV_unbindP x v y ps

{-@ lem_commute_psubFV_openP_at :: x:Vname -> { v:Value | isLC v } 
        -> j:Index -> { y:Vname | x != y } -> ps:Preds
        -> { pf:_ | psubFV x v (openP_at j y ps) = openP_at j y (psubFV x v ps) } / [predsize ps] @-}
lem_commute_psubFV_openP_at :: Vname -> Expr -> Index -> Vname -> Preds -> Proof
lem_commute_psubFV_openP_at x v j y PEmpty       = ()
lem_commute_psubFV_openP_at x v j y (PCons p ps) = () ? lem_commute_subFV_open_at   x v j y p
                                                      ? lem_commute_psubFV_openP_at x v j y ps

{-@ lem_commute_psubFV_psubBV_at :: j:Index -> v:Value -> y:Vname -> { v_y:Value | isLC v_y } 
      -> ps:Preds
      -> { pf:_ | psubFV y v_y (psubBV_at j v ps) == psubBV_at j (subFV y v_y v) (psubFV y v_y ps) } 
       / [predsize ps] @-}
lem_commute_psubFV_psubBV_at :: Index -> Expr -> Vname -> Expr -> Preds -> Proof
lem_commute_psubFV_psubBV_at j v y v_y PEmpty       = ()
lem_commute_psubFV_psubBV_at j v y v_y (PCons p ps) = () ? lem_commute_subFV_subBV_at   j v y v_y p
                                                         ? lem_commute_psubFV_psubBV_at j v y v_y ps

{-@ lem_commute_psubFV_unbind_tvP :: x:Vname -> { v:Value | isLC v } -> { a:Vname | x != a } -> ps:Preds
        -> { pf:_ | psubFV x v (unbind_tvP a ps) = unbind_tvP a (psubFV x v ps) } / [predsize ps] @-}
lem_commute_psubFV_unbind_tvP :: Vname -> Expr -> Vname -> Preds -> Proof
lem_commute_psubFV_unbind_tvP x v a PEmpty       = ()
lem_commute_psubFV_unbind_tvP x v a (PCons p ps) = () ? lem_commute_subFV_unbind_tv   x v a p
                                                      ? lem_commute_psubFV_unbind_tvP x v a ps

{-@ lem_commute_psubFV_open_tvP_at :: x:Vname -> { v:Value | isLC v } 
        -> j:Index -> { a:Vname | x != a } -> ps:Preds
        -> { pf:_ | psubFV x v (open_tvP_at j a ps) = open_tvP_at j a (psubFV x v ps) } / [predsize ps] @-}
lem_commute_psubFV_open_tvP_at :: Vname -> Expr -> Index -> Vname -> Preds -> Proof
lem_commute_psubFV_open_tvP_at x v j a PEmpty       = ()
lem_commute_psubFV_open_tvP_at x v j a (PCons p ps) = () ? lem_commute_subFV_open_tv_at   x v j a p
                                                         ? lem_commute_psubFV_open_tvP_at x v j a ps

{-@ lem_commute_psubFV_psubBTV_at :: j:Index -> t:UserType -> y:Vname -> { v_y:Value | isLC v_y } 
      -> ps:Preds
      -> { pf:_ | psubFV y v_y (psubBTV_at j t ps) == psubBTV_at j (tsubFV y v_y t) (psubFV y v_y ps) } 
       / [predsize ps] @-}
lem_commute_psubFV_psubBTV_at :: Index -> Type -> Vname -> Expr -> Preds -> Proof
lem_commute_psubFV_psubBTV_at j t y v_y PEmpty       = ()
lem_commute_psubFV_psubBTV_at j t y v_y (PCons p ps) = () ? lem_commute_subFV_subBTV_at   j t y v_y p
                                                          ? lem_commute_psubFV_psubBTV_at j t y v_y ps

{-@ lem_commute_psubFTV_unbindP :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> { y:Vname | a != y } -> ps:Preds
        -> { pf:_ | psubFTV a t_a (unbindP y ps) = unbindP y (psubFTV a t_a ps) } / [predsize ps] @-}
lem_commute_psubFTV_unbindP :: Vname -> Type -> Vname -> Preds -> Proof
lem_commute_psubFTV_unbindP a t_a y PEmpty       = ()
lem_commute_psubFTV_unbindP a t_a y (PCons p ps) = () ? lem_commute_subFTV_unbind   a t_a y p
                                                      ? lem_commute_psubFTV_unbindP a t_a y ps

{-@ lem_commute_psubFTV_openP_at :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> j:Index -> { y:Vname | a != y } -> ps:Preds
        -> { pf:_ | psubFTV a t_a (openP_at j y ps) = openP_at j y (psubFTV a t_a ps) } / [predsize ps] @-}
lem_commute_psubFTV_openP_at :: Vname -> Type -> Index -> Vname -> Preds -> Proof
lem_commute_psubFTV_openP_at a t_a j y PEmpty       = ()
lem_commute_psubFTV_openP_at a t_a j y (PCons p ps) = () ? lem_commute_subFTV_open_at   a t_a j y p
                                                         ? lem_commute_psubFTV_openP_at a t_a j y ps

{-@ lem_commute_psubFTV_psubBV_at :: j:Index -> v:Value -> y:Vname -> { t_y:UserType | isLCT t_y } 
      -> ps:Preds
      -> { pf:_ | psubFTV y t_y (psubBV_at j v ps) == psubBV_at j (subFTV y t_y v) (psubFTV y t_y ps) } 
       / [predsize ps] @-}
lem_commute_psubFTV_psubBV_at :: Index -> Expr -> Vname -> Type -> Preds -> Proof
lem_commute_psubFTV_psubBV_at j v y t_y PEmpty       = ()
lem_commute_psubFTV_psubBV_at j v y t_y (PCons p ps) = () ? lem_commute_subFTV_subBV_at   j v y t_y p
                                                          ? lem_commute_psubFTV_psubBV_at j v y t_y ps

{-@ lem_commute_psubFTV_unbind_tvP :: a:Vname -> { t_a:UserType | isLCT t_a } 
      -> { a':Vname | a' != a } -> ps:Preds
      -> { pf:_ | psubFTV a t_a (unbind_tvP a' ps) = unbind_tvP a' (psubFTV a t_a ps) } / [predsize ps] @-}
lem_commute_psubFTV_unbind_tvP :: Vname -> Type -> Vname -> Preds -> Proof
lem_commute_psubFTV_unbind_tvP a t_a a' PEmpty       = ()
lem_commute_psubFTV_unbind_tvP a t_a a' (PCons p ps) = () ? lem_commute_subFTV_unbind_tv   a t_a a' p
                                                          ? lem_commute_psubFTV_unbind_tvP a t_a a' ps

{-@ lem_commute_psubFTV_open_tvP_at :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> j:Index -> { a':Vname | a' != a } -> ps:Preds
        -> { pf:_ | psubFTV a t_a (open_tvP_at j a' ps) = open_tvP_at j a' (psubFTV a t_a ps) } / [predsize ps] @-}
lem_commute_psubFTV_open_tvP_at :: Vname -> Type -> Index -> Vname -> Preds -> Proof
lem_commute_psubFTV_open_tvP_at a t_a j a' PEmpty       = ()
lem_commute_psubFTV_open_tvP_at a t_a j a' (PCons p ps) = () ? lem_commute_subFTV_open_tv_at   a t_a j a' p
                                                             ? lem_commute_psubFTV_open_tvP_at a t_a j a' ps

{-@ lem_commute_psubFTV_psubBTV_at :: j:Index -> t:UserType -> y:Vname -> { t_y:UserType | isLCT t_y } 
      -> ps:Preds
      -> {pf:_ | psubFTV y t_y (psubBTV_at j t ps) == psubBTV_at j (tsubFTV y t_y t) (psubFTV y t_y ps)} 
       / [predsize ps] @-}
lem_commute_psubFTV_psubBTV_at :: Index -> Type -> Vname -> Type -> Preds -> Proof
lem_commute_psubFTV_psubBTV_at j t y t_y PEmpty       = ()
lem_commute_psubFTV_psubBTV_at j t y t_y (PCons p ps) = () ? lem_commute_subFTV_subBTV_at   j t y t_y p
                                                           ? lem_commute_psubFTV_psubBTV_at j t y t_y ps


------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TERM VARIABLES in TYPES
------------------------------------------------------------------------------

{-@ lem_tsubFV_notin :: x:Vname -> v:Value -> { t:Type | not (Set_mem x (free t)) } 
                               -> { pf:_ | tsubFV x v t == t } / [tsize t] @-}
lem_tsubFV_notin :: Vname -> Expr -> Type -> Proof
lem_tsubFV_notin x v t@(TRefn b   ps)     = () ? lem_psubFV_notin x v ps
lem_tsubFV_notin x v t@(TFunc   t_w t')   = () ? lem_tsubFV_notin x v t_w
                                               ? lem_tsubFV_notin x v t'
lem_tsubFV_notin x v t@(TExists   t_w t') = () ? lem_tsubFV_notin x v t_w
                                               ? lem_tsubFV_notin x v t'
lem_tsubFV_notin x v t@(TPoly   k t')     = () ? lem_tsubFV_notin x v t'

{-@ lem_openT_at_lct_at :: j:Index -> x:Vname -> { kx:Index | j >= kx } -> ka:Index 
        -> { t:Type | isLCT_at kx ka t } -> { pf:_ | openT_at j x t = t } / [tsize t] @-}
lem_openT_at_lct_at :: Index -> Vname -> Index -> Index -> Type -> Proof
lem_openT_at_lct_at j x kx ka (TRefn b ps)
                = () ? lem_openP_at_lcp_at (j+1) x (kx+1) ka     ps
lem_openT_at_lct_at j x kx ka (TFunc t_z t)
                = () ? lem_openT_at_lct_at j     x kx     ka     t_z
                     ? lem_openT_at_lct_at (j+1) x (kx+1) ka     t
lem_openT_at_lct_at j x kx ka (TExists t_z t)
                = () ? lem_openT_at_lct_at j     x kx     ka     t_z
                     ? lem_openT_at_lct_at (j+1) x (kx+1) ka     t
lem_openT_at_lct_at j x kx ka (TPoly k t)
                = () ? lem_openT_at_lct_at j     x kx     (ka+1) t

{-@ lem_tsubBV_at_lct_at :: j:Index -> v:Value -> { kx:Index | j >= kx } -> ka:Index 
        -> { t:Type | isLCT_at kx ka t } -> { pf:_ | tsubBV_at j v t = t } / [tsize t] @-}
lem_tsubBV_at_lct_at :: Index -> Expr -> Index -> Index -> Type -> Proof
lem_tsubBV_at_lct_at j v kx ka (TRefn b ps)
                = () ? lem_psubBV_at_lcp_at (j+1) v (kx+1) ka     ps
lem_tsubBV_at_lct_at j v kx ka (TFunc t_z t)
                = () ? lem_tsubBV_at_lct_at j     v kx     ka     t_z
                     ? lem_tsubBV_at_lct_at (j+1) v (kx+1) ka     t
lem_tsubBV_at_lct_at j v kx ka (TExists t_z t)
                = () ? lem_tsubBV_at_lct_at j     v kx     ka     t_z
                     ? lem_tsubBV_at_lct_at (j+1) v (kx+1) ka     t
lem_tsubBV_at_lct_at j v kx ka (TPoly k t)
                = () ? lem_tsubBV_at_lct_at j     v kx     (ka+1) t

{-@ lem_open_tvT_at_lct_at :: j:Index -> a:Vname -> kx:Index -> { ka:Index | j >= ka } 
        -> { t:Type | isLCT_at kx ka t } -> { pf:_ | open_tvT_at j a t = t } / [tsize t] @-}
lem_open_tvT_at_lct_at :: Index -> Vname -> Index -> Index -> Type -> Proof
lem_open_tvT_at_lct_at j a kx ka (TRefn b ps)
                = () ? lem_open_tvP_at_lcp_at j     a (kx+1) ka     ps
lem_open_tvT_at_lct_at j a kx ka (TFunc t_z t)
                = () ? lem_open_tvT_at_lct_at j     a kx     ka     t_z
                     ? lem_open_tvT_at_lct_at j     a (kx+1) ka     t
lem_open_tvT_at_lct_at j a kx ka (TExists t_z t)
                = () ? lem_open_tvT_at_lct_at j     a kx     ka     t_z
                     ? lem_open_tvT_at_lct_at j     a (kx+1) ka     t
lem_open_tvT_at_lct_at j a kx ka (TPoly k t)
                = () ? lem_open_tvT_at_lct_at (j+1) a kx     (ka+1) t

{-@ lem_tsubBTV_at_lct_at :: j:Index -> t_a:UserType -> kx:Index -> { ka:Index | j >= ka } 
        -> { t:Type | isLCT_at kx ka t } -> { pf:_ | tsubBTV_at j t_a t = t } / [tsize t] @-}
lem_tsubBTV_at_lct_at :: Index -> Type -> Index -> Index -> Type -> Proof
lem_tsubBTV_at_lct_at j t_a kx ka (TRefn b ps)
                = () ? lem_psubBTV_at_lcp_at j     t_a (kx+1) ka     ps
lem_tsubBTV_at_lct_at j t_a kx ka (TFunc t_z t)
                = () ? lem_tsubBTV_at_lct_at j     t_a kx     ka     t_z
                     ? lem_tsubBTV_at_lct_at j     t_a (kx+1) ka     t
lem_tsubBTV_at_lct_at j t_a kx ka (TExists t_z t)
                = () ? lem_tsubBTV_at_lct_at j     t_a kx     ka     t_z
                     ? lem_tsubBTV_at_lct_at j     t_a (kx+1) ka     t
lem_tsubBTV_at_lct_at j t_a kx ka (TPoly k t)
                = () ? lem_tsubBTV_at_lct_at (j+1) t_a kx     (ka+1) t

{-@ lem_tsubBV_is_unbindT :: y:Vname -> t:Type -> { pf:_ | tsubBV (FV y) t == unbindT y t } @-}
lem_tsubBV_is_unbindT :: Vname -> Type -> Proof
lem_tsubBV_is_unbindT y t = lem_tsubBV_at_is_openT_at 0 y t

{-@ lem_tsubBV_at_is_openT_at :: j:Index -> y:Vname -> t:Type
        -> { pf:_ | tsubBV_at j (FV y) t == openT_at j y t } / [tsize t] @-}
lem_tsubBV_at_is_openT_at :: Index -> Vname -> Type -> Proof
lem_tsubBV_at_is_openT_at j y (TRefn   b  ps) = lem_psubBV_at_is_openP_at (j+1) y ps 
lem_tsubBV_at_is_openT_at j y (TFunc   t_x t) = lem_tsubBV_at_is_openT_at j     y t_x
                                              ? lem_tsubBV_at_is_openT_at (j+1) y t
lem_tsubBV_at_is_openT_at j y (TExists t_x t) = lem_tsubBV_at_is_openT_at j     y t_x
                                              ? lem_tsubBV_at_is_openT_at (j+1) y t
lem_tsubBV_at_is_openT_at j y (TPoly   k   t) = lem_tsubBV_at_is_openT_at j     y t

{-@ lem_tsubFV_unbindT :: y:Vname -> v:Value -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | tsubBV v t == tsubFV y v (unbindT y t) } / [tsize t] @-}
lem_tsubFV_unbindT :: Vname -> Expr -> Type -> Proof
lem_tsubFV_unbindT y v t = lem_tsubFV_openT_at 0 y v t

{-@ lem_tsubFV_openT_at :: j:Index -> y:Vname -> v:Value 
        -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | tsubBV_at j v t == tsubFV y v (openT_at j y t) } / [tsize t] @-}
lem_tsubFV_openT_at :: Index -> Vname -> Expr -> Type -> Proof
lem_tsubFV_openT_at j y v (TRefn b ps)      = () ? lem_psubFV_openP_at (j+1) y v ps
lem_tsubFV_openT_at j y v (TFunc   t_w t')  = () ? lem_tsubFV_openT_at j     y v t_w
                                                 ? lem_tsubFV_openT_at (j+1) y v t'
lem_tsubFV_openT_at j y v (TExists t_w t')  = () ? lem_tsubFV_openT_at j     y v t_w
                                                 ? lem_tsubFV_openT_at (j+1) y v t' 
lem_tsubFV_openT_at j y v (TPoly  k t')     = () ? lem_tsubFV_openT_at j     y v t'

{-@ lem_commute_tsubFV_unbindT :: x:Vname -> { v:Value | isLC v } -> { y:Vname | x != y } -> t:Type
        -> {pf:_ | tsubFV x v (unbindT y t) == unbindT y (tsubFV x v t)} / [tsize t] @-}
lem_commute_tsubFV_unbindT :: Vname -> Expr -> Vname -> Type -> Proof
lem_commute_tsubFV_unbindT x v y t = lem_commute_tsubFV_openT_at x v 0 y t

{-@ lem_commute_tsubFV_openT_at :: x:Vname -> { v:Value | isLC v } 
        -> j:Index -> { y:Vname | x != y } -> t:Type
        -> {pf:_ | tsubFV x v (openT_at j y t) == openT_at j y (tsubFV x v t)} / [tsize t] @-}
lem_commute_tsubFV_openT_at :: Vname -> Expr -> Index -> Vname -> Type -> Proof
lem_commute_tsubFV_openT_at x v j y (TRefn b ps)
              = () ? lem_commute_psubFV_openP_at x v (j+1) y ps
lem_commute_tsubFV_openT_at x v j y (TFunc t_w t)
              = () ? lem_commute_tsubFV_openT_at x v j     y t_w
                   ? lem_commute_tsubFV_openT_at x v (j+1) y t
lem_commute_tsubFV_openT_at x v j y (TExists t_w t)
              = () ? lem_commute_tsubFV_openT_at x v j     y t_w
                   ? lem_commute_tsubFV_openT_at x v (j+1) y t
lem_commute_tsubFV_openT_at x v j y (TPoly k t)
              = () ? lem_commute_tsubFV_openT_at x v j     y t

{-@ lem_commute_tsubFV_tsubBV :: v:Value 
        -> y:Vname -> { v_y:Value | isLC v_y } -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV v t) == tsubBV (subFV y v_y v) (tsubFV y v_y t) } 
         / [tsize t] @-}
lem_commute_tsubFV_tsubBV :: Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV v y v_y t = lem_commute_tsubFV_tsubBV_at 0 v y v_y t

{-@ lem_commute_tsubFV_tsubBV_at :: j:Index -> v:Value 
        -> y:Vname -> { v_y:Value | isLC v_y } -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV_at j v t) == tsubBV_at j (subFV y v_y v) (tsubFV y v_y t) } 
         / [tsize t] @-}
lem_commute_tsubFV_tsubBV_at :: Index -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV_at j v y v_y (TRefn b ps)
  | otherwise = () ? lem_commute_psubFV_psubBV_at (j+1) v y v_y ps
lem_commute_tsubFV_tsubBV_at j v y v_y (TFunc t_w t)
              = () ? lem_commute_tsubFV_tsubBV_at j v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV_at (j+1) v y v_y t
lem_commute_tsubFV_tsubBV_at j v y v_y (TExists t_w t)
              = () ? lem_commute_tsubFV_tsubBV_at j v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV_at (j+1) v y v_y t
lem_commute_tsubFV_tsubBV_at j v y v_y (TPoly k t) 
              = () ? lem_commute_tsubFV_tsubBV_at j v y v_y t

{-@ lem_commute_tsubFV_unbind_tvT :: x:Vname -> { v:Value | isLC v } -> { a:Vname | x != a } -> t:Type
        -> {pf:_ | tsubFV x v (unbind_tvT a t) == unbind_tvT a (tsubFV x v t)} / [tsize t] @-}
lem_commute_tsubFV_unbind_tvT :: Vname -> Expr -> Vname -> Type -> Proof
lem_commute_tsubFV_unbind_tvT x v a t = lem_commute_tsubFV_open_tvT_at x v 0 a t

{-@ lem_commute_tsubFV_open_tvT_at :: x:Vname -> { v:Value | isLC v } 
        -> j:Index -> { a:Vname | x != a } -> t:Type
        -> {pf:_ | tsubFV x v (open_tvT_at j a t) == open_tvT_at j a (tsubFV x v t)} / [tsize t] @-}
lem_commute_tsubFV_open_tvT_at :: Vname -> Expr -> Index -> Vname -> Type -> Proof
lem_commute_tsubFV_open_tvT_at x v j a (TRefn b ps) = case b of 
  (BTV i) | i == j    -> () ? lem_commute_psubFV_open_tvP_at x v j a ps
          | otherwise -> () ? lem_commute_psubFV_open_tvP_at x v j a ps
  _                   -> () ? lem_commute_psubFV_open_tvP_at x v j a ps
lem_commute_tsubFV_open_tvT_at x v j a (TFunc t_w t)
              = () ? lem_commute_tsubFV_open_tvT_at x v j     a t_w
                   ? lem_commute_tsubFV_open_tvT_at x v j     a t
lem_commute_tsubFV_open_tvT_at x v j a (TExists t_w t)
              = () ? lem_commute_tsubFV_open_tvT_at x v j     a t_w
                   ? lem_commute_tsubFV_open_tvT_at x v j     a t
lem_commute_tsubFV_open_tvT_at x v j a (TPoly k t)
              = () ? lem_commute_tsubFV_open_tvT_at x v (j+1) a t

{-@ lem_commute_tsubFV_tsubBTV :: t_a:UserType
        -> y:Vname -> { v_y:Value | isLC v_y }  -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBTV t_a t) == tsubBTV (tsubFV y v_y t_a) (tsubFV y v_y t) } @-}
lem_commute_tsubFV_tsubBTV :: Type -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBTV t_a y v_y t = lem_commute_tsubFV_tsubBTV_at 0 t_a y v_y t

{-@ lem_commute_tsubFV_tsubBTV_at :: j:Index -> t_a:UserType
      -> y:Vname -> { v_y:Value | isLC v_y }  -> t:Type
      -> { pf:_ | tsubFV y v_y (tsubBTV_at j t_a t) == tsubBTV_at j (tsubFV y v_y t_a) (tsubFV y v_y t)}
       / [ tsize t ] @-}
lem_commute_tsubFV_tsubBTV_at :: Index -> Type -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBTV_at j t_a y v_y (TRefn b ps) = case b of
  (BTV j') | j == j' -> () ? lem_commute_psubFV_psubBTV_at j t_a y v_y ps
                           ? lem_subFV_push           y v_y (psubBTV_at j t_a ps) t_a
  _                  -> () ? lem_commute_psubFV_psubBTV_at j t_a y v_y ps
lem_commute_tsubFV_tsubBTV_at j t_a y v_y (TFunc t_w t)
              = () ? lem_commute_tsubFV_tsubBTV_at j t_a y v_y t_w
                   ? lem_commute_tsubFV_tsubBTV_at j t_a y v_y t
lem_commute_tsubFV_tsubBTV_at j t_a y v_y (TExists  t_w t)
              = () ? lem_commute_tsubFV_tsubBTV_at j t_a y v_y t_w
                   ? lem_commute_tsubFV_tsubBTV_at j t_a y v_y t
lem_commute_tsubFV_tsubBTV_at j t_a y v_y (TPoly k t) 
              = () ? lem_commute_tsubFV_tsubBTV_at (j+1) t_a y v_y t

{-@ lem_commute_tsubFTV_unbindT :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> { y:Vname | a != y } -> t:Type
        -> {pf:_ | tsubFTV a t_a (unbindT y t) == unbindT y (tsubFTV a t_a t)} / [tsize t] @-}
lem_commute_tsubFTV_unbindT :: Vname -> Type -> Vname -> Type -> Proof
lem_commute_tsubFTV_unbindT a t_a y t = lem_commute_tsubFTV_openT_at a t_a 0 y t

{-@ lem_commute_tsubFTV_openT_at :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> j:Index -> { y:Vname | a != y } -> t:Type
        -> {pf:_ | tsubFTV a t_a (openT_at j y t) == openT_at j y (tsubFTV a t_a t)} / [tsize t] @-}
lem_commute_tsubFTV_openT_at :: Vname -> Type -> Index -> Vname -> Type -> Proof
lem_commute_tsubFTV_openT_at a t_a j y (TRefn b ps) = case b of
  (FTV a0) | a0 == a   -> () ? lem_commute_psubFTV_openP_at a t_a (j+1) y ps
                             ? lem_openT_at_push j y (psubFTV a t_a ps) t_a
                             ? lem_openT_at_lct_at j y 0 0 t_a
           | otherwise -> () ? lem_commute_psubFTV_openP_at a t_a (j+1) y ps
  _                    -> () ? lem_commute_psubFTV_openP_at a t_a (j+1) y ps
lem_commute_tsubFTV_openT_at a t_a j y (TFunc t_w t)
              = () ? lem_commute_tsubFTV_openT_at a t_a j     y t_w
                   ? lem_commute_tsubFTV_openT_at a t_a (j+1) y t
lem_commute_tsubFTV_openT_at a t_a j y (TExists t_w t)
              = () ? lem_commute_tsubFTV_openT_at a t_a j     y t_w
                   ? lem_commute_tsubFTV_openT_at a t_a (j+1) y t
lem_commute_tsubFTV_openT_at a t_a j y (TPoly k t)
              = () ? lem_commute_tsubFTV_openT_at a t_a j     y t

{-@ lem_commute_tsubFTV_tsubBV :: v:Value 
        -> a:Vname -> { t_a:UserType | isLCT t_a } -> t:Type
        -> { pf:_ | tsubFTV a t_a (tsubBV v t) == tsubBV (subFTV a t_a v) (tsubFTV a t_a t) } @-}
lem_commute_tsubFTV_tsubBV :: Expr -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBV v a t_a t = lem_commute_tsubFTV_tsubBV_at 0 v a t_a t

{-@ lem_commute_tsubFTV_tsubBV_at :: j:Index -> v:Value 
        -> a:Vname -> { t_a:UserType | isLCT t_a } -> t:Type
        -> { pf:_ | tsubFTV a t_a (tsubBV_at j v t) == tsubBV_at j (subFTV a t_a v) (tsubFTV a t_a t) } 
         / [tsize t] @-}
lem_commute_tsubFTV_tsubBV_at :: Index -> Expr -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBV_at j v a t_a (TRefn b ps) = case b of
  (FTV a') | a == a'   -> () ? lem_commute_psubFTV_psubBV_at (j+1) v a t_a ps
                             ? lem_subBV_at_push j (subFTV a t_a v) (psubFTV a t_a ps) t_a
                             ? lem_tsubBV_at_lct_at j (subFTV a t_a v) 0 0 t_a
  _                    -> () ? lem_commute_psubFTV_psubBV_at (j+1) v a t_a ps
lem_commute_tsubFTV_tsubBV_at j v a t_a (TFunc t_w t)
              = () ? lem_commute_tsubFTV_tsubBV_at j     v a t_a t_w
                   ? lem_commute_tsubFTV_tsubBV_at (j+1) v a t_a t
lem_commute_tsubFTV_tsubBV_at j v a t_a (TExists t_w t)
              = () ? lem_commute_tsubFTV_tsubBV_at j     v a t_a t_w
                   ? lem_commute_tsubFTV_tsubBV_at (j+1) v a t_a t
lem_commute_tsubFTV_tsubBV_at j v a t_a (TPoly k t) 
              = () ? lem_commute_tsubFTV_tsubBV_at j v a t_a t

{-@ lem_commute_tsubFTV_unbind_tvT :: a:Vname -> { t_a:UserType | isLCT t_a } 
        -> { a':Vname | a' != a } -> t:Type
        -> {pf:_ | tsubFTV a t_a (unbind_tvT a' t) == unbind_tvT a' (tsubFTV a t_a t)} / [tsize t] @-}
lem_commute_tsubFTV_unbind_tvT :: Vname -> Type -> Vname -> Type -> Proof
lem_commute_tsubFTV_unbind_tvT a t_a a' t = lem_commute_tsubFTV_open_tvT_at a t_a 0 a' t

{-@ lem_commute_tsubFTV_open_tvT_at :: a:Vname -> { t_a:UserType | isLCT t_a }
        -> j:Index -> { a':Vname | a' != a } -> t:Type
        -> {pf:_ | tsubFTV a t_a (open_tvT_at j a' t) == open_tvT_at j a' (tsubFTV a t_a t)} / [tsize t] @-}
lem_commute_tsubFTV_open_tvT_at :: Vname -> Type -> Index -> Vname -> Type -> Proof
lem_commute_tsubFTV_open_tvT_at a t_a j a' (TRefn b ps) = case b of 
  (FTV a0) | a0 == a   -> () ? lem_commute_psubFTV_open_tvP_at a t_a j a' ps
                             ? lem_open_tvT_at_push j a' (psubFTV a t_a ps) t_a
                             ? lem_open_tvT_at_lct_at j a' 0 0 t_a
           | otherwise -> () ? lem_commute_psubFTV_open_tvP_at a t_a j a' ps
  (BTV i)  | i == j    -> () ? lem_commute_psubFTV_open_tvP_at a t_a j a' ps
           | otherwise -> () ? lem_commute_psubFTV_open_tvP_at a t_a j a' ps
  _                    -> () ? lem_commute_psubFTV_open_tvP_at a t_a j a' ps
lem_commute_tsubFTV_open_tvT_at a t_a j a' (TFunc t_w t)
              = () ? lem_commute_tsubFTV_open_tvT_at a t_a j     a' t_w
                   ? lem_commute_tsubFTV_open_tvT_at a t_a j     a' t
lem_commute_tsubFTV_open_tvT_at a t_a j a' (TExists t_w t)
              = () ? lem_commute_tsubFTV_open_tvT_at a t_a j     a' t_w
                   ? lem_commute_tsubFTV_open_tvT_at a t_a j     a' t
lem_commute_tsubFTV_open_tvT_at a t_a j a' (TPoly k t)
              = () ? lem_commute_tsubFTV_open_tvT_at a t_a (j+1) a' t

{-@ lem_commute_tsubFTV_tsubBTV :: t1:UserType
        -> a:Vname -> { t_a:UserType | isLCT t_a } -> t:Type
        -> { pf:_ | tsubFTV a  t_a                (tsubBTV t1 t) 
                 == tsubBTV (tsubFTV a t_a t1) (tsubFTV a t_a t) } / [tsize t] @-}
lem_commute_tsubFTV_tsubBTV :: Type -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBTV t1 a t_a t = lem_commute_tsubFTV_tsubBTV_at 0 t1 a t_a t

{-@ lem_commute_tsubFTV_tsubBTV_at :: j:Index -> t1:UserType
        -> a:Vname -> { t_a:UserType | isLCT t_a } -> t:Type
        -> { pf:_ | tsubFTV a  t_a                (tsubBTV_at j t1 t) 
                 == tsubBTV_at j (tsubFTV a t_a t1) (tsubFTV a t_a t) } / [tsize t] @-}
lem_commute_tsubFTV_tsubBTV_at :: Index -> Type -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBTV_at j t1 a t_a (TRefn b ps) = case b of
  (FTV a') | a == a'    -> () ? lem_commute_psubFTV_psubBTV_at j t1 a t_a ps
                              ? lem_subBTV_at_push j (tsubFTV a t_a t1) (psubFTV a t_a ps) t_a
                              ? lem_tsubBTV_at_lct_at j (tsubFTV a t_a t1) 0 0 t_a
  (BTV j') | j == j'    -> () ? lem_commute_psubFTV_psubBTV_at j t1 a t_a ps
                              ? lem_subFTV_push a t_a (psubBTV_at j t1 ps) t1
  _                     -> () ? lem_commute_psubFTV_psubBTV_at j t1 a t_a ps
lem_commute_tsubFTV_tsubBTV_at j t1 a t_a (TFunc t_w t)
              = () ? lem_commute_tsubFTV_tsubBTV_at j t1 a t_a t_w
                   ? lem_commute_tsubFTV_tsubBTV_at j t1 a t_a t
lem_commute_tsubFTV_tsubBTV_at j t1 a t_a (TExists t_w t)
              = () ? lem_commute_tsubFTV_tsubBTV_at j t1 a t_a t_w
                   ? lem_commute_tsubFTV_tsubBTV_at j t1 a t_a t
lem_commute_tsubFTV_tsubBTV_at j t1 a t_a (TPoly k t) 
              = () ? lem_commute_tsubFTV_tsubBTV_at (j+1) t1 a t_a t

------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in TYPES
------------------------------------------------------------------------------

{-@ lem_tsubFTV_notin :: a:Vname -> t_a:UserType -> { t:Type | not (Set_mem a (freeTV t)) } 
                               -> { pf:_ | tsubFTV a t_a t == t } / [tsize t] @-}
lem_tsubFTV_notin :: Vname -> Type -> Type -> Proof
lem_tsubFTV_notin a t_a t@(TRefn b ps)     = () ? lem_psubFTV_notin a t_a ps
lem_tsubFTV_notin a t_a t@(TFunc t_w t')   = () ? lem_tsubFTV_notin a t_a t_w
                                                ? lem_tsubFTV_notin a t_a t'
lem_tsubFTV_notin a t_a t@(TExists t_w t') = () ? lem_tsubFTV_notin a t_a t_w
                                                ? lem_tsubFTV_notin a t_a t'
lem_tsubFTV_notin a t_a t@(TPoly  k t')    = () ? lem_tsubFTV_notin a t_a t'

{-@ lem_tsubFTV_ftv :: a:Vname -> t_a:UserType
        -> { pf:_ | tsubFTV a t_a (TRefn (FTV a) PEmpty) == t_a } @-}
lem_tsubFTV_ftv :: Vname -> Type -> Proof
lem_tsubFTV_ftv a t_a = lem_push_empty t_a

{-@ lem_tsubFTV_trefn :: a:Vname -> { t_a:UserType | isTRefn t_a } -> { t:Type | isTRefn t }
        -> { pf:_ | isTRefn (tsubFTV a t_a t) } @-}
lem_tsubFTV_trefn :: Vname -> Type -> Type -> Proof
lem_tsubFTV_trefn a (TRefn b' q') (TRefn b p) = case b of
  (FTV a') | a' == a  -> toProof (
        tsubFTV a (TRefn b'  q') (TRefn b  p)
    === push (psubFTV a (TRefn b'  q') p) (TRefn b'  q')
    === TRefn b'  (strengthen (psubFTV a (TRefn b'  q') p) q') )
  _                   -> ()

{-@ lem_tsubFTV_unbind_tvT :: a:Vname -> t_a:UserType 
        -> { t:Type | not (Set_mem a (freeTV t)) }
        -> { pf:_ | tsubBTV t_a t == tsubFTV a t_a (unbind_tvT a t) } / [tsize t] @-}
lem_tsubFTV_unbind_tvT :: Vname -> Type -> Type -> Proof
lem_tsubFTV_unbind_tvT a t_a t = lem_tsubFTV_open_tvT_at 0 a t_a t

{-@ lem_tsubFTV_open_tvT_at :: j:Index -> a:Vname -> t_a:UserType 
        -> { t:Type | not (Set_mem a (freeTV t)) }
        -> { pf:_ | tsubBTV_at j t_a t == tsubFTV a t_a (open_tvT_at j a t) } / [tsize t] @-}
lem_tsubFTV_open_tvT_at :: Index -> Vname -> Type -> Type -> Proof
lem_tsubFTV_open_tvT_at j a t_a (TRefn b ps)     = case b of 
  (FTV a1) | a1 == a   -> () ? lem_psubFTV_open_tvP_at   j a  t_a ps
  (BTV i)  | i == j    -> () ? lem_psubFTV_open_tvP_at   j a  t_a ps
  _                    -> () ? lem_psubFTV_open_tvP_at   j a  t_a ps
lem_tsubFTV_open_tvT_at j a t_a (TFunc t_w t')   = () ? lem_tsubFTV_open_tvT_at j a t_a t_w 
                                                      ? lem_tsubFTV_open_tvT_at j a t_a t' 
lem_tsubFTV_open_tvT_at j a t_a (TExists t_w t') = () ? lem_tsubFTV_open_tvT_at j a t_a t_w
                                                      ? lem_tsubFTV_open_tvT_at j a t_a t'
lem_tsubFTV_open_tvT_at j a t_a (TPoly k t')     = () ? lem_tsubFTV_open_tvT_at (j+1) a t_a t'

---------------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION and the PUSH function
---------------------------------------------------------------------------------------

{-@ lem_push_empty :: t_a:UserType -> { pf:_ | push PEmpty t_a == t_a } @-}
lem_push_empty ::  Type -> Proof
lem_push_empty (TRefn b rs)   = toProof ( strengthen PEmpty rs )
lem_push_empty (TFunc  t_z t) = () 
lem_push_empty (TPoly   k' t) = () 

{-@ lem_openT_at_push :: j:Index -> y:Vname -> ps:Preds -> t_a:UserType 
        -> { pf:_ | openT_at j y (push ps t_a) == push (openP_at (j+1) y ps) (openT_at j y t_a) } @-}
lem_openT_at_push :: Index -> Vname -> Preds -> Type -> Proof
lem_openT_at_push j y ps (TRefn   b ps') = () ? lem_openP_at_strengthen (j+1) y ps ps'
lem_openT_at_push j y ps (TFunc   t_x t) = () 
lem_openT_at_push j y ps (TPoly   k t)   = () 

{-@ lem_open_tvT_at_push :: j:Index -> a':Vname -> ps:Preds -> t_a:UserType 
        -> { pf:_ | open_tvT_at j a' (push ps t_a) == push (open_tvP_at j a' ps) (open_tvT_at j a' t_a) } @-}
lem_open_tvT_at_push :: Index -> Vname -> Preds -> Type -> Proof
lem_open_tvT_at_push j a' ps (TRefn   b ps') = case b of 
  (BTV i) | i == j   -> () ? lem_open_tvP_at_strengthen j a' ps ps'
  _                  -> () ? lem_open_tvP_at_strengthen j a' ps ps'
lem_open_tvT_at_push j a' ps (TFunc   t_x t) = () 
lem_open_tvT_at_push j a' ps (TPoly   k t)   = () 

{-@ lem_push_strengthen :: ps:Preds -> rs:Preds -> t:Type
        -> { pf:_ | push (strengthen ps rs) t == push ps (push rs t) } @-}
lem_push_strengthen :: Preds -> Preds -> Type -> Proof
lem_push_strengthen ps rs (TRefn b qs)    = () ? lem_strengthen_assoc ps rs qs
lem_push_strengthen ps rs (TFunc t_z t)   = () {-? lem_push_strengthen  ps rs t_z
                                               ? lem_push_strengthen  ps rs t-}
lem_push_strengthen ps rs (TExists t_z t) = () ? lem_push_strengthen  ps rs t_z
                                               ? lem_push_strengthen  ps rs t
lem_push_strengthen ps rs (TPoly k t)     = () -- ? lem_push_strengthen  ps rs t

{-@ lem_subFV_push :: x:Vname -> v:Value -> ps:Preds -> t:UserType
        -> { pf:_ | tsubFV x v (push ps t) == push (psubFV x v ps) (tsubFV x v t) } @-}
lem_subFV_push :: Vname -> Expr -> Preds -> Type -> Proof
lem_subFV_push x v ps (TRefn   b  rs) = () ? lem_psubFV_strengthen x v ps rs
lem_subFV_push x v ps (TFunc   t_y t) = () -- ? lem_subFV_push x v ps t_y 
                                           -- ? lem_subFV_push x v ps t
lem_subFV_push x v ps (TPoly   k   t) = () -- ? lem_subFV_push x v ps t

{-@ lem_subBV_at_push :: j:Index -> v:Value -> ps:Preds -> t:UserType
        -> { pf:_ | tsubBV_at j v (push ps t) == push (psubBV_at (j+1) v ps) (tsubBV_at j v t) } @-}
lem_subBV_at_push :: Index -> Expr -> Preds -> Type -> Proof
lem_subBV_at_push j v ps (TRefn   b  rs) = () ? lem_psubBV_at_strengthen (j+1) v ps rs
lem_subBV_at_push j v ps (TFunc   t_y t) = () -- ? lem_subBV_at_push j v ps t_y 
                                              -- ? lem_subBV_at_push (j+1) v ps t
lem_subBV_at_push j v ps (TPoly   k   t) = () -- ? lem_subBV_at_push j v ps t

{-@ lem_subFTV_push :: a:Vname -> t_a:UserType -> ps:Preds -> t:UserType
        -> { pf:_ | tsubFTV a t_a (push ps t) == push (psubFTV a t_a ps) (tsubFTV a t_a t) } @-}
lem_subFTV_push :: Vname -> Type -> Preds -> Type -> Proof
lem_subFTV_push a t_a ps (TRefn   b  rs) = case b of 
  (FTV a') | a == a'  -> () ? lem_psubFTV_strengthen a t_a ps rs
                            ? lem_push_strengthen (psubFTV a t_a ps) (psubFTV a t_a rs) t_a
  _                   -> () ? lem_psubFTV_strengthen a t_a ps rs
lem_subFTV_push a t_a ps (TFunc   t_y t) = () 
lem_subFTV_push a t_a ps (TPoly    k  t) = () 

{-@ lem_subBTV_at_push :: j:Index -> t_a:UserType -> ps:Preds -> t:UserType 
      -> {pf:_ | tsubBTV_at j t_a (push ps t) == push (psubBTV_at j t_a ps) (tsubBTV_at j t_a t)} @-}
lem_subBTV_at_push :: Index -> Type -> Preds -> Type -> Proof
lem_subBTV_at_push j t_a ps (TRefn   b  rs) = case b of 
  (BTV j') | j == j'  -> () ? lem_psubBTV_at_strengthen j t_a ps rs
                            ? lem_push_strengthen (psubBTV_at j t_a ps) (psubBTV_at j t_a rs) t_a
  _                   -> () ? lem_psubBTV_at_strengthen j t_a ps rs    
lem_subBTV_at_push j t_a ps (TFunc   t_y t) = () 
lem_subBTV_at_push j t_a ps (TPoly    k  t) = () 

---------------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in SYSTEM F TYPES
---------------------------------------------------------------------------------------

{-@ lem_ftsubFV_notin :: a:Vname -> t_a:FType -> { t:FType | not (Set_mem a (ffreeTV t)) } 
                               -> { pf:_ | ftsubFV a t_a t == t } / [ftsize t] @-}
lem_ftsubFV_notin :: Vname -> FType -> FType -> Proof
lem_ftsubFV_notin a t_a (FTBasic b)     = () 
lem_ftsubFV_notin a t_a (FTFunc t_w t') = () ? lem_ftsubFV_notin a t_a t_w
                                             ? lem_ftsubFV_notin a t_a t'
lem_ftsubFV_notin a t_a (FTPoly  k t')  = () ? lem_ftsubFV_notin a t_a t'

{-@ lem_islcft_at_openFT_at :: j:Index -> a:Vname -> { k:Index | j >= k }
         -> { t:FType | isLCFT_at k t } -> { pf:_ | openFT_at j a t == t } / [ftsize t] @-}
lem_islcft_at_openFT_at :: Index -> Vname -> Index -> FType -> Proof
lem_islcft_at_openFT_at j a k (FTBasic b)     = () 
lem_islcft_at_openFT_at j a k (FTFunc t_w t') = () ? lem_islcft_at_openFT_at j     a k t_w
                                                   ? lem_islcft_at_openFT_at j     a k t'
lem_islcft_at_openFT_at j a k (FTPoly  k' t') = () ? lem_islcft_at_openFT_at (j+1) a (k+1) t'

{-@ lem_islcft_at_ftsubBV_at :: j:Index -> t_j:FType -> { k:Index | j >= k }
         -> { t:FType | isLCFT_at k t } -> { pf:_ | ftsubBV_at j t_j t == t } / [ftsize t] @-}
lem_islcft_at_ftsubBV_at :: Index -> FType -> Index -> FType -> Proof
lem_islcft_at_ftsubBV_at j t_j k (FTBasic b)     = () 
lem_islcft_at_ftsubBV_at j t_j k (FTFunc t_w t') = () ? lem_islcft_at_ftsubBV_at j     t_j k t_w
                                                      ? lem_islcft_at_ftsubBV_at j     t_j k t'
lem_islcft_at_ftsubBV_at j t_j k (FTPoly  k' t') = () ? lem_islcft_at_ftsubBV_at (j+1) t_j (k+1) t'

{-@ lem_ftsubFV_unbindFT :: a':Vname -> t_a:FType 
        -> { t:FType | not (Set_mem a' (ffreeTV t)) }
        -> { pf:_ | ftsubBV t_a t == ftsubFV a' t_a (unbindFT a' t) } / [ftsize t] @-}
lem_ftsubFV_unbindFT ::  Vname -> FType -> FType -> Proof
lem_ftsubFV_unbindFT a' t_a t = lem_ftsubFV_openFT_at 0 a' t_a t

{-@ lem_ftsubFV_openFT_at :: j:Index -> a':Vname -> t_a:FType 
        -> { t:FType | not (Set_mem a' (ffreeTV t)) }
        -> { pf:_ | ftsubBV_at j t_a t == ftsubFV a' t_a (openFT_at j a' t) } / [ftsize t] @-}
lem_ftsubFV_openFT_at :: Index -> Vname -> FType -> FType -> Proof
lem_ftsubFV_openFT_at j a' t_a (FTBasic b)      = ()
lem_ftsubFV_openFT_at j a' t_a (FTFunc t_w t')  = () ? lem_ftsubFV_openFT_at j a' t_a t_w 
                                                     ? lem_ftsubFV_openFT_at j a' t_a t' 
lem_ftsubFV_openFT_at j a' t_a (FTPoly k t')    = () ? lem_ftsubFV_openFT_at (j+1) a' t_a t'

{-@ lem_commute_ftsubFV_unbindFT :: a0:Vname -> { t_a0:FType  | isLCFT t_a0 }
      -> { a:Vname | a != a0 } -> t:FType
      -> { pf:_ | ftsubFV a0 t_a0 (unbindFT a t) == unbindFT a (ftsubFV a0 t_a0 t)} / [ftsize t] @-}
lem_commute_ftsubFV_unbindFT :: Vname -> FType -> Vname -> FType -> Proof
lem_commute_ftsubFV_unbindFT a0 t_a0 a t = lem_commute_ftsubFV_openFT_at a0 t_a0 0 a t

{-@ lem_commute_ftsubFV_openFT_at :: a0:Vname -> { t_a0:FType  | isLCFT t_a0 }
      -> j:Index -> { a:Vname | a != a0 } -> t:FType
      -> {pf:_ | ftsubFV a0 t_a0 (openFT_at j a t) == openFT_at j a (ftsubFV a0 t_a0 t)} / [ftsize t] @-}
lem_commute_ftsubFV_openFT_at :: Vname -> FType -> Index -> Vname -> FType -> Proof
lem_commute_ftsubFV_openFT_at a0 t_a0 j a (FTBasic b)    = case b of
  (FTV aa) | a0 == aa  -> () ? lem_islcft_at_openFT_at j a 0 t_a0
  _                    -> ()
lem_commute_ftsubFV_openFT_at a0 t_a0 j a (FTFunc t1 t2)
  = () ? lem_commute_ftsubFV_openFT_at a0 t_a0 j a t1
       ? lem_commute_ftsubFV_openFT_at a0 t_a0 j a t2
lem_commute_ftsubFV_openFT_at a0 t_a0 j a (FTPoly  k t)
  = () ? lem_commute_ftsubFV_openFT_at a0 t_a0 (j+1) a t

{-@ lem_commute_ftsubFV_ftsubBV :: a:Vname -> { t_a:FType | isLCFT t_a }
      -> t0:FType -> t:FType
      -> { pf:_ | ftsubFV a t_a (ftsubBV t0 t) == ftsubBV (ftsubFV a t_a t0) (ftsubFV a t_a t) } 
       / [ftsize t] @-}
lem_commute_ftsubFV_ftsubBV :: Vname -> FType -> FType -> FType -> Proof
lem_commute_ftsubFV_ftsubBV a t_a t0 t = lem_commute_ftsubFV_ftsubBV_at a t_a 0 t0 t

{-@ lem_commute_ftsubFV_ftsubBV_at :: a:Vname -> { t_a:FType | isLCFT t_a }
      -> j:Index -> t_j:FType -> t:FType
      -> {pf:_ | ftsubFV a t_a (ftsubBV_at j t_j t) == ftsubBV_at j (ftsubFV a t_a t_j) (ftsubFV a t_a t)} 
       / [ftsize t] @-}
lem_commute_ftsubFV_ftsubBV_at :: Vname -> FType -> Index -> FType -> FType -> Proof
lem_commute_ftsubFV_ftsubBV_at a t_a j t_j (FTBasic b)    = case b of
  (FTV aa) | a == aa   -> () ? lem_islcft_at_ftsubBV_at j (ftsubFV a t_a t_j) 0 t_a
  (BTV i)  | i == j    -> () 
  _                    -> ()
lem_commute_ftsubFV_ftsubBV_at a t_a j t_j (FTFunc t1 t2)
  = () ? lem_commute_ftsubFV_ftsubBV_at a t_a j t_j t1
       ? lem_commute_ftsubFV_ftsubBV_at a t_a j t_j t2
lem_commute_ftsubFV_ftsubBV_at a t_a j t_j (FTPoly k t)
  = () ? lem_commute_ftsubFV_ftsubBV_at a t_a (j+1) t_j t
