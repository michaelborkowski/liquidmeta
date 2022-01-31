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

{-@ reflect foo07 @-}   
foo07 x = Just x 
foo07 :: a -> Maybe a 

{-@ lem_union_subset :: a:S.Set Vname -> b:S.Set Vname 
        -> { c:S.Set Vname | Set_sub a c && Set_sub b c }
        -> { pf:_ | Set_sub (Set_cup a b) c } @-}
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

{- READY IF NEEDED
{-@ lem_unbind_lc :: x:Vname -> { e:Expr | isLC e } -> { pf:_ | unbind x e == e } / [esize e] @-} 
lem_unbind_lc :: Vname -> Expr -> Proof
lem_unbind_lc x e = lem_open_at_lc_at 0 x 0 0 e
-}
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

{-
{-@ lem_subFV_id :: x:Vname -> e:Expr -> { pf:_ | subFV x (FV x) e == e } / [esize e] @-}
lem_subFV_id :: Vname -> Expr -> Proof
lem_subFV_id x (Bc b)   = ()
lem_subFV_id x (Ic n)   = ()
lem_subFV_id x (Prim c) = ()
lem_subFV_id x (BV w)   = ()
lem_subFV_id x (FV w) | x == w    = ()
                      | otherwise = ()
lem_subFV_id x e@(Lambda w e')    = () ? lem_subFV_id x e'
lem_subFV_id x (App e1 e2)        = () ? lem_subFV_id x e1
                                       ? lem_subFV_id x e2
lem_subFV_id x (LambdaT a k e')   = () ? lem_subFV_id x e'
lem_subFV_id x (AppT e t)         = () ? lem_subFV_id x e
                                       ? lem_tsubFV_id x t
lem_subFV_id x e@(Let w ew e')    = () ? lem_subFV_id x ew
                                       ? lem_subFV_id x e'
lem_subFV_id x (Annot e' t)       = () ? lem_subFV_id x e'
                                       ? lem_tsubFV_id x t

{-@ lem_chain_subFV :: x:Vname -> y:Vname -> v:Value
      -> { e:Expr | x == y || not (Set_mem y (fv e)) }
      -> { pf:_ | subFV x v e == subFV y v (subFV x (FV y) e) } / [esize e] @-}
lem_chain_subFV :: Vname -> Vname -> Expr -> Expr -> Proof
lem_chain_subFV x y v (Bc b)   = ()
lem_chain_subFV x y v (Ic n)   = ()
lem_chain_subFV x y v (Prim c) = ()
lem_chain_subFV x y v (BV w)   = ()
lem_chain_subFV x y v (FV w)   
    | x == w    = ()
    | otherwise = ()
lem_chain_subFV x y v e@(Lambda w e')    = () ? lem_chain_subFV x y v e'
lem_chain_subFV x y v (App e1 e2)        = () ? lem_chain_subFV x y v e1
                                              ? lem_chain_subFV x y v e2
lem_chain_subFV x y v e@(LambdaT a k e') = () ? lem_chain_subFV x y v e' 
lem_chain_subFV x y v (AppT e t)         = () ? lem_chain_subFV x y v e
                                              ? lem_chain_tsubFV x y v t
lem_chain_subFV x y v e@(Let w ew e')    = () ? lem_chain_subFV x y v ew
                                              ? lem_chain_subFV x y v e'
lem_chain_subFV x y v (Annot e' t)       = () ? lem_chain_subFV x y v e'
                                              ? lem_chain_tsubFV x y v t
-}

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

{-
{-@ lem_commute_subFV_unbind_tv :: x:Vname -> v:Value -> { z:Vname | not (Set_mem z (freeBTV v)) }
        -> { z':Vname | z' != x } -> e:Expr
        -> {pf:_ | subFV x v (unbind_tv z z' e) == unbind_tv z z' (subFV x v e)} / [esize e] @-}
lem_commute_subFV_unbind_tv :: Vname -> Expr -> Vname -> Vname -> Expr -> Proof
lem_commute_subFV_unbind_tv x v z z' (Bc b)       = ()
lem_commute_subFV_unbind_tv x v z z' (Ic n)       = ()
lem_commute_subFV_unbind_tv x v z z' (Prim c)     = ()
lem_commute_subFV_unbind_tv x v z z' (BV w)       = () 
lem_commute_subFV_unbind_tv x v z z' (FV w)       
  | w == x    = () ? lem_unbind_tv_notin z z' v
  | otherwise = ()
lem_commute_subFV_unbind_tv x v z z' (Lambda w e) 
              = () ? lem_commute_subFV_unbind_tv x v z z' e
lem_commute_subFV_unbind_tv x v z z' (App e e')     
              = () ? lem_commute_subFV_unbind_tv x v z z' e
                   ? lem_commute_subFV_unbind_tv x v z z' e'
lem_commute_subFV_unbind_tv x v z z' (LambdaT a k e)
  | a == z    = ()
  | otherwise = () ? lem_commute_subFV_unbind_tv x v z z' e
lem_commute_subFV_unbind_tv x v z z' (AppT e t)     
              = () ? lem_commute_subFV_unbind_tv x v z z' e
                   ? lem_commute_tsubFV_unbind_tvT x v z z' t
lem_commute_subFV_unbind_tv x v z z' (Let w ew e)     
              = () ? lem_commute_subFV_unbind_tv x v z z' ew
                   ? lem_commute_subFV_unbind_tv x v z z' e
lem_commute_subFV_unbind_tv x v z z' (Annot e t)     
              = () ? lem_commute_subFV_unbind_tv x v z z' e
                   ? lem_commute_tsubFV_unbind_tvT x v z z' t

{-@ lem_commute_subFV_subBV :: x:Vname -> v:Value 
        -> y:Vname -> { v_y:Value | not (Set_mem x (freeBV v_y)) } -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x (subFV y v_y v) (subFV y v_y e) } / [esize e] @-}
lem_commute_subFV_subBV :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV x v y v_y (Bc b)       = ()
lem_commute_subFV_subBV x v y v_y (Ic n)       = ()
lem_commute_subFV_subBV x v y v_y (Prim p)     = ()
lem_commute_subFV_subBV x v y v_y (BV w) 
  | x == w    = () -- ? lem_subFV_notin y v_y (BV x)
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (FV w)       
  | y == w    = () 
                   ? lem_unbind_lc x (subFV y v_y v) v_y
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (Lambda w e)
  | x == w    = () 
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (App e e')
              = () ? lem_commute_subFV_subBV x v y v_y e
                   ? lem_commute_subFV_subBV x v y v_y e'
lem_commute_subFV_subBV x v y v_y (LambdaT a k e)
              = () ? lem_commute_subFV_subBV   x v y v_y e
lem_commute_subFV_subBV x v y v_y (AppT e t)
              = () ? lem_commute_subFV_subBV   x v y v_y e
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_subFV_subBV x v y v_y (Let w ew e)
  | x == w    = () ? lem_commute_subFV_subBV x v y v_y ew
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y ew
                   ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (Annot e t)
              = () ? lem_commute_subFV_subBV   x v y v_y e
                   ? lem_commute_tsubFV_tsubBV x v y v_y t

{-@ lem_commute_subFV_subBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> { v_y:Value | not (Set_mem x (freeBV v_y)) } -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x v (subFV y v_y e) } @-}
lem_commute_subFV_subBV1 :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV1 x v y v_y e = lem_commute_subFV_subBV x v y v_y e 
                                           ? lem_subFV_notin y v_y v 

{-@ lem_commute_subFV_subFTV :: a:Vname -> t_a:UserType ->  y:Vname
        -> { v_y:Value | not (Set_mem a (ftv v_y)) } -> e:Expr 
        -> { pf:_ | subFV y v_y (subFTV a t_a e) == 
                    subFTV a (tsubFV y v_y t_a) (subFV y v_y e) } / [esize e] @-} 
lem_commute_subFV_subFTV :: Vname -> Type -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subFTV a t_a x v (Bc b)       = ()
lem_commute_subFV_subFTV a t_a x v (Ic n)       = ()
lem_commute_subFV_subFTV a t_a x v (Prim p)     = ()
lem_commute_subFV_subFTV a t_a x v (BV w)       = ()
lem_commute_subFV_subFTV a t_a x v (FV w)     
  | x == w    = () ? lem_subFTV_notin a (tsubFV x v t_a) v
  | otherwise = ()
lem_commute_subFV_subFTV a t_a x v (Lambda w e)
              = () ? lem_commute_subFV_subFTV a t_a x v e
lem_commute_subFV_subFTV a t_a x v (App e e')
              = () ? lem_commute_subFV_subFTV a t_a x v e
                   ? lem_commute_subFV_subFTV a t_a x v e'
lem_commute_subFV_subFTV a t_a x v (LambdaT a1 k e)
              = () ? lem_commute_subFV_subFTV   a t_a x v e
lem_commute_subFV_subFTV a t_a x v (AppT e t) 
              = () ? lem_commute_subFV_subFTV   a t_a x v e
                   ? lem_commute_tsubFV_tsubFTV a t_a x v t
lem_commute_subFV_subFTV a t_a x v (Let w ew e)
              = () ? lem_commute_subFV_subFTV a t_a x v ew
                   ? lem_commute_subFV_subFTV a t_a x v e
lem_commute_subFV_subFTV a t_a x v (Annot e t)
              = () ? lem_commute_subFV_subFTV   a t_a x v e
                   ? lem_commute_tsubFV_tsubFTV a t_a x v t

{-@ lem_commute_subFV_subBTV :: a:Vname -> t_a:UserType
        -> y:Vname -> { v_y:Value | not (Set_mem a (freeBTV v_y)) } -> e:Expr
        -> { pf:_ | subFV y v_y (subBTV a t_a e) == subBTV a (tsubFV y v_y t_a) (subFV y v_y e) } / [esize e] @-}
lem_commute_subFV_subBTV :: Vname -> Type -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBTV a t_a y v_y (Bc b)       = ()
lem_commute_subFV_subBTV a t_a y v_y (Ic n)       = ()
lem_commute_subFV_subBTV a t_a y v_y (Prim p)     = ()
lem_commute_subFV_subBTV a t_a y v_y (BV w)       = ()
lem_commute_subFV_subBTV a t_a y v_y (FV w)       
  | y == w    = () ? lem_subBTV_notin a (tsubFV y v_y t_a) v_y
  | otherwise = ()
lem_commute_subFV_subBTV a t_a y v_y (Lambda w e)
              = () ? lem_commute_subFV_subBTV   a t_a y v_y e
lem_commute_subFV_subBTV a t_a y v_y (App e e')
              = () ? lem_commute_subFV_subBTV a t_a y v_y e
                   ? lem_commute_subFV_subBTV a t_a y v_y e'
lem_commute_subFV_subBTV a t_a y v_y (LambdaT a' k e)
  | a == a'   = () 
  | otherwise = () ? lem_commute_subFV_subBTV a t_a y v_y e
lem_commute_subFV_subBTV a t_a y v_y (AppT e t)
  = ()      ? lem_commute_subFV_subBTV   a t_a y v_y e
            ? lem_commute_tsubFV_tsubBTV a t_a y v_y t
lem_commute_subFV_subBTV a t_a y v_y (Let w ew e)
              = () ? lem_commute_subFV_subBTV a t_a y v_y ew
                   ? lem_commute_subFV_subBTV a t_a y v_y e
lem_commute_subFV_subBTV a t_a y v_y (Annot e t)
              = () ? lem_commute_subFV_subBTV   a t_a y v_y e
                   ? lem_commute_tsubFV_tsubBTV a t_a y v_y t

{-@ lem_commute_subFV_subBTV1 :: a:Vname -> t_a:UserType
        -> { y:Vname | not (Set_mem y (free t_a)) } -> { v_y:Value | not (Set_mem a (freeBTV v_y)) } 
        -> e:Expr -> { pf:_ | subFV y v_y (subBTV a t_a e) == subBTV a t_a (subFV y v_y e) } @-}
lem_commute_subFV_subBTV1 :: Vname -> Type -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBTV1 a t_a y v_y e = lem_commute_subFV_subBTV a t_a y v_y e 
                                              ? lem_tsubFV_notin y v_y t_a

{-@ lem_commute_subFV :: x:Vname -> v:Value -> { y:Vname | not (y == x)} 
        -> { v_y:Value | not (Set_mem x (fv v_y)) } -> e:Expr 
        -> { pf:_ | subFV y v_y (subFV x v e) == 
                    subFV x (subFV y v_y v) (subFV y v_y e) } / [esize e] @-} 
lem_commute_subFV :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV x v y v_y (Bc b)       = ()
lem_commute_subFV x v y v_y (Ic n)       = ()
lem_commute_subFV x v y v_y (Prim p)     = ()
lem_commute_subFV x v y v_y (BV w)       = ()
lem_commute_subFV x v y v_y (FV w)       
  | x == w    = ()
  | y == w    = () ? lem_subFV_notin x v_y (FV y)
                   ? lem_subFV_notin x (subFV y v_y v) v_y
  | otherwise = ()
lem_commute_subFV x v y v_y (Lambda w e)
              = () ? lem_commute_subFV x v y v_y e
lem_commute_subFV x v y v_y (App e e')
              = () ? lem_commute_subFV x v y v_y e
                   ? lem_commute_subFV x v y v_y e'
lem_commute_subFV x v y v_y (LambdaT a k e)
              = () ? lem_commute_subFV x v y v_y e
lem_commute_subFV x v y v_y (AppT e t)
              = () ? lem_commute_subFV x v y v_y e
                   ? lem_commute_tsubFV x v y v_y t
lem_commute_subFV x v y v_y (Let w ew e)
              = () ? lem_commute_subFV x v y v_y ew
                   ? lem_commute_subFV x v y v_y e
lem_commute_subFV x v y v_y (Annot e t)
              = () ? lem_commute_subFV x v y v_y e
                   ? lem_commute_tsubFV x v y v_y t

------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in TERMS
------------------------------------------------------------------------------

{-@ lem_subBTV_notin :: a:Vname -> t:UserType -> { e:Expr | not (Set_mem a (freeBTV e)) } 
                               -> { pf:_ | subBTV a t e == e } / [esize e] @-} 
lem_subBTV_notin :: Vname -> Type -> Expr -> Proof
lem_subBTV_notin a t (Bc _)           = ()
lem_subBTV_notin a t (Ic _)           = ()
lem_subBTV_notin a t (Prim _)         = ()
lem_subBTV_notin a t (BV w)           = ()
lem_subBTV_notin a t (FV _)           = ()
lem_subBTV_notin a t (Lambda w e)     = () ? lem_subBTV_notin a t e
lem_subBTV_notin a t (App e e')       = () ? lem_subBTV_notin a t e 
                                           ? lem_subBTV_notin a t e'
lem_subBTV_notin a t (LambdaT a' k e) 
    | a == a'                         = ()
    | otherwise                       = () ? lem_subBTV_notin a t e
lem_subBTV_notin a t (AppT e' t')     = () ? lem_subBTV_notin  a t e'
                                           ? lem_tsubBTV_notin a t t' 
lem_subBTV_notin a t (Let w ew e)     = () ? lem_subBTV_notin a t ew
                                           ? lem_subBTV_notin a t e
lem_subBTV_notin a t (Annot e' t')    = () ? lem_subBTV_notin  a t e'
                                           ? lem_tsubBTV_notin a t t'

{-@ lem_commute_subFTV_subFV :: x:Vname -> v:Value -> a:Vname 
        -> { t_a:UserType | not (Set_mem x (free t_a)) } -> e:Expr 
        -> { pf:_ | subFTV a t_a (subFV x v e) == 
                    subFV x (subFTV a t_a v) (subFTV a t_a e) } / [esize e] @-} 
lem_commute_subFTV_subFV :: Vname -> Expr -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subFV x v a t_a (Bc b)       = ()
lem_commute_subFTV_subFV x v a t_a (Ic n)       = ()
lem_commute_subFTV_subFV x v a t_a (Prim p)     = ()
lem_commute_subFTV_subFV x v a t_a (BV w)       = ()
lem_commute_subFTV_subFV x v a t_a (FV w)     
  | x == w    = () ? lem_tsubFV_notin x (subFTV a t_a v) t_a
  | otherwise = ()
lem_commute_subFTV_subFV x v a t_a (Lambda w e)
              = () ? lem_commute_subFTV_subFV x v a t_a e
lem_commute_subFTV_subFV x v a t_a (App e e')
              = () ? lem_commute_subFTV_subFV x v a t_a e
                   ? lem_commute_subFTV_subFV x v a t_a e'
lem_commute_subFTV_subFV x v a t_a (LambdaT a1 k e)
              = () ? lem_commute_subFTV_subFV   x v a t_a e
lem_commute_subFTV_subFV x v a t_a (AppT e t) 
              = () ? lem_commute_subFTV_subFV   x v a t_a e
                   ? lem_commute_tsubFTV_tsubFV x v a t_a t
lem_commute_subFTV_subFV x v a t_a (Let w ew e)
              = () ? lem_commute_subFTV_subFV x v a t_a ew
                   ? lem_commute_subFTV_subFV x v a t_a e
lem_commute_subFTV_subFV x v a t_a (Annot e t)
              = () ? lem_commute_subFTV_subFV   x v a t_a e
                   ? lem_commute_tsubFTV_tsubFV x v a t_a t

{-@ lem_commute_subFTV_subBV :: x:Vname -> v:Value 
        -> a:Vname -> { t_a:UserType | not (Set_mem x (tfreeBV t_a)) } -> e:Expr
        -> { pf:_ | subFTV a t_a (subBV x v e) == subBV x (subFTV a t_a v) (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV_subBV :: Vname -> Expr -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBV x v a t_a (Bc b)       = ()
lem_commute_subFTV_subBV x v a t_a (Ic n)       = ()
lem_commute_subFTV_subBV x v a t_a (Prim p)     = ()
lem_commute_subFTV_subBV x v a t_a (BV w) 
  | x == w    = () -- ? lem_subFV_notin y v_y (BV x)
  | otherwise = ()
lem_commute_subFTV_subBV x v a t_a (FV w)       = () 
lem_commute_subFTV_subBV x v a t_a (Lambda w e)
  | x == w    = () 
  | otherwise = () ? lem_commute_subFTV_subBV x v a t_a e
lem_commute_subFTV_subBV x v a t_a (App e e')
              = () ? lem_commute_subFTV_subBV x v a t_a e
                   ? lem_commute_subFTV_subBV x v a t_a e'
lem_commute_subFTV_subBV x v a t_a (LambdaT a' k e)
              = () ? lem_commute_subFTV_subBV   x v a t_a e
lem_commute_subFTV_subBV x v a t_a (AppT e t) 
              = () ? lem_commute_subFTV_subBV   x v a t_a e
                   ? lem_commute_tsubFTV_tsubBV x v a t_a t
lem_commute_subFTV_subBV x v a t_a (Let w ew e)
  | x == w    = () ? lem_commute_subFTV_subBV x v a t_a ew
  | otherwise = () ? lem_commute_subFTV_subBV x v a t_a ew
                   ? lem_commute_subFTV_subBV x v a t_a e
lem_commute_subFTV_subBV x v a t_a (Annot e t)
              = () ? lem_commute_subFTV_subBV   x v a t_a e
                   ? lem_commute_tsubFTV_tsubBV x v a t_a t

{-@ lem_commute_subFTV_subBV1 :: x:Vname -> v:Value -> { a:Vname | not (Set_mem a (ftv v)) } 
        -> { t_a:UserType | not (Set_mem x (tfreeBV t_a)) } -> e:Expr
        -> { pf:_ | subFTV a t_a (subBV x v e) == subBV x v (subFTV a t_a e) } @-}
lem_commute_subFTV_subBV1 :: Vname -> Expr -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBV1 x v a t_a e = lem_commute_subFTV_subBV x v a t_a e 
                                            ? lem_subFTV_notin a t_a v 

{-@ lem_commute_subFTV :: a1:Vname -> t1:UserType
      -> { a:Vname | not (a1 == a) } -> { t_a:UserType | not (Set_mem a1 (freeTV t_a)) } -> e:Expr
      -> { pf:_ | subFTV a t_a (subFTV a1 t1 e) == subFTV a1 (tsubFTV a t_a t1) (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV :: Vname -> Type -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV a1 t1 a t_a (Bc b)       = ()
lem_commute_subFTV a1 t1 a t_a (Ic n)       = ()
lem_commute_subFTV a1 t1 a t_a (Prim p)     = ()
lem_commute_subFTV a1 t1 a t_a (BV w)       = ()
lem_commute_subFTV a1 t1 a t_a (FV w)       = () 
lem_commute_subFTV a1 t1 a t_a (Lambda w e)
              = () ? lem_commute_subFTV a1 t1 a t_a e
lem_commute_subFTV a1 t1 a t_a (App e e')
              = () ? lem_commute_subFTV a1 t1 a t_a e
                   ? lem_commute_subFTV a1 t1 a t_a e'
lem_commute_subFTV a1 t1 a t_a (LambdaT a' k e)
              = () ? lem_commute_subFTV a1 t1 a t_a e
lem_commute_subFTV a1 t1 a t_a (AppT e t) 
  = ()      ? lem_commute_subFTV  a1 t1 a t_a e
            ? lem_commute_tsubFTV a1 t1 a t_a t
lem_commute_subFTV a1 t1 a t_a (Let w ew e)
              = () ? lem_commute_subFTV a1 t1 a t_a ew
                   ? lem_commute_subFTV a1 t1 a t_a e
lem_commute_subFTV a1 t1 a t_a (Annot e t)
              = () ? lem_commute_subFTV  a1 t1 a t_a e
                   ? lem_commute_tsubFTV a1 t1 a t_a t

{-@ lem_commute_subFTV_subBTV :: a1:Vname -> t1:UserType
        -> a:Vname -> { t_a:UserType | not (Set_mem a1 (tfreeBTV t_a)) } -> e:Expr
        -> { pf:_ | subFTV a t_a (subBTV a1 t1 e) == subBTV a1 (tsubFTV a t_a t1) (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV_subBTV :: Vname -> Type -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBTV a1 t1 a t_a (Bc b)       = ()
lem_commute_subFTV_subBTV a1 t1 a t_a (Ic n)       = ()
lem_commute_subFTV_subBTV a1 t1 a t_a (Prim p)     = ()
lem_commute_subFTV_subBTV a1 t1 a t_a (BV w)       = ()
lem_commute_subFTV_subBTV a1 t1 a t_a (FV w)       = () 
lem_commute_subFTV_subBTV a1 t1 a t_a (Lambda w e)
              = () ? lem_commute_subFTV_subBTV a1 t1 a t_a e
lem_commute_subFTV_subBTV a1 t1 a t_a (App e e')
              = () ? lem_commute_subFTV_subBTV a1 t1 a t_a e
                   ? lem_commute_subFTV_subBTV a1 t1 a t_a e'
lem_commute_subFTV_subBTV a1 t1 a t_a (LambdaT a' k e)
  | a1 == a'  = ()
  | otherwise = () ? lem_commute_subFTV_subBTV a1 t1 a t_a e
lem_commute_subFTV_subBTV a1 t1 a t_a (AppT e t) 
  = ()      ? lem_commute_subFTV_subBTV   a1 t1 a t_a e
            ? lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t
lem_commute_subFTV_subBTV a1 t1 a t_a (Let w ew e)
              = () ? lem_commute_subFTV_subBTV a1 t1 a t_a ew
                   ? lem_commute_subFTV_subBTV a1 t1 a t_a e
lem_commute_subFTV_subBTV a1 t1 a t_a (Annot e t)
              = () ? lem_commute_subFTV_subBTV   a1 t1 a t_a e
                   ? lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t

{-@ lem_commute_subFTV_subBTV1 :: a1:Vname -> t1:UserType 
        -> { a:Vname | not (Set_mem a (freeTV t1)) } -> { t_a:UserType | not (Set_mem a1 (tfreeBTV t_a)) } 
        -> e:Expr -> { pf:_ | subFTV a t_a (subBTV a1 t1 e) == subBTV a1 t1 (subFTV a t_a e) } @-}
lem_commute_subFTV_subBTV1 :: Vname -> Type -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBTV1 a1 t1 a t_a e = lem_commute_subFTV_subBTV a1 t1 a t_a e 
                                               ? lem_tsubFTV_notin a t_a t1
-}

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

{-@ lem_open_tvP_at_lcp_at :: j:Index -> a:Vname -> kx:Index -> { ka:Index | j >= ka } 
        -> { ps:Preds | isLCP_at kx ka ps } -> { pf:_ | open_tvP_at j a ps = ps } / [predsize ps] @-}
lem_open_tvP_at_lcp_at :: Index -> Vname -> Index -> Index -> Preds -> Proof
lem_open_tvP_at_lcp_at j a kx ka PEmpty       = ()
lem_open_tvP_at_lcp_at j a kx ka (PCons p ps) = () ? lem_open_tv_at_lc_at   j a kx ka p
                                                   ? lem_open_tvP_at_lcp_at j a kx ka ps

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


------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TERM VARIABLES in TYPES
------------------------------------------------------------------------------

{-
{-@ lem_tsubFV_id :: x:Vname -> t:Type -> { pf:_ | tsubFV x (FV x) t == t } / [tsize t] @-}
lem_tsubFV_id :: Vname -> Type -> Proof
lem_tsubFV_id x t@(TRefn b w p)      = () ? lem_subFV_id x p
lem_tsubFV_id x t@(TFunc w t_w t')   = () ? lem_tsubFV_id x t_w
                                          ? lem_tsubFV_id x t'
lem_tsubFV_id x t@(TExists w t_w t') = () ? lem_tsubFV_id x t_w
                                          ? lem_tsubFV_id x t'
lem_tsubFV_id x t@(TPoly a k t')     = () ? lem_tsubFV_id x t'
-}

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
{-
{-@ lem_tsubFV_tfreeBV :: x:Vname -> { v:Value | Set_emp (freeBV v) }
        -> { t:Type | Set_emp (tfreeBV t) } -> { pf:_ | Set_emp (tfreeBV (tsubFV x v t)) } @-}
lem_tsubFV_tfreeBV :: Vname -> Expr -> Type -> Proof
lem_tsubFV_tfreeBV x v t@(TRefn b w p)
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFV x v t)) (S.union (tfreeBV t) (freeBV v)) )
lem_tsubFV_tfreeBV x v t@(TFunc w t_w t')
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFV x v t)) (S.union (tfreeBV t) (freeBV v)) )
lem_tsubFV_tfreeBV x v t@(TExists w t_w t')
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFV x v t)) (S.union (tfreeBV t) (freeBV v)) )
lem_tsubFV_tfreeBV x v t@(TPoly a k t')
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFV x v t)) (S.union (tfreeBV t) (freeBV v)) )
-}
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

{-
{-@ lem_chain_tsubFV :: x:Vname -> y:Vname -> v:Value 
        -> { t:Type | x == y || not (Set_mem y (free t)) }
        -> { pf:_ | tsubFV x v t == tsubFV y v (tsubFV x (FV y) t) } / [tsize t] @-}
lem_chain_tsubFV :: Vname -> Vname -> Expr -> Type -> Proof
lem_chain_tsubFV x y v t@(TRefn b w p)     
               = () ? lem_chain_subFV x y v p
lem_chain_tsubFV x y v t@(TFunc w t_w t')
               = () ? lem_chain_tsubFV x y v t_w 
                    ? lem_chain_tsubFV x y v t' 
lem_chain_tsubFV x y v t@(TExists w t_w t') 
               = () ? lem_chain_tsubFV x y v t_w
                    ? lem_chain_tsubFV x y v t'
lem_chain_tsubFV x y v (TPoly a k t) = () ? lem_chain_tsubFV x y v t
-}

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

{-
{-@ lem_commute_tsubFV_tsubBV :: x:Vname -> v:Value 
        -> y:Vname -> { v_y:Value | not (Set_mem x (freeBV v_y)) }  -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x (subFV y v_y v) (tsubFV y v_y t) } / [tsize t] @-}
lem_commute_tsubFV_tsubBV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV x v y v_y (TRefn b w p)
  | x == 0    = ()
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y p
lem_commute_tsubFV_tsubBV x v y v_y (TFunc w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_tsubFV_tsubBV x v y v_y (TExists w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_tsubFV_tsubBV x v y v_y (TPoly a k t) 
              = () ? lem_commute_tsubFV_tsubBV x v y v_y t

{-@ lem_commute_tsubFV_tsubBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> { v_y:Value | not (Set_mem x (freeBV v_y)) } -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x v (tsubFV y v_y t) } @-}
lem_commute_tsubFV_tsubBV1 :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV1 x v y v_y t = lem_commute_tsubFV_tsubBV x v y v_y t
                                             ? lem_subFV_notin y v_y v

{-@ lem_commute_tsubFV_tsubFTV :: a:Vname -> t_a:UserType ->  y:Vname
        -> { v_y:Value | not (Set_mem a (ftv v_y)) } -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubFTV a t_a t) == 
                    tsubFTV a (tsubFV y v_y t_a) (tsubFV y v_y t) } / [tsize t] @-} 
lem_commute_tsubFV_tsubFTV :: Vname -> Type -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubFTV a t_a x v (TRefn b w p) = case b of
  (FTV a1) | a == a1   -> () ? lem_commute_subFV_subFTV a t_a x v p
                             ? lem_subFV_push x v (subFTV a t_a p) t_a
           | otherwise -> () ? lem_commute_subFV_subFTV a t_a x v p
  _                    -> () ? lem_commute_subFV_subFTV a t_a x v p
lem_commute_tsubFV_tsubFTV a t_a x v (TFunc w t_w t)
              = () ? lem_commute_tsubFV_tsubFTV a t_a x v t_w
                   ? lem_commute_tsubFV_tsubFTV a t_a x v t
lem_commute_tsubFV_tsubFTV a t_a x v (TExists w t_w t)
              = () ? lem_commute_tsubFV_tsubFTV a t_a x v t_w
                   ? lem_commute_tsubFV_tsubFTV a t_a x v t
lem_commute_tsubFV_tsubFTV a t_a x v (TPoly a1 k t) 
              = () ? lem_commute_tsubFV_tsubFTV a t_a x v t

{-@ lem_commute_tsubFV_tsubBTV :: a:Vname -> t_a:UserType
        -> y:Vname -> { v_y:Value | not (Set_mem a (freeBTV v_y)) }  -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBTV a t_a t) == tsubBTV a (tsubFV y v_y t_a) (tsubFV y v_y t) } / [tsize t] @-}
lem_commute_tsubFV_tsubBTV :: Vname -> Type -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBTV a t_a y v_y (TRefn b w p) = case b of
  (BTV a') | a == a' -> () ? lem_commute_subFV_subBTV a t_a y v_y p
                           ? lem_subFV_push           y v_y (subBTV a t_a p) t_a
  _                  -> () ? lem_commute_subFV_subBTV a t_a y v_y p
lem_commute_tsubFV_tsubBTV a t_a y v_y (TFunc w t_w t)
              = () ? lem_commute_tsubFV_tsubBTV a t_a y v_y t_w
                   ? lem_commute_tsubFV_tsubBTV a t_a y v_y t
lem_commute_tsubFV_tsubBTV a t_a y v_y (TExists w t_w t)
              = () ? lem_commute_tsubFV_tsubBTV a t_a y v_y t_w
                   ? lem_commute_tsubFV_tsubBTV a t_a y v_y t
lem_commute_tsubFV_tsubBTV a t_a y v_y (TPoly a' k t) 
  | a == a'   = ()
  | otherwise = () ? lem_commute_tsubFV_tsubBTV a t_a y v_y t

{-@ lem_commute_tsubFV_tsubBTV1 :: a:Vname -> t_a:UserType
        -> { y:Vname | not (Set_mem y (free t_a)) } -> { v_y:Value | not (Set_mem a (freeBTV v_y)) } 
        -> t:Type -> { pf:_ | tsubFV y v_y (tsubBTV a t_a t) == tsubBTV a t_a (tsubFV y v_y t) } @-}
lem_commute_tsubFV_tsubBTV1 :: Vname -> Type -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBTV1 a t_a y v_y t = lem_commute_tsubFV_tsubBTV a t_a y v_y t
                                                ? lem_tsubFV_notin y v_y t_a

{-@ lem_commute_tsubFV :: x:Vname -> v:Value -> { y:Vname | not ( y == x ) } 
        -> { v_y:Value | not (Set_mem x (fv v_y)) } -> t:Type 
        -> { pf:_ | tsubFV y v_y (tsubFV x v t) 
                 == tsubFV x (subFV y v_y v) (tsubFV y v_y t) } / [tsize t] @-}
lem_commute_tsubFV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV x v y v_y (TRefn b w p)     = () ? lem_commute_subFV x v y v_y p
lem_commute_tsubFV x v y v_y (TFunc w t_w t)   = () ? lem_commute_tsubFV x v y v_y t_w
                                                    ? lem_commute_tsubFV x v y v_y t
lem_commute_tsubFV x v y v_y (TExists w t_w t) = () ? lem_commute_tsubFV x v y v_y t_w
                                                    ? lem_commute_tsubFV x v y v_y t
lem_commute_tsubFV x v y v_y (TPoly a k t)     = () ? lem_commute_tsubFV x v y v_y t
-}

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

{-
{-@ lem_tsubBTV_notin :: a:Vname -> t_a:UserType -> { t:Type | not (Set_mem a (tfreeBTV t)) }
                -> { pf:_ | tsubBTV a t_a t == t } / [tsize t] @-} 
lem_tsubBTV_notin :: Vname -> Type -> Type -> Proof
lem_tsubBTV_notin a t_a (TRefn b y r)        = () ? lem_subBTV_notin a t_a r
lem_tsubBTV_notin a t_a (TFunc z t_z t)      = () ? lem_tsubBTV_notin a t_a t_z
                                                  ? lem_tsubBTV_notin a t_a t
lem_tsubBTV_notin a t_a (TExists z t_z t)    = () ? lem_tsubBTV_notin a t_a t_z
                                                  ? lem_tsubBTV_notin a t_a t
lem_tsubBTV_notin a t_a (TPoly a' k t') 
    | a == a'   = ()
    | otherwise = () ? lem_tsubBTV_notin a t_a t'

{-@ lem_tsubFTV_trefn :: a:Vname -> { t_a:UserType | isTRefn t_a } -> { t:Type | isTRefn t }
        -> { pf:_ | isTRefn (tsubFTV a t_a t) } @-}
lem_tsubFTV_trefn :: Vname -> Type -> Type -> Proof
lem_tsubFTV_trefn a (TRefn b' y' q') (TRefn b z p) = case b of
  (FTV a') | a' == a  -> () {-? toProof (
        tsubFTV a (TRefn b' y' q') (TRefn b z p)
    === push (subFTV a (TRefn b' y' q') p) (TRefn b' y' q')
    === TRefn b' y' (strengthen (subFTV a (TRefn b' y' q') p) q') )-}
  _                   -> ()

{-@ lem_tsubFTV_tfreeBV :: a:Vname -> { t_a:UserType | Set_emp (tfreeBV t_a) }
        -> { t:Type | Set_emp (tfreeBV t) } -> { pf:_ | Set_emp (tfreeBV (tsubFTV a t_a t)) } @-}
lem_tsubFTV_tfreeBV :: Vname -> Type -> Type -> Proof
lem_tsubFTV_tfreeBV a t_a t@(TRefn b w p)
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFTV a t_a t)) (S.union (tfreeBV t) (tfreeBV t_a)) )
lem_tsubFTV_tfreeBV a t_a t@(TFunc w t_w t')
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFTV a t_a t)) (S.union (tfreeBV t) (tfreeBV t_a)) )
lem_tsubFTV_tfreeBV a t_a t@(TExists w t_w t')
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFTV a t_a t)) (S.union (tfreeBV t) (tfreeBV t_a)) )
lem_tsubFTV_tfreeBV a t_a t@(TPoly a' k t')
  = () ? toProof ( S.isSubsetOf (tfreeBV (tsubFTV a t_a t)) (S.union (tfreeBV t) (tfreeBV t_a)) )
-}
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

{-
{-@ lem_commute_tsubFTV_tsubFV :: x:Vname -> v:Value -> a:Vname 
        -> { t_a:UserType | not (Set_mem x (free t_a)) } -> t:Type
        -> { pf:_ | tsubFTV a t_a (tsubFV x v t) == 
                    tsubFV x (subFTV a t_a v) (tsubFTV a t_a t) } / [tsize t] @-} 
lem_commute_tsubFTV_tsubFV :: Vname -> Expr -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubFV x v a t_a (TRefn b w p) = case b of
  (FTV a1) | a == a1   -> () ? lem_commute_subFTV_subFV x v a t_a p
                             ? lem_tsubFV_notin x (subFTV a t_a v) t_a
                             ? lem_subFV_push x (subFTV a t_a v) (subFTV a t_a p) t_a
           | otherwise -> () ? lem_commute_subFTV_subFV x v a t_a p
  _                    -> () ? lem_commute_subFTV_subFV x v a t_a p
lem_commute_tsubFTV_tsubFV x v a t_a (TFunc w t_w t)
              = () ? lem_commute_tsubFTV_tsubFV x v a t_a t_w
                   ? lem_commute_tsubFTV_tsubFV x v a t_a t
lem_commute_tsubFTV_tsubFV x v a t_a (TExists w t_w t)
              = () ? lem_commute_tsubFTV_tsubFV x v a t_a t_w
                   ? lem_commute_tsubFTV_tsubFV x v a t_a t
lem_commute_tsubFTV_tsubFV x v a t_a (TPoly a1 k t) 
              = () ? lem_commute_tsubFTV_tsubFV x v a t_a t

{-@ lem_commute_tsubFTV_unbindT :: a:Vname -> t_a:UserType 
        -> { x:Vname | not (Set_mem x (tfreeBV t_a)) } -> y:Vname -> t:Type 
        -> { pf:_ | tsubFTV a t_a (unbindT x y t) == unbindT x y (tsubFTV a t_a t)} / [tsize t] @-}
lem_commute_tsubFTV_unbindT :: Vname -> Type -> Vname -> Vname -> Type -> Proof
lem_commute_tsubFTV_unbindT a t_a x y (TRefn b w p) = case b of
  (FTV a0) | a0 == a && ( x == 0 )   -> () ? lem_tsubBV_RVname x (FV y) (push (subFTV a t_a p) t_a)
           | a0 == a && not (x == 0) -> () ? lem_commute_subFTV_unbind a t_a x y p
                                           ? lem_subBV_push x (FV y) (subFTV a t_a p) t_a
                                           ? lem_tsubBV_notin x (FV y) t_a
           | otherwise -> () ? lem_commute_subFTV_unbind a t_a x y p
  _        | x == 0    -> ()
           | otherwise -> () ? lem_commute_subFTV_unbind a t_a x y p
lem_commute_tsubFTV_unbindT a t_a x y (TFunc w t_w t)
  | x == w    = () ? lem_commute_tsubFTV_unbindT a t_a x y t_w
  | otherwise = () ? lem_commute_tsubFTV_unbindT a t_a x y t_w
                   ? lem_commute_tsubFTV_unbindT a t_a x y t
lem_commute_tsubFTV_unbindT a t_a x y (TExists w t_w t)
  | x == w    = () ? lem_commute_tsubFTV_unbindT a t_a x y t_w
  | otherwise = () ? lem_commute_tsubFTV_unbindT a t_a x y t_w
                   ? lem_commute_tsubFTV_unbindT a t_a x y t
lem_commute_tsubFTV_unbindT a t_a x y (TPoly a0 k0 t)
              = () ? lem_commute_tsubFTV_unbindT a t_a x y t

{-@ lem_commute_tsubFTV_unbind_tvT :: a:Vname -> t_a:UserType 
        -> { a1:Vname | not (Set_mem a1 (tfreeBTV t_a)) } -> { a1':Vname | a1' != a } -> t:Type 
        -> {pf:_ | tsubFTV a t_a (unbind_tvT a1 a1' t) == unbind_tvT a1 a1' (tsubFTV a t_a t)} / [tsize t] @-}
lem_commute_tsubFTV_unbind_tvT :: Vname -> Type -> Vname -> Vname -> Type -> Proof
lem_commute_tsubFTV_unbind_tvT a t_a a1 a1' (TRefn b w p) = case b of
  (FTV a0) | a0 == a   -> () ? lem_commute_subFTV_unbind_tv a t_a a1 a1' p
                             ? lem_unbind_tv_push   a1 a1' (subFTV a t_a p) t_a
                             ? lem_unbind_tvT_notin a1 a1' t_a
           | otherwise -> () ? lem_commute_subFTV_unbind_tv a t_a a1 a1' p
  (BTV a0) | a0 == a1  -> () ? lem_commute_subFTV_unbind_tv a t_a a1 a1' p
           | otherwise -> () ? lem_commute_subFTV_unbind_tv a t_a a1 a1' p
  _                    -> () ? lem_commute_subFTV_unbind_tv a t_a a1 a1' p
lem_commute_tsubFTV_unbind_tvT a t_a z z' (TFunc w t_w t)
              = () ? lem_commute_tsubFTV_unbind_tvT a t_a z z' t_w
                   ? lem_commute_tsubFTV_unbind_tvT a t_a z z' t
lem_commute_tsubFTV_unbind_tvT a t_a z z' (TExists w t_w t)
              = () ? lem_commute_tsubFTV_unbind_tvT a t_a z z' t_w
                   ? lem_commute_tsubFTV_unbind_tvT a t_a z z' t
lem_commute_tsubFTV_unbind_tvT a t_a z z' (TPoly a0 k0 t)
  | z == a0   = ()
  | otherwise = () ? lem_commute_tsubFTV_unbind_tvT a t_a z z' t

{-@ lem_commute_tsubFTV_tsubBV :: x:Vname -> v:Value 
        -> a:Vname -> { t_a:UserType | not (Set_mem x (tfreeBV t_a)) } -> t:Type
        -> { pf:_ | tsubFTV a t_a (tsubBV x v t) == tsubBV x (subFTV a t_a v) (tsubFTV a t_a t) } / [tsize t] @-}
lem_commute_tsubFTV_tsubBV :: Vname -> Expr -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBV x v a t_a (TRefn b w p) = case b of
  (FTV a') | a == a' && x == 0       -> () ? lem_tsubBV_RVname x (subFTV a t_a v) 
                                                                 (tsubFTV a t_a (TRefn b w p))
           | a == a' && not (x == 0) -> () ? lem_commute_subFTV_subBV x v a t_a p
                                           ? lem_subBV_push x (subFTV a t_a v) (subFTV a t_a p) t_a
                                           ? lem_tsubBV_notin x (subFTV a t_a v) t_a
           | otherwise -> () ? lem_commute_subFTV_subBV x v a t_a p
  _        | x == 0    -> () 
           | otherwise -> () ? lem_commute_subFTV_subBV x v a t_a p
lem_commute_tsubFTV_tsubBV x v a t_a (TFunc w t_w t)
  | x == w    = () ? lem_commute_tsubFTV_tsubBV x v a t_a t_w
  | otherwise = () ? lem_commute_tsubFTV_tsubBV x v a t_a t_w
                   ? lem_commute_tsubFTV_tsubBV x v a t_a t
lem_commute_tsubFTV_tsubBV x v a t_a (TExists w t_w t)
  | x == w    = () ? lem_commute_tsubFTV_tsubBV x v a t_a t_w
  | otherwise = () ? lem_commute_tsubFTV_tsubBV x v a t_a t_w
                   ? lem_commute_tsubFTV_tsubBV x v a t_a t
lem_commute_tsubFTV_tsubBV x v a t_a (TPoly a' k t) 
              = () ? lem_commute_tsubFTV_tsubBV x v a t_a t

{-@ lem_commute_tsubFTV_tsubBV1 :: x:Vname -> v:Value 
        -> { a:Vname | not (Set_mem a (ftv v)) } 
        -> { t_a:UserType | not (Set_mem x (tfreeBV t_a)) } -> t:Type
        -> { pf:_ | tsubFTV a t_a (tsubBV x v t) == tsubBV x v (tsubFTV a t_a t) } @-}
lem_commute_tsubFTV_tsubBV1 :: Vname -> Expr -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBV1 x v a t_a t = lem_commute_tsubFTV_tsubBV x v a t_a t
                                             ? lem_subFTV_notin a t_a v

{-@ lem_commute_tsubFTV :: a1:Vname -> t1:UserType
        -> { a:Vname | not (a1 == a) } -> { t_a:UserType | not (Set_mem a1 (freeTV t_a)) } -> t:Type
        -> { pf:_ | tsubFTV a  t_a                (tsubFTV a1 t1 t) 
                 == tsubFTV a1 (tsubFTV a t_a t1) (tsubFTV a t_a t) } / [tsize t] @-}
lem_commute_tsubFTV :: Vname -> Type -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV a1 t1 a t_a (TRefn b w p) = case b of
  (FTV a') | a  == a'       -> () ? lem_commute_subFTV a1 t1 a t_a p
                                  ? lem_subFTV_push a1 (tsubFTV a t_a t1) (subFTV a t_a p) t_a
                                  ? lem_tsubFTV_notin a1 (tsubFTV a t_a t1) t_a
  (FTV a') | a1 == a'       -> () ? lem_commute_subFTV a1 t1 a t_a p
                                  ? lem_subFTV_push a t_a (subFTV a1 t1 p) t1
  _                         -> () ? lem_commute_subFTV a1 t1 a t_a p
lem_commute_tsubFTV a1 t1 a t_a (TFunc w t_w t)
              = () ? lem_commute_tsubFTV a1 t1 a t_a t_w
                   ? lem_commute_tsubFTV a1 t1 a t_a t
lem_commute_tsubFTV a1 t1 a t_a (TExists w t_w t)
              = () ? lem_commute_tsubFTV a1 t1 a t_a t_w
                   ? lem_commute_tsubFTV a1 t1 a t_a t
lem_commute_tsubFTV a1 t1 a t_a (TPoly a' k t) 
              = () ? lem_commute_tsubFTV a1 t1 a t_a t

{-@ lem_commute_tsubFTV_tsubBTV :: a1:Vname -> t1:UserType
        -> a:Vname -> { t_a:UserType | not (Set_mem a1 (tfreeBTV t_a)) } -> t:Type
        -> { pf:_ | tsubFTV a  t_a                (tsubBTV a1 t1 t) 
                 == tsubBTV a1 (tsubFTV a t_a t1) (tsubFTV a t_a t) } / [tsize t] @-}
lem_commute_tsubFTV_tsubBTV :: Vname -> Type -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBTV a1 t1 a t_a (TRefn b w p) = case b of
  (FTV a') | a  == a'       -> () ? lem_commute_subFTV_subBTV a1 t1 a t_a p
                                  ? lem_subBTV_push a1 (tsubFTV a t_a t1) (subFTV a t_a p) t_a
                                  ? lem_tsubBTV_notin a1 (tsubFTV a t_a t1) t_a
  (BTV a') | a1 == a'       -> () ? lem_commute_subFTV_subBTV a1 t1 a t_a p
                                  ? lem_subFTV_push a t_a (subBTV a1 t1 p) t1
  _                         -> () ? lem_commute_subFTV_subBTV a1 t1 a t_a p
lem_commute_tsubFTV_tsubBTV a1 t1 a t_a (TFunc w t_w t)
              = () ? lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t_w
                   ? lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t
lem_commute_tsubFTV_tsubBTV a1 t1 a t_a (TExists w t_w t)
              = () ? lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t_w
                   ? lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t
lem_commute_tsubFTV_tsubBTV a1 t1 a t_a (TPoly a' k t) 
  | a1 == a'  = ()
  | otherwise = () ? lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t

{-@ lem_commute_tsubFTV_tsubBTV1 :: a1:Vname -> t1:UserType 
        -> { a:Vname | not (Set_mem a (freeTV t1)) } -> { t_a:UserType | not (Set_mem a1 (tfreeBTV t_a)) } 
        -> t:Type -> { pf:_ | tsubFTV a t_a (tsubBTV a1 t1 t) == tsubBTV a1 t1 (tsubFTV a t_a t) } @-}
lem_commute_tsubFTV_tsubBTV1 :: Vname -> Type -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBTV1 a1 t1 a t_a t = lem_commute_tsubFTV_tsubBTV a1 t1 a t_a t
                                                 ? lem_tsubFTV_notin a t_a t1

{-@ lem_commute_tchgFTV_tsubBTV :: a1:Vname -> t1:UserType
        -> a:Vname -> a':Vname -> t:Type
        -> { pf:_ | tchgFTV a  a'                (tsubBTV a1 t1 t) 
                 == tsubBTV a1 (tchgFTV a a' t1) (tchgFTV a a' t) } / [tsize t] @-}
lem_commute_tchgFTV_tsubBTV :: Vname -> Type -> Vname -> Vname -> Type -> Proof
lem_commute_tchgFTV_tsubBTV a1 t1 a a' (TRefn b w p) = case b of
  (FTV a2) | a  == a2       -> () ? lem_commute_chgFTV_subBTV a1 t1 a a' p
  (BTV a2) | a1 == a2       -> () ? lem_commute_chgFTV_subBTV a1 t1 a a' p
                                  ? lem_chgFTV_push a a' (subBTV a1 t1 p) t1
  _                         -> () ? lem_commute_chgFTV_subBTV a1 t1 a a' p
lem_commute_tchgFTV_tsubBTV a1 t1 a a' (TFunc w t_w t)
              = () ? lem_commute_tchgFTV_tsubBTV a1 t1 a a' t_w
                   ? lem_commute_tchgFTV_tsubBTV a1 t1 a a' t
lem_commute_tchgFTV_tsubBTV a1 t1 a a' (TExists w t_w t)
              = () ? lem_commute_tchgFTV_tsubBTV a1 t1 a a' t_w
                   ? lem_commute_tchgFTV_tsubBTV a1 t1 a a' t
lem_commute_tchgFTV_tsubBTV a1 t1 a a' (TPoly a2 k t) 
  | a1 == a2  = ()
  | otherwise = () ? lem_commute_tchgFTV_tsubBTV a1 t1 a a' t
-}
---------------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION and the PUSH function
---------------------------------------------------------------------------------------

{-@ lem_push_empty :: t_a:UserType -> { pf:_ | push PEmpty t_a == t_a } @-}
lem_push_empty ::  Type -> Proof
lem_push_empty (TRefn b rs)   = toProof ( strengthen PEmpty rs )
lem_push_empty (TFunc  t_z t) = () 
lem_push_empty (TPoly   k' t) = () 

{-ready
{-@ lem_unbindT_push :: y:Vname -> ps:Preds -> t_a:UserType
        -> { pf:_ | unbindT y (push ps t_a) == push (unbindP y ps) (unbindT y t_a) } @-}
lem_unbindT_push :: Vname -> Preds -> UserType -> Proof
lem_unbindT_push y ps ps' = lem_openT_at_push 0 y ps ps'-}

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

{-
{-@ lem_push_strengthen :: p:Pred -> r:Pred -> t:Type
        -> { pf:_ | push (strengthen p r) t == push p (push r t) } @-}
lem_push_strengthen :: Expr -> Expr -> Type -> Proof
lem_push_strengthen p r (TRefn b z q)     = () ? lem_strengthen_assoc p r q
lem_push_strengthen p r (TFunc z t_z t)   = () ? lem_push_strengthen p r t_z
                                               ? lem_push_strengthen p r t
lem_push_strengthen p r (TExists z t_z t) = () ? lem_push_strengthen p r t_z
                                               ? lem_push_strengthen p r t
lem_push_strengthen p r (TPoly a k t)     = () ? lem_push_strengthen p r t

{-@ lem_subFV_push :: x:Vname -> v:Value -> p:Pred -> t:UserType
        -> { pf:_ | tsubFV x v (push p t) == push (subFV x v p) (tsubFV x v t) } @-}
lem_subFV_push :: Vname -> Expr -> Expr -> Type -> Proof
lem_subFV_push x v p (TRefn   b z   r) = () ? lem_subFV_strengthen x v p r
lem_subFV_push x v p (TFunc   y t_y t) = () ? lem_subFV_push x v p t_y 
                                            ? lem_subFV_push x v p t
lem_subFV_push x v p (TPoly   a k   t) = () ? lem_subFV_push x v p t

{-@ lem_subBV_push :: { x:Vname | not (x == 0) } -> v:Value -> p:Pred -> t:UserType
        -> { pf:_ | tsubBV x v (push p t) == push (subBV x v p) (tsubBV x v t) } @-}
lem_subBV_push :: Vname -> Expr -> Expr -> Type -> Proof
lem_subBV_push x v p (TRefn   b z   r) = () ? lem_subBV_strengthen x v p r
lem_subBV_push x v p (TFunc   y t_y t) = () ? lem_subBV_push x v p t_y 
                                            ? lem_subBV_push x v p t
lem_subBV_push x v p (TPoly   a k   t) = () ? lem_subBV_push x v p t

{-@ lem_subFTV_push :: a:Vname -> t_a:UserType -> p:Pred -> t:UserType
        -> { pf:_ | tsubFTV a t_a (push p t) == push (subFTV a t_a p) (tsubFTV a t_a t) } @-}
lem_subFTV_push :: Vname -> Type -> Expr -> Type -> Proof
lem_subFTV_push a t_a p (TRefn   b z   r) = case b of 
  (FTV a') | a == a'  -> () {-? toProof ( tsubFTV a t_a (push p (TRefn (FTV a) z r))
                    === tsubFTV a t_a (TRefn b z (strengthen p r))
                    === push (subFTV a t_a (strengthen p r)) t_a-}
                      ? lem_subFTV_strengthen a t_a p r
--                    === push (strengthen (subFTV a t_a p) (subFTV a t_a r)) t_a
                      ? lem_push_strengthen (subFTV a t_a p) (subFTV a t_a r) t_a
  {-                  === push (subFTV a t_a p) (push (subFTV a t_a r) t_a)
                    === push (subFTV a t_a p) (tsubFTV a t_a (TRefn (FTV a) z r)) )-}
  _        -> () ? lem_subFTV_strengthen a t_a p r    
lem_subFTV_push a t_a p (TFunc   y t_y t) = () ? lem_subFTV_push a t_a p t_y
                                               ? lem_subFTV_push a t_a p t
lem_subFTV_push a t_a p (TPoly   a' k  t) = () ? lem_subFTV_push a t_a p t

{-@ lem_subBTV_push ::  a:Vname -> t_a:UserType -> p:Pred -> t:UserType 
        -> { pf:_ | tsubBTV a t_a (push p t) == push (subBTV a t_a p) (tsubBTV a t_a t) } @-}
lem_subBTV_push :: Vname -> Type -> Expr -> Type -> Proof
lem_subBTV_push a t_a p (TRefn   b z   r) = case b of 
  (BTV a') | a == a'  -> () ? lem_subBTV_strengthen a t_a p r
                            ? lem_push_strengthen (subBTV a t_a p) (subBTV a t_a r) t_a
  _        -> () ? lem_subBTV_strengthen a t_a p r    
lem_subBTV_push a t_a p (TFunc   y t_y t) = () ? lem_subBTV_push a t_a p t_y
                                               ? lem_subBTV_push a t_a p t
lem_subBTV_push a t_a p (TPoly   a' k  t) = () ? lem_subBTV_push a t_a p t
-}

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
