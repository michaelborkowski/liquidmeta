{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsSubstitution where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

{-@ reflect foo15 @-}   
foo15 x = Just x 
foo15 :: a -> Maybe a 

{-@ lem_union_subset :: a:S.Set Vname -> b:S.Set Vname 
        -> { c:S.Set Vname | Set_sub a c && Set_sub b c }
        -> { pf:_ | Set_sub (Set_cup a b) c } @-}
lem_union_subset :: S.Set Vname -> S.Set Vname -> S.Set Vname -> Proof
lem_union_subset a b c = ()

---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION
---------------------------------------------------------------------------

--                        -> { pf:_ | isValue (subFV y v_y v) && Set_emp (freeBV (subFV y v_y v)) } @-}
-- Lemmas. The set of Values is closed under substitution.
{-@ lem_subFV_value :: y:Vname -> v_y:Value -> v:Value -> { pf:_ | isValue (subFV y v_y v) } @-}
lem_subFV_value :: Vname -> Expr -> Expr -> Proof
lem_subFV_value y v_y (Bc _)          = ()
lem_subFV_value y v_y (Ic _)          = ()
lem_subFV_value y v_y (Prim _)        = ()
lem_subFV_value y v_y (FV x) 
    | x == y    = () -- toProof ( subFV y v_y (FV x) === v_y ) 
    | otherwise = () -- toProof ( subFV y v_y (FV x) === FV x)
lem_subFV_value y v_y (Lambda x e) 
    | x == y    = () -- toProof ( subFV y v_y (Lambda x e) === Lambda x (subFV y v_y e) )
    | otherwise = () {- toProof ( freeBV (subFV y v_y (Lambda x e))
                        === freeBV (Lambda x (subFV y v_y e))
                        === S.difference (freeBV (subFV y v_y e)) (S.singleton x)
                        === S.empty ) -}
lem_subFV_value y v_y (LambdaT a k e) = ()
lem_subFV_value y v_y Crash           = ()  

{-@ lem_subFV_notin :: x:Vname -> v:Value -> { e:Expr | not (Set_mem x (fv e)) } 
                               -> { pf:_ | subFV x v e == e } / [esize e] @-}
lem_subFV_notin :: Vname -> Expr -> Expr -> Proof
lem_subFV_notin x v (Bc b)           = ()
lem_subFV_notin x v (Ic n)           = ()
lem_subFV_notin x v (Prim c)         = ()
lem_subFV_notin x v (BV y)           = ()
lem_subFV_notin x v (FV y)           = ()
lem_subFV_notin x v e@(Lambda w e')  = () ? lem_subFV_notin x v e'
lem_subFV_notin x v (App e1 e2)      = () ? lem_subFV_notin x v e1
                                          ? lem_subFV_notin x v e2
lem_subFV_notin x v (LambdaT a k e') = () ? lem_subFV_notin x v e'
lem_subFV_notin x v (AppT e t)       = () ? lem_subFV_notin x v e
                                          ? lem_tsubFV_notin x v t
lem_subFV_notin x v e@(Let w ew e')  = () ? lem_subFV_notin x v ew
                                          ? lem_subFV_notin x v e'
lem_subFV_notin x v (Annot e' t)     = () ? lem_subFV_notin x v e'
                                          ? lem_tsubFV_notin x v t
lem_subFV_notin x v (Crash)          = () 

{-@ lem_subBV_notin :: x:Vname -> v_x:Value -> { e:Expr | not (Set_mem x (freeBV e)) } 
                               -> { pf:_ | subBV x v_x e == e } / [esize e] @-} 
lem_subBV_notin :: Vname -> Expr -> Expr -> Proof
lem_subBV_notin x v_x (Bc _)          = ()
lem_subBV_notin x v_x (Ic _)          = ()
lem_subBV_notin x v_x (Prim _)        = ()
lem_subBV_notin x v_x (BV w)          = ()
lem_subBV_notin x v_x (FV _)          = ()
lem_subBV_notin x v_x (Lambda w e)
    | x == w    = ()
    | otherwise = () ? lem_subBV_notin x v_x e
lem_subBV_notin x v_x (App e e')      = () ? lem_subBV_notin x v_x e 
                                           ? lem_subBV_notin x v_x e'
lem_subBV_notin x v_x (LambdaT a k e) = () ? lem_subBV_notin x v_x e
lem_subBV_notin x v_x (AppT e t)      = () ? lem_subBV_notin x v_x e
                                           ? lem_tsubBV_notin x v_x t
lem_subBV_notin x v_x (Let w ew e)
    | x == w    = () ? lem_subBV_notin x v_x ew
    | otherwise = () ? lem_subBV_notin x v_x ew
                     ? lem_subBV_notin x v_x e
lem_subBV_notin x v_x (Annot e t)     = () ? lem_subBV_notin x v_x e
                                           ? lem_tsubBV_notin x v_x t  
lem_subBV_notin x v_x Crash           = ()


{-@ lem_subFV_unbind :: x:Vname -> y:Vname -> v:Value
      -> { e:Expr | not (Set_mem y (fv e)) }
      -> { pf:_ | subBV x v e == subFV y v (unbind x y e) } / [esize e] @-}
lem_subFV_unbind :: Vname -> Vname -> Expr -> Expr -> Proof
lem_subFV_unbind x y v (Bc b)   = ()
lem_subFV_unbind x y v (Ic n)   = ()
lem_subFV_unbind x y v (Prim c) = ()
lem_subFV_unbind x y v (BV w)
    | x == w    = ()
    | otherwise = ()
lem_subFV_unbind x y v (FV w)   = ()
lem_subFV_unbind x y v e@(Lambda w e') 
    | x == w    = () ? lem_subFV_notin y v e'
                     {- ? toProof ( subFV y v (unbind x y e)
                        === subFV y v (Lambda w e')
                        === Lambda w (subFV y v e')
                        === Lambda w e'
                        === subBV x v (Lambda w e') )  -}
    | otherwise = () ? lem_subFV_unbind x y v e'
lem_subFV_unbind x y v (App e1 e2) 
                = () ? lem_subFV_unbind x y v e1
                     ? lem_subFV_unbind x y v e2
lem_subFV_unbind x y v (LambdaT a k e')
                = () ? lem_subFV_unbind x y v e'
lem_subFV_unbind x y v (AppT e t)
                = () ? lem_subFV_unbind x y v e
                     ? lem_tsubFV_unbindT x y v t
lem_subFV_unbind x y v e@(Let w ew e')
    | x == w    = () ? lem_subFV_unbind x y v ew
                     ? lem_subFV_notin y v e'
                     -- ? toProof ( subFV y v e' === e' )
    | otherwise = () ? lem_subFV_unbind x y v ew
                     ? lem_subFV_unbind x y v e'
lem_subFV_unbind x y v (Annot e' t)
                = () ? lem_subFV_unbind x y v e'
                     ? lem_tsubFV_unbindT x y v t
lem_subFV_unbind x y v (Crash)  = () 

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
lem_subFV_id x (Crash)            = () 

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
lem_chain_subFV x y v e@(Let w ew e')
                = () ? lem_chain_subFV x y v ew
                     ? lem_chain_subFV x y v e'
lem_chain_subFV x y v (Annot e' t)
                = () ? lem_chain_subFV x y v e'
                     ? lem_chain_tsubFV x y v t
lem_chain_subFV x y v (Crash)  = () 

{-@ lem_commute_subFV_unbind :: x:Vname -> y:Vname -> z:Vname 
        -> { z':Vname | z' != x } -> e:Expr
        -> {pf:_ | subFV x (FV y) (unbind z z' e) == unbind z z' (subFV x (FV y) e)} / [esize e] @-}
lem_commute_subFV_unbind :: Vname -> Vname -> Vname -> Vname -> Expr -> Proof
lem_commute_subFV_unbind x y z z' (Bc b)       = ()
lem_commute_subFV_unbind x y z z' (Ic n)       = ()
lem_commute_subFV_unbind x y z z' (Prim c)     = ()
lem_commute_subFV_unbind x y z z' (BV w)       
  | w == z    = ()
  | otherwise = ()
lem_commute_subFV_unbind x y z z' (FV w)       = ()
lem_commute_subFV_unbind x y z z' (Lambda w e) 
  | w == z    = ()
  | otherwise = () ? lem_commute_subFV_unbind x y z z' e
lem_commute_subFV_unbind x y z z' (App e e')     
              = () ? lem_commute_subFV_unbind x y z z' e
                   ? lem_commute_subFV_unbind x y z z' e'
lem_commute_subFV_unbind x y z z' (LambdaT a k e)
              = () ? lem_commute_subFV_unbind x y z z' e
lem_commute_subFV_unbind x y z z' (AppT e t)     
              = () ? lem_commute_subFV_unbind x y z z' e
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_subFV_unbind x y z z' (Let w ew e)     
  | w == z    = () ? lem_commute_subFV_unbind x y z z' ew
  | otherwise = () ? lem_commute_subFV_unbind x y z z' ew
                   ? lem_commute_subFV_unbind x y z z' e
lem_commute_subFV_unbind x y z z' (Annot e t)     
              = () ? lem_commute_subFV_unbind x y z z' e
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_subFV_unbind x y z z' (Crash)      = ()

{-@ lem_commute_subFV_subBV :: x:Vname -> v:Value 
        -> y:Vname -> { v_y:Value | not (Set_mem x (freeBV v_y)) } -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x (subFV y v_y v) (subFV y v_y e) } / [esize e] @-}
lem_commute_subFV_subBV :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV x v y v_y (Bc b)       = ()
lem_commute_subFV_subBV x v y v_y (Ic n)       = ()
lem_commute_subFV_subBV x v y v_y (Prim p)     = ()
lem_commute_subFV_subBV x v y v_y (BV w) 
  | x == w    = () -- ? lem_subFV_notin y v_y (BV x)
                   {- toProof ( subFV y v_y (subBV x v (BV x))
                      === subFV y v_y v
                      === subBV x (subFV y v_y v) (BV x)
                      === subBV x (subFV y v_y v) (subFV y v_y (BV x)) ) --`withProof` -}
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (FV w)       
  | y == w    = () {- toProof ( subFV y v_y (subBV x v (FV y))
                      === subFV y v_y (FV y)
                      === v_y -}
                   ? lem_subBV_notin x (subFV y v_y v) v_y
                   {- === subBV x (subFV y v_y v) v_y
                      === subBV x (subFV y v_y v) (subFV y v_y (FV y)) ) -}
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
lem_commute_subFV_subBV x v y v_y Crash        = ()


{-@ lem_commute_subFV_subBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> { v_y:Value | not (Set_mem x (freeBV v_y)) } -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x v (subFV y v_y e) } @-}
lem_commute_subFV_subBV1 :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV1 x v y v_y e = lem_commute_subFV_subBV x v y v_y e 
                                           ? lem_subFV_notin y v_y v 
                                           -- ? toProof ( subFV y v_y v === v )

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
                   {- ? toProof ( subFV y v_y (subFV x v (FV y))
                           === subFV y v_y (FV y)
                           === v_y 
                           === subFV x (subFV y v_y v) v_y
                           === subFV x (subFV y v_y v) (subFV y v_y (FV y)) ) -}
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
lem_commute_subFV x v y v_y Crash        = ()

{-@ lem_tsubBV_notin :: x:Vname -> v_x:Value -> { t:Type | not (Set_mem x (tfreeBV t)) }
                -> { pf:_ | tsubBV x v_x t == t } / [tsize t] @-} 
lem_tsubBV_notin :: Vname -> Expr -> Type -> Proof
lem_tsubBV_notin x v_x (TRefn b y r)       
    | x == y    = ()
    | otherwise = () ? lem_subBV_notin x v_x r
lem_tsubBV_notin x v_x (BTV a) = ()
lem_tsubBV_notin x v_x (FTV a) = ()
lem_tsubBV_notin x v_x (TFunc z t_z t)       
    | x == z    = () ? lem_tsubBV_notin x v_x t_z
    | otherwise = () ? lem_tsubBV_notin x v_x t_z
                     ? lem_tsubBV_notin x v_x t
lem_tsubBV_notin x v_x (TExists z t_z t)       
    | x == z    = () ? lem_tsubBV_notin x v_x t_z
    | otherwise = () ? lem_tsubBV_notin x v_x t_z
                     ? lem_tsubBV_notin x v_x t
lem_tsubBV_notin x v_x (TPoly a k t) = () ? lem_tsubBV_notin x v_x t
--    | x == a    = ()
--    | otherwise = () ? lem_tsubBV_inval x v_x t

{-@ lem_tsubFV_unbindT :: x:Vname -> y:Vname -> v:Value 
        -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | tsubBV x v t == tsubFV y v (unbindT x y t) } / [tsize t] @-}
lem_tsubFV_unbindT :: Vname -> Vname -> Expr -> Type -> Proof
lem_tsubFV_unbindT x y v t@(TRefn b w p)     
  | x == w     = () ? lem_subFV_notin y v p
                    {- toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TRefn b w p)
                       === TRefn b w (subFV y v p)
                       === TRefn b w p 
                       === tsubBV x v (TRefn b w p) ) -}
  | otherwise  = () ? lem_subFV_unbind x y v p
lem_tsubFV_unbindT x y v (BTV a) = ()
lem_tsubFV_unbindT x y v (FTV a) = ()
lem_tsubFV_unbindT x y v t@(TFunc w t_w t')
  | x == w     = () {- toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TFunc w (unbindT x y t_w) t')
                       === TFunc w (tsubFV y v (unbindT x y t_w)) (tsubFV y v t') -}
                         ? lem_tsubFV_unbindT x y v t_w
                         ? lem_tsubFV_notin y v t'
                    {-   === TFunc w (tsubBV x v t_w) (tsubFV y v t')
                       === TFunc w (tsubBV x v t_w) t'
                       === tsubBV x v (TFunc w t_w t') ) -}
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w 
                    ? lem_tsubFV_unbindT x y v t' 
lem_tsubFV_unbindT x y v t@(TExists w t_w t') 
  | x == w     = () {- toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TExists w (unbindT x y t_w) t')
                       === TExists w (tsubFV y v (unbindT x y t_w)) (tsubFV y v t') -}
                         ? lem_tsubFV_unbindT x y v t_w 
                         ? lem_tsubFV_notin y v t'
                    {- === TExists w (tsubBV x v t_w) (tsubFV y v t')
                       === TExists w (tsubBV x v t_w) t'
                       === tsubBV x v (TExists w t_w t') ) -}
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w
                    ? lem_tsubFV_unbindT x y v t'
lem_tsubFV_unbindT x y v t@(TPoly a k t') = () ? lem_tsubFV_unbindT x y v t'

{-@ lem_tsubFV_id :: x:Vname -> t:Type -> { pf:_ | tsubFV x (FV x) t == t } / [tsize t] @-}
lem_tsubFV_id :: Vname -> Type -> Proof
lem_tsubFV_id x t@(TRefn b w p)      = () ? lem_subFV_id x p
lem_tsubFV_id x (BTV a)              = ()
lem_tsubFV_id x (FTV a)              = ()
lem_tsubFV_id x t@(TFunc w t_w t')   = () ? lem_tsubFV_id x t_w
                                          ? lem_tsubFV_id x t'
lem_tsubFV_id x t@(TExists w t_w t') = () ? lem_tsubFV_id x t_w
                                          ? lem_tsubFV_id x t'
lem_tsubFV_id x t@(TPoly a k t')     = () ? lem_tsubFV_id x t'

{-@ lem_tsubFV_notin :: x:Vname -> v:Value -> { t:Type | not (Set_mem x (free t)) } 
                               -> { pf:_ | tsubFV x v t == t } / [tsize t] @-}
lem_tsubFV_notin :: Vname -> Expr -> Type -> Proof
lem_tsubFV_notin x v t@(TRefn b w p)      = () ? lem_subFV_notin x v p
lem_tsubFV_notin x v (BTV a)              = ()
lem_tsubFV_notin x v (FTV a)              = ()
lem_tsubFV_notin x v t@(TFunc w t_w t')   = () ? lem_tsubFV_notin x v t_w
                                               ? lem_tsubFV_notin x v t'
lem_tsubFV_notin x v t@(TExists w t_w t') = () ? lem_tsubFV_notin x v t_w
                                               ? lem_tsubFV_notin x v t'
lem_tsubFV_notin x v t@(TPoly a k t')     = () ? lem_tsubFV_notin x v t'

{-@ lem_chain_tsubFV :: x:Vname -> y:Vname -> v:Value 
        -> { t:Type | x == y || not (Set_mem y (free t)) }
        -> { pf:_ | tsubFV x v t == tsubFV y v (tsubFV x (FV y) t) } / [tsize t] @-}
lem_chain_tsubFV :: Vname -> Vname -> Expr -> Type -> Proof
lem_chain_tsubFV x y v t@(TRefn b w p)     
               = () ? lem_chain_subFV x y v p
lem_chain_tsubFV x y v (BTV a) = ()
lem_chain_tsubFV x y v (FTV a) = ()
lem_chain_tsubFV x y v t@(TFunc w t_w t')
               = () ? lem_chain_tsubFV x y v t_w 
                    ? lem_chain_tsubFV x y v t' 
lem_chain_tsubFV x y v t@(TExists w t_w t') 
               = () ? lem_chain_tsubFV x y v t_w
                    ? lem_chain_tsubFV x y v t'
lem_chain_tsubFV x y v (TPoly a k t) = () ? lem_chain_tsubFV x y v t

{-@ lem_commute_tsubFV_unbindT :: x:Vname -> y:Vname -> z:Vname 
        -> { z':Vname | z' != x } -> t:Type
        -> {pf:_ | tsubFV x (FV y) (unbindT z z' t) == unbindT z z' (tsubFV x (FV y) t)} / [tsize t] @-}
lem_commute_tsubFV_unbindT :: Vname -> Vname -> Vname -> Vname -> Type -> Proof
lem_commute_tsubFV_unbindT x y z z' (TRefn b w p)
  | z == w    = ()
  | otherwise = () ? lem_commute_subFV_unbind x y z z' p
lem_commute_tsubFV_unbindT x y z z' (BTV a) = ()
lem_commute_tsubFV_unbindT x y z z' (FTV a) = ()
lem_commute_tsubFV_unbindT x y z z' (TFunc w t_w t)
  | z == w    = () ? lem_commute_tsubFV_unbindT x y z z' t_w
  | otherwise = () ? lem_commute_tsubFV_unbindT x y z z' t_w
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_tsubFV_unbindT x y z z' (TExists w t_w t)
  | z == w    = () ? lem_commute_tsubFV_unbindT x y z z' t_w
  | otherwise = () ? lem_commute_tsubFV_unbindT x y z z' t_w
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_tsubFV_unbindT x y z z' (TPoly a k t)
              = () ? lem_commute_tsubFV_unbindT x y z z' t

{-@ lem_commute_tsubFV_tsubBV :: x:Vname -> v:Value 
        -> y:Vname -> { v_y:Value | not (Set_mem x (freeBV v_y)) }  -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x (subFV y v_y v) (tsubFV y v_y t) } / [tsize t] @-}
lem_commute_tsubFV_tsubBV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV x v y v_y (TRefn b w p)
  | x == w    = ()
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y p
lem_commute_tsubFV_tsubBV x v y v_y (BTV a) = ()
lem_commute_tsubFV_tsubBV x v y v_y (FTV a) = ()
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
                                             -- ? toProof (subFV y v_y v === v )

{-@ lem_commute_tsubFV :: x:Vname -> v:Value -> { y:Vname | not ( y == x ) } 
        -> { v_y:Value | not (Set_mem x (fv v_y)) } -> t:Type 
        -> { pf:_ | tsubFV y v_y (tsubFV x v t) 
                 == tsubFV x (subFV y v_y v) (tsubFV y v_y t) } / [tsize t] @-}
lem_commute_tsubFV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV x v y v_y (TRefn b w p)     = () ? lem_commute_subFV x v y v_y p
lem_commute_tsubFV x v y v_y (BTV a)           = ()
lem_commute_tsubFV x v y v_y (FTV a)           = ()
lem_commute_tsubFV x v y v_y (TFunc w t_w t)   = () ? lem_commute_tsubFV x v y v_y t_w
                                                    ? lem_commute_tsubFV x v y v_y t
lem_commute_tsubFV x v y v_y (TExists w t_w t) = () ? lem_commute_tsubFV x v y v_y t_w
                                                    ? lem_commute_tsubFV x v y v_y t
lem_commute_tsubFV x v y v_y (TPoly a k t)     = () ? lem_commute_tsubFV x v y v_y t

