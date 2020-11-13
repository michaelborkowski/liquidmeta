{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SameBinders where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

  --- DEFINITIONS

{-@ reflect refn_binders @-} -- all of the "binders" are term variable binders only
{-@ refn_binders :: e:Expr -> S.Set Vname / [esize e] @-}
refn_binders :: Expr -> S.Set Vname
refn_binders (Lambda x e)    = refn_binders e
refn_binders (App e e')      = S.union (refn_binders e)   (refn_binders e')
refn_binders (LambdaT a k e) = refn_binders e
refn_binders (AppT e t)      = S.union (refn_binders e)   (refn_bindersT t)
refn_binders (Let x e_x e)   = S.union (refn_binders e_x) (refn_binders e)
refn_binders (Annot e t)     = S.union (refn_binders e)   (refn_bindersT t)
refn_binders _               = S.empty

{-@ reflect refn_bindersT @-}
{-@ refn_bindersT :: t:Type -> S.Set Vname / [tsize t] @-}
refn_bindersT :: Type -> S.Set Vname
refn_bindersT (TRefn b' x' p')   = S.union (S.singleton x')    (refn_binders p')
refn_bindersT (TFunc x t_x t')   = S.union (refn_bindersT t_x) (refn_bindersT t')
refn_bindersT (TExists x t_x t') = S.union (refn_bindersT t_x) (refn_bindersT t')
refn_bindersT (TPoly a k   t')   = refn_bindersT t'

{-@ reflect binders_are @-}
binders_are :: Type -> Vname -> Bool
binders_are (TRefn b x p)     x' =  x == x'
binders_are (TFunc   x t_x t) x' = binders_are t_x x' && binders_are t x'
binders_are (TExists x t_x t) x' = binders_are t_x x' && binders_are t x'
binders_are (TPoly   a k   t) x' = binders_are t x'

{-@ reflect same_binders @-}
{-@ same_binders :: t_a:Type -> t:Type -> Bool / [tsize t_a, tsize t] @-}
same_binders :: Type -> Type -> Bool
same_binders t_a (TFunc   x t_x t')
  = same_binders t_a t_x && same_binders t_a t'
same_binders t_a (TExists x t_x t')
  = same_binders t_a t_x && same_binders t_a t'
same_binders t_a (TPoly   a k   t')
  = same_binders t_a t'
same_binders t_a (TRefn b' x' p')
  = binders_are t_a x' && same_bindersE t_a p'

{-@ reflect same_bindersE @-}
{-@ same_bindersE :: t_a:Type -> e:Expr -> Bool / [tsize t_a, esize e] @-}
same_bindersE :: Type -> Expr -> Bool
same_bindersE t_a (Lambda x e)    = same_bindersE t_a e
same_bindersE t_a (App e e')      = same_bindersE t_a e && same_bindersE t_a e'
same_bindersE t_a (LambdaT a k e) = same_bindersE t_a e
same_bindersE t_a (AppT e t)      = same_bindersE t_a e && same_binders t_a t
same_bindersE t_a (Let x e_x e)   = same_bindersE t_a e_x && same_bindersE t_a e
same_bindersE t_a (Annot e t)     = same_bindersE t_a e && same_binders t_a t
same_bindersE t_a _               = True

{-@ reflect same_bindersEE @-}
{-@ same_bindersEE :: v:Expr -> e:Expr -> Bool / [esize e] @-}
same_bindersEE :: Expr -> Expr -> Bool
same_bindersEE v (Lambda x e')    = same_bindersEE v e' 
same_bindersEE v (App e1 e2)      = same_bindersEE v e1  && same_bindersEE v  e2
same_bindersEE v (LambdaT a k e') = same_bindersEE v e' 
same_bindersEE v (AppT e' t)      = same_bindersEE v e'  && same_bindersE  t  v
same_bindersEE v (Let x e_x e')   = same_bindersEE v e_x && same_bindersEE v  e' 
same_bindersEE v (Annot e' t)     = same_bindersEE v e'  && same_bindersE  t  v
same_bindersEE v  _               = True

{-@ reflect same_binders_env @-}
{-@ same_binders_env :: t_a:Type -> g:Env -> Bool @-}
same_binders_env :: Type -> Env -> Bool
same_binders_env t_a Empty          = True
same_binders_env t_a (Cons x t_x g) = same_binders t_a t_x && same_binders_env t_a g
same_binders_env t_a (ConsT a k  g) = same_binders_env t_a g

  --- PROPERTIES

{-@ lem_same_binders_refl :: t_a:Type -> { t:Type | same_binders t_a t } 
        -> { pf:_ | same_binders t_a t_a && same_binders t t } @-}
lem_same_binders_refl :: Type -> Type -> Proof
lem_same_binders_refl t_a t = undefined {- 2 -}

{-@ lem_same_binders_commute :: t:Type ->  t':Type  
        -> { pf:_ | (same_binders t t' => same_binders t' t) 
                 && (same_binders t' t => same_binders t t') } / [tsize t + tsize t'] @-}
lem_same_binders_commute :: Type -> Type -> Proof
lem_same_binders_commute (TRefn b' x' p')   (TRefn   b   y q) = undefined
lem_same_binders_commute (TRefn b' x' p')   (TFunc   y t_y t) = undefined
lem_same_binders_commute (TRefn b' x' p')   (TExists y t_y t) = undefined
lem_same_binders_commute (TRefn b' x' p')   (TPoly   a   k t) = undefined
lem_same_binders_commute (TFunc   x t_x t') (TRefn   b   y q) = undefined
lem_same_binders_commute (TFunc   x t_x t') (TFunc   y t_y t) = undefined {-
  = () ? lem_same_binders_commute (TFunc   x t_x t') t_y 
       ? lem_same_binders_commute (TFunc   x t_x t') t 
--       ? lem_same_binders_commute t_y t' 
--       ? lem_same_binders_commute t   t' -}
lem_same_binders_commute (TFunc   x t_x t') (TExists y t_y t) = undefined {-
  = () ? lem_same_binders_commute t_y t_x 
       ? lem_same_binders_commute t   t_x 
       ? lem_same_binders_commute t_y t' 
       ? lem_same_binders_commute t   t' -}
lem_same_binders_commute (TFunc   x t_x t') (TPoly   a   k t) = undefined {-
  = () ? lem_same_binders_commute t t_x 
       ? lem_same_binders_commute t t'  -}
lem_same_binders_commute (TExists x t_x t') (TRefn   b   y q) = undefined 
lem_same_binders_commute (TExists x t_x t') (TFunc   y t_y t) = undefined {-
  = () ? lem_same_binders_commute t_y t_x 
       ? lem_same_binders_commute t   t_x 
       ? lem_same_binders_commute t_y t' 
       ? lem_same_binders_commute t   t' -}
lem_same_binders_commute (TExists x t_x t') (TExists y t_y t) = undefined {-
  = () ? lem_same_binders_commute t_y t_x 
       ? lem_same_binders_commute t   t_x 
       ? lem_same_binders_commute t_y t' 
       ? lem_same_binders_commute t   t' -}
lem_same_binders_commute (TExists x t_x t') (TPoly   a   k t) = undefined {-
  = () ? lem_same_binders_commute t t_x
       ? lem_same_binders_commute t t' -}
lem_same_binders_commute (TPoly   a' k' t') (TRefn   b   y q) = undefined
lem_same_binders_commute (TPoly   a' k' t') (TFunc   y t_y t) = undefined {-
  = () ? lem_same_binders_commute t_y t' 
       ? lem_same_binders_commute t   t'-}
lem_same_binders_commute (TPoly   a' k' t') (TExists y t_y t) = undefined {-
  = () ? lem_same_binders_commute t_y t' 
       ? lem_same_binders_commute t   t' -}
lem_same_binders_commute (TPoly   a' k' t') (TPoly   a   k t) = undefined {-
  = () ? lem_same_binders_commute t   t' -}

{-@ lem_same_binders_toBare :: t_a:Type -> t:Type 
        -> { pf:_ | same_binders t_a t => same_binders (toBare t_a) t } @-}
lem_same_binders_toBare :: Type -> Type -> Proof
lem_same_binders_toBare t_a t = () ? lem_same_binders_commute t_a t
                                   ? lem_same_binders_toBare' t t_a
                                   ? lem_same_binders_commute (toBare t_a) t
 
{-@ lem_same_binders_toBare' :: t:Type -> t':Type 
        -> { pf:_ | same_binders t t' => same_binders t (toBare t') } @-}
lem_same_binders_toBare' :: Type -> Type -> Proof
lem_same_binders_toBare' t (TRefn b x p)      = ()
lem_same_binders_toBare' t (TFunc   x t_x t') = () ? lem_same_binders_toBare' t t_x
                                                   ? lem_same_binders_toBare' t t'
lem_same_binders_toBare' t (TExists x t_x t') = () ? lem_same_binders_toBare' t t_x
                                                   ? lem_same_binders_toBare' t t'
lem_same_binders_toBare' t (TPoly   a  k  t') = () ? lem_same_binders_toBare' t t'

{-@ lem_same_bindersE_subBV :: t:Type -> x:Vname -> { v:Value | same_bindersE t v}
        -> { e:Expr | same_bindersE t e } -> { pf:_ | same_bindersE t (subBV x v e) } / [esize e] @-}
lem_same_bindersE_subBV  :: Type -> Vname -> Expr -> Expr -> Proof
lem_same_bindersE_subBV t x v (Bc b)              = () 
lem_same_bindersE_subBV t x v (Ic n)              = () 
lem_same_bindersE_subBV t x v (Prim p)            = () 
lem_same_bindersE_subBV t x v (BV y) | x == y     = () 
                                     | otherwise  = ()
lem_same_bindersE_subBV t x v (FV y)              = () 
lem_same_bindersE_subBV t x v (Lambda y e) 
  | x == y     = () -- Lambda y e 
  | otherwise  = () ? lem_same_bindersE_subBV t x v e --Lambda y (subBV x v e)
lem_same_bindersE_subBV t x v (App e e')          
  = () ? lem_same_bindersE_subBV t x v e
       ? lem_same_bindersE_subBV t x v e' -- App   (subBV x v_x e)  (subBV x v_x e')
lem_same_bindersE_subBV t x v (LambdaT a k e)           
  = () ? lem_same_bindersE_subBV t x v e -- LambdaT a k (subBV x v_x e) 
lem_same_bindersE_subBV t x v (AppT e t')          
  = () ? lem_same_bindersE_subBV t x v e 
       ? lem_same_binders_tsubBV t x v t' --AppT  (subBV x v_x e) (tsubBV x v_x t)
lem_same_bindersE_subBV t x v (Let y e1 e2) 
  | x == y    = () ? lem_same_bindersE_subBV t x v e1 --Let y (subBV x v_x e1) e2
  | otherwise = () ? lem_same_bindersE_subBV t x v e1
                   ? lem_same_bindersE_subBV t x v e2 --Let y (subBV x v_x e1) (subBV x v_x e2)
lem_same_bindersE_subBV t x v (Annot e t')   
  = () ? lem_same_bindersE_subBV t x v e
       ? lem_same_binders_tsubBV t x v t' --Annot (subBV x v_x e) (tsubBV x v_x t)
lem_same_bindersE_subBV t x v Crash               = ()

{-@ lem_same_binders_tsubBV :: t_a:Type -> x:Vname -> { v:Value | same_bindersE t_a v }
        -> { t:Type | same_binders t_a t} -> { pf:_ | same_binders t_a (tsubBV x v t) } / [tsize t] @-}
lem_same_binders_tsubBV :: Type -> Vname -> Expr -> Type -> Proof
lem_same_binders_tsubBV t_a x v (TRefn b y r)     
  | x == y                     = ()
  | otherwise                  = () ? lem_same_bindersE_subBV t_a x v r 
lem_same_binders_tsubBV t_a x v (TFunc z t_z t)   
  | x == z                     = () ? lem_same_binders_tsubBV t_a x v t_z 
  | otherwise                  = () ? lem_same_binders_tsubBV t_a x v t_z
                                    ? lem_same_binders_tsubBV t_a x v t 
lem_same_binders_tsubBV t_a x v (TExists z t_z t) 
  | x == z                     = () ? lem_same_binders_tsubBV t_a x v t_z 
  | otherwise                  = () ? lem_same_binders_tsubBV t_a x v t_z
                                    ? lem_same_binders_tsubBV t_a x v t
lem_same_binders_tsubBV t_a x v (TPoly a  k  t)   
                               = () ? lem_same_binders_tsubBV t_a x v t

{-@ lem_same_bindersE_subFTV :: t:Type -> a:Vname -> { t':Type | same_binders t t' }
        -> { e:Expr | same_bindersE t e } -> { pf:_ | same_bindersE t (subFTV a t' e) } / [esize e] @-}
lem_same_bindersE_subFTV :: Type -> Vname -> Type -> Expr -> Proof
lem_same_bindersE_subFTV t a t_a e         = undefined {- 2 -}

{-@ lem_same_bindersE_subBTV :: t:Type -> a:Vname -> { t':Type | same_binders t t' }
        -> { e:Expr | same_bindersE t e } -> { pf:_ | same_bindersE t (subBTV a t' e) } / [esize e] @-}
lem_same_bindersE_subBTV :: Type -> Vname -> Type -> Expr -> Proof
lem_same_bindersE_subBTV t a t_a (Bc b)         = ()
lem_same_bindersE_subBTV t a t_a (Ic n)         = ()
lem_same_bindersE_subBTV t a t_a (Prim p)       = ()
lem_same_bindersE_subBTV t a t_a (BV y)         = () 
lem_same_bindersE_subBTV t a t_a (FV y)         = () 
lem_same_bindersE_subBTV t a t_a (Lambda y e)   
  = () ? lem_same_bindersE_subBTV t a t_a e  -- Lambda y (subBTV a t_a e)
lem_same_bindersE_subBTV t a t_a (App e e')   
  = () ? lem_same_bindersE_subBTV t a t_a e
       ? lem_same_bindersE_subBTV t a t_a e' -- App   (subBTV a t_a e)  (subBTV a t_a e')
lem_same_bindersE_subBTV t a t_a (LambdaT a' k e) 
  | a == a'   = ()
  | otherwise = () ? lem_same_bindersE_subBTV t a t_a e --LambdaT a' k (subBTV a t_a e)
lem_same_bindersE_subBTV t a t_a (AppT e t')     
  = () ? lem_same_bindersE_subBTV t a t_a e  -- AppT  (subBTV a t_a e) (tsubBTV a t_a t)
       ? lem_same_binders_tsubBTV t a (toBare t_a ? lem_same_binders_toBare' t t_a) t' 
lem_same_bindersE_subBTV t a t_a (Let y e1 e2)   
  = () ? lem_same_bindersE_subBTV t a t_a e1
       ? lem_same_bindersE_subBTV t a t_a e2 -- Let y (subBTV a t_a e1) (subBTV a t_a e2)
lem_same_bindersE_subBTV t a t_a (Annot e t')    
  = () ? lem_same_bindersE_subBTV t a t_a e 
       ? lem_same_binders_tsubBTV t a t_a t' -- Annot (subBTV a t_a e) (tsubBTV a t_a t)
lem_same_bindersE_subBTV t a t_a Crash          = ()   

{-@ lem_same_bindersE_unbind_tv :: t:Type -> a:Vname -> a':Vname 
        -> { e:Expr | same_bindersE t e } -> { pf:_ | same_bindersE t (unbind_tv a a' e) } / [esize e] @-}
lem_same_bindersE_unbind_tv :: Type -> Vname -> Vname -> Expr -> Proof
lem_same_bindersE_unbind_tv t a a' (Bc b)         = ()
lem_same_bindersE_unbind_tv t a a' (Ic n)         = ()
lem_same_bindersE_unbind_tv t a a' (Prim p)       = ()
lem_same_bindersE_unbind_tv t a a' (BV y)         = () 
lem_same_bindersE_unbind_tv t a a' (FV y)         = () 
lem_same_bindersE_unbind_tv t a a' (Lambda y e)   
  = () ? lem_same_bindersE_unbind_tv t a a' e  
lem_same_bindersE_unbind_tv t a a' (App e e')   
  = () ? lem_same_bindersE_unbind_tv t a a' e
       ? lem_same_bindersE_unbind_tv t a a' e' 
lem_same_bindersE_unbind_tv t a a' (LambdaT a1 k e) 
  | a == a1   = ()
  | otherwise = () ? lem_same_bindersE_unbind_tv t a a' e 
lem_same_bindersE_unbind_tv t a a' (AppT e t')     
  = () ? lem_same_bindersE_unbind_tv t a a' e  
       ? lem_same_binders_unbind_tvT t a a' t' 
lem_same_bindersE_unbind_tv t a a' (Let y e1 e2)   
  = () ? lem_same_bindersE_unbind_tv t a a' e1
       ? lem_same_bindersE_unbind_tv t a a' e2 
lem_same_bindersE_unbind_tv t a a' (Annot e t')    
  = () ? lem_same_bindersE_unbind_tv t a a' e 
       ? lem_same_binders_unbind_tvT t a a' t' 
lem_same_bindersE_unbind_tv t a a' Crash          = ()   

{-@ lem_same_binders_tsubBTV :: t:Type -> a:Vname -> { t_a:Type | same_binders t t_a }
        -> { t':Type | same_binders t t'} -> { pf:_ | same_binders t (tsubBTV a t_a t') } / [tsize t'] @-}
lem_same_binders_tsubBTV :: Type -> Vname -> Type -> Type -> Proof
lem_same_binders_tsubBTV t a t_a (TRefn b x r)        = case b of 
  (BTV a') | a == a'  -> () ? lem_same_bindersE_push t a 
                                  (subBTV a t_a r ? lem_same_bindersE_subBTV t a t_a r) t_a 
  _                   -> () ? lem_same_bindersE_subBTV t a t_a r 
lem_same_binders_tsubBTV t a t_a (TFunc z t_z t')      
  = () ? lem_same_binders_tsubBTV t a t_a t_z 
       ? lem_same_binders_tsubBTV t a t_a t' --TFunc   z  (tsubBTV a t_a t_z) (tsubBTV a t_a t')
lem_same_binders_tsubBTV t a t_a (TExists z t_z t')    
  = () ? lem_same_binders_tsubBTV t a t_a t_z 
       ? lem_same_binders_tsubBTV t a t_a t' --TExists z  (tsubBTV a t_a t_z) (tsubBTV a t_a t')
lem_same_binders_tsubBTV t a t_a (TPoly a' k  t')    
  | a == a'            = () -- TPoly   a' k t 
  | otherwise          = () ? lem_same_binders_tsubBTV t a t_a t' --TPoly   a' k (tsubBTV a t_a t')

{-@ lem_same_binders_unbind_tvT :: t:Type -> a:Vname -> a':Vname 
        -> { t':Type | same_binders t t'} -> { pf:_ | same_binders t (unbind_tvT a a' t') } / [tsize t'] @-}
lem_same_binders_unbind_tvT :: Type -> Vname -> Vname -> Type -> Proof
lem_same_binders_unbind_tvT t a a' (TRefn b x r)        = case b of 
  (BTV a1) | a == a1  -> () ? lem_same_bindersE_unbind_tv t a a' r
  _                   -> () ? lem_same_bindersE_unbind_tv t a a' r 
lem_same_binders_unbind_tvT t a a' (TFunc z t_z t')      
  = () ? lem_same_binders_unbind_tvT t a a' t_z 
       ? lem_same_binders_unbind_tvT t a a' t'
lem_same_binders_unbind_tvT t a a' (TExists z t_z t')    
  = () ? lem_same_binders_unbind_tvT t a a' t_z 
       ? lem_same_binders_unbind_tvT t a a' t' 
lem_same_binders_unbind_tvT t a a' (TPoly a1 k  t')    
  | a == a1            = () 
  | otherwise          = () ? lem_same_binders_unbind_tvT t a a' t' 

{-@ lem_same_bindersE_push :: t:Type -> a:Vname -> { p:Pred | same_bindersE t p }
        -> { t':Type | same_binders t t'} -> { pf:_ | same_binders t (push p t') } / [tsize t'] @-}
lem_same_bindersE_push :: Type -> Vname -> Expr -> Type -> Proof
lem_same_bindersE_push t a p (TRefn   b x   r) 
  = () ? lem_same_bindersE_strengthen t p r --TRefn   b x            (strengthen p r)
lem_same_bindersE_push t a p (TFunc   y t_y t') 
  = () ? lem_same_bindersE_push t a p t_y
       ? lem_same_bindersE_push t a p t' -- TFunc   y (push p t_y) (push p t')
lem_same_bindersE_push t a p (TExists y t_y t') 
  = () ? lem_same_bindersE_push t a p t' -- TExists y t_y          (push p t')
lem_same_bindersE_push t a p (TPoly   a' k   t') 
  = () ? lem_same_bindersE_push t a p t' -- TPoly   a k            (push p t') 

{-@ lem_same_bindersE_strengthen :: t:Type -> { p:Pred | same_bindersE t p }
        -> { r:Pred | same_bindersE t r } -> { pf:_ | same_bindersE t (strengthen p r) } @-}
lem_same_bindersE_strengthen :: Type -> Expr -> Expr -> Proof
lem_same_bindersE_strengthen t p r 
  | (r == Bc True)  = ()
  | (p == Bc True)  = ()
  | otherwise       = () -- App (App (Prim And) p) r
