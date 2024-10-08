{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicProps where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

-- force these into scope for LH
semantics = (Step, EvalsTo)
typing = (HasBType, WFType, WFEnv)

{-@ reflect foo2 @-}   
foo2 x = Just x 
foo2 :: a -> Maybe a 

{-@ lem_union_subset :: a:S.Set Vname -> b:S.Set Vname 
        -> { c:S.Set Vname | Set_sub a c && Set_sub b c }
        -> { pf:_ | Set_sub (Set_cup a b) c } @-}
lem_union_subset :: S.Set Vname -> S.Set Vname -> S.Set Vname -> Proof
lem_union_subset a b c = ()

---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION
---------------------------------------------------------------------------

-- Lemmas. The set of Values is closed under substitution.
{-@ lem_subFV_value :: y:Vname -> v_y:Value -> v:Value  
                        -> { pf:_ | isValue (subFV y v_y v) && Set_emp (freeBV (subFV y v_y v)) } @-}
lem_subFV_value :: Vname -> Expr -> Expr -> Proof
lem_subFV_value y v_y (Bc _)       = ()
lem_subFV_value y v_y (Ic _)       = ()
lem_subFV_value y v_y (Prim _)     = ()
lem_subFV_value y v_y (FV x) 
    | x == y    = toProof ( subFV y v_y (FV x) === v_y ) 
    | otherwise = toProof ( subFV y v_y (FV x) === FV x)
lem_subFV_value y v_y (Lambda x e) 
    | x == y    = toProof ( subFV y v_y (Lambda x e) === Lambda x (subFV y v_y e) )
    | otherwise = toProof ( freeBV (subFV y v_y (Lambda x e))
                        === freeBV (Lambda x (subFV y v_y e))
                        === S.difference (freeBV (subFV y v_y e)) (S.singleton x)
                        === S.empty ) 
lem_subFV_value y v_y Crash        = ()  

{-@ lem_subBV_value :: x:Vname -> v_x:Value -> { v:Expr | not (Set_mem x (freeBV v)) }
                -> { pf:_ | subBV x v_x v == v } / [esize v] @-} 
lem_subBV_value :: Vname -> Expr -> Expr -> Proof
lem_subBV_value x v_x (Bc _)       = ()
lem_subBV_value x v_x (Ic _)       = ()
lem_subBV_value x v_x (Prim _)     = ()
lem_subBV_value x v_x (BV w)       = ()
lem_subBV_value x v_x (FV _)       = ()
lem_subBV_value x v_x (Lambda w e)
    | x == w    = ()
    | otherwise = () ? lem_subBV_value x v_x e
lem_subBV_value x v_x (App e e')   = () ? lem_subBV_value x v_x e 
                                        ? lem_subBV_value x v_x e'
lem_subBV_value x v_x (Let w ew e)
    | x == w    = () ? lem_subBV_value x v_x ew
    | otherwise = () ? lem_subBV_value x v_x ew
                     ? lem_subBV_value x v_x e
lem_subBV_value x v_x (Annot e t)  = () ? lem_subBV_value x v_x e
                                        ? lem_tsubBV_inval x v_x t  
lem_subBV_value x v_x Crash        = ()

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
    | x == w    = toProof ( subFV y v (unbind x y e)
                        === subFV y v (Lambda w e')
                        === Lambda w (subFV y v e')
                        === Lambda w e'
                        === subBV x v (Lambda w e') ) 
    | otherwise = () ? lem_subFV_unbind x y v e'
lem_subFV_unbind x y v (App e1 e2) 
                = () ? lem_subFV_unbind x y v e1
                     ? lem_subFV_unbind x y v e2
lem_subFV_unbind x y v e@(Let w ew e')
    | x == w    = () ? lem_subFV_unbind x y v ew
                     ? toProof ( subFV y v e' === e' )
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
lem_subFV_id x (FV w)   
    | x == w    = ()
    | otherwise = ()
lem_subFV_id x e@(Lambda w e') 
                = () ? lem_subFV_id x e'
lem_subFV_id x (App e1 e2) 
                = () ? lem_subFV_id x e1
                     ? lem_subFV_id x e2
lem_subFV_id x e@(Let w ew e')
                = () ? lem_subFV_id x ew
                     ? lem_subFV_id x e'
lem_subFV_id x (Annot e' t)
                = () ? lem_subFV_id x e'
                     ? lem_tsubFV_id x t
lem_subFV_id x (Crash)  = () 

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
lem_chain_subFV x y v e@(Lambda w e') 
                = () ? lem_chain_subFV x y v e'
lem_chain_subFV x y v (App e1 e2) 
                = () ? lem_chain_subFV x y v e1
                     ? lem_chain_subFV x y v e2
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
lem_commute_subFV_unbind x y z z' (Let w ew e)     
  | w == z    = () ? lem_commute_subFV_unbind x y z z' ew
  | otherwise = () ? lem_commute_subFV_unbind x y z z' ew
                   ? lem_commute_subFV_unbind x y z z' e
lem_commute_subFV_unbind x y z z' (Annot e t)     
              = () ? lem_commute_subFV_unbind x y z z' e
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_subFV_unbind x y z z' (Crash)      = ()

{-@ lem_commute_subFV_subBV :: x:Vname -> v:Value -> y:Vname ->  v_y:Value -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x (subFV y v_y v) (subFV y v_y e) } / [esize e] @-}
lem_commute_subFV_subBV :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV x v y v_y (Bc b)       = ()
lem_commute_subFV_subBV x v y v_y (Ic n)       = ()
lem_commute_subFV_subBV x v y v_y (Prim p)     = ()
lem_commute_subFV_subBV x v y v_y (BV w) 
  | x == w    = toProof ( subFV y v_y (subBV x v (BV x))
                      === subFV y v_y v
                      === subBV x (subFV y v_y v) (BV x)
                      === subBV x (subFV y v_y v) (subFV y v_y (BV x)) ) --`withProof`
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (FV w)       
  | y == w    = toProof ( subFV y v_y (subBV x v (FV y))
                      === subFV y v_y (FV y)
                      === v_y ? lem_subBV_value x (subFV y v_y v) v_y
                      === subBV x (subFV y v_y v) v_y
                      === subBV x (subFV y v_y v) (subFV y v_y (FV y)) )
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (Lambda w e)
  | x == w    = () 
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (App e e')
              = () ? lem_commute_subFV_subBV x v y v_y e
                   ? lem_commute_subFV_subBV x v y v_y e'
lem_commute_subFV_subBV x v y v_y (Let w ew e)
  | x == w    = () ? lem_commute_subFV_subBV x v y v_y ew
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y ew
                   ? lem_commute_subFV_subBV x v y v_y e
lem_commute_subFV_subBV x v y v_y (Annot e t)
              = () ? lem_commute_subFV_subBV   x v y v_y e
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_subFV_subBV x v y v_y Crash        = ()


{-@ lem_commute_subFV_subBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> v_y:Value -> e:Expr
        -> { pf:_ | subFV y v_y (subBV x v e) == subBV x v (subFV y v_y e) } @-}
lem_commute_subFV_subBV1 :: Vname -> Expr -> Vname -> Expr -> Expr -> Proof
lem_commute_subFV_subBV1 x v y v_y e = lem_commute_subFV_subBV x v y v_y e 
                                           ? toProof ( subFV y v_y v === v )

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
  | y == w    = () ? toProof ( subFV y v_y (subFV x v (FV y))
                           === subFV y v_y (FV y)
                           === v_y 
                           === subFV x (subFV y v_y v) v_y
                           === subFV x (subFV y v_y v) (subFV y v_y (FV y)) )
  | otherwise = ()
lem_commute_subFV x v y v_y (Lambda w e)
              = () ? lem_commute_subFV x v y v_y e
lem_commute_subFV x v y v_y (App e e')
              = () ? lem_commute_subFV x v y v_y e
                   ? lem_commute_subFV x v y v_y e'
lem_commute_subFV x v y v_y (Let w ew e)
              = () ? lem_commute_subFV x v y v_y ew
                   ? lem_commute_subFV x v y v_y e
lem_commute_subFV x v y v_y (Annot e t)
              = () ? lem_commute_subFV x v y v_y e
                   ? lem_commute_tsubFV x v y v_y t
lem_commute_subFV x v y v_y Crash        = ()

{-@ lem_tsubBV_inval :: x:Vname -> v_x:Value -> { t:Type | not (Set_mem x (tfreeBV t)) }
                -> { pf:_ | tsubBV x v_x t == t } / [tsize t] @-} 
lem_tsubBV_inval :: Vname -> Expr -> Type -> Proof
lem_tsubBV_inval x v_x (TRefn b y r)       
    | x == y    = ()
    | otherwise = () ? lem_subBV_value x v_x r
lem_tsubBV_inval x v_x (TFunc z t_z t)       
    | x == z    = () ? lem_tsubBV_inval x v_x t_z
    | otherwise = () ? lem_tsubBV_inval x v_x t_z
                     ? lem_tsubBV_inval x v_x t
lem_tsubBV_inval x v_x (TExists z t_z t)       
    | x == z    = () ? lem_tsubBV_inval x v_x t_z
    | otherwise = () ? lem_tsubBV_inval x v_x t_z
                     ? lem_tsubBV_inval x v_x t

{-@ lem_tsubFV_unbindT :: x:Vname -> y:Vname -> v:Value 
        -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | tsubBV x v t == tsubFV y v (unbindT x y t) } / [tsize t] @-}
lem_tsubFV_unbindT :: Vname -> Vname -> Expr -> Type -> Proof
lem_tsubFV_unbindT x y v t@(TRefn b w p)     
  | x == w     = toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TRefn b w p)
                       === TRefn b w (subFV y v p)
                       === TRefn b w p 
                       === tsubBV x v (TRefn b w p) )
  | otherwise  = () ? lem_subFV_unbind x y v p
lem_tsubFV_unbindT x y v t@(TFunc w t_w t')
  | x == w     = toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TFunc w (unbindT x y t_w) t')
                       === TFunc w (tsubFV y v (unbindT x y t_w)) (tsubFV y v t')
                         ? lem_tsubFV_unbindT x y v t_w
                       === TFunc w (tsubBV x v t_w) (tsubFV y v t')
                       === TFunc w (tsubBV x v t_w) t'
                       === tsubBV x v (TFunc w t_w t') )
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w 
                    ? lem_tsubFV_unbindT x y v t' 
lem_tsubFV_unbindT x y v t@(TExists w t_w t') 
  | x == w     = toProof ( tsubFV y v (unbindT x y t)
                       === tsubFV y v (TExists w (unbindT x y t_w) t')
                       === TExists w (tsubFV y v (unbindT x y t_w)) (tsubFV y v t')
                         ? lem_tsubFV_unbindT x y v t_w 
                       === TExists w (tsubBV x v t_w) (tsubFV y v t')
                       === TExists w (tsubBV x v t_w) t'
                       === tsubBV x v (TExists w t_w t') )
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w
                    ? lem_tsubFV_unbindT x y v t'

{-@ lem_tsubFV_id :: x:Vname -> t:Type -> { pf:_ | tsubFV x (FV x) t == t } / [tsize t] @-}
lem_tsubFV_id :: Vname -> Type -> Proof
lem_tsubFV_id x t@(TRefn b w p)
               = () ? lem_subFV_id x p
lem_tsubFV_id x t@(TFunc w t_w t')
               = () ? lem_tsubFV_id x t_w
                    ? lem_tsubFV_id x t'
lem_tsubFV_id x t@(TExists w t_w t')
               = () ? lem_tsubFV_id x t_w
                    ? lem_tsubFV_id x t'

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

{-@ lem_commute_tsubFV_unbindT :: x:Vname -> y:Vname -> z:Vname 
        -> { z':Vname | z' != x } -> t:Type
        -> {pf:_ | tsubFV x (FV y) (unbindT z z' t) == unbindT z z' (tsubFV x (FV y) t)} / [tsize t] @-}
lem_commute_tsubFV_unbindT :: Vname -> Vname -> Vname -> Vname -> Type -> Proof
lem_commute_tsubFV_unbindT x y z z' (TRefn b w p)
  | z == w    = ()
  | otherwise = () ? lem_commute_subFV_unbind x y z z' p
lem_commute_tsubFV_unbindT x y z z' (TFunc w t_w t)
  | z == w    = () ? lem_commute_tsubFV_unbindT x y z z' t_w
  | otherwise = () ? lem_commute_tsubFV_unbindT x y z z' t_w
                   ? lem_commute_tsubFV_unbindT x y z z' t
lem_commute_tsubFV_unbindT x y z z' (TExists w t_w t)
  | z == w    = () ? lem_commute_tsubFV_unbindT x y z z' t_w
  | otherwise = () ? lem_commute_tsubFV_unbindT x y z z' t_w
                   ? lem_commute_tsubFV_unbindT x y z z' t

{-@ lem_commute_tsubFV_tsubBV :: x:Vname -> v:Value -> y:Vname -> v_y:Value  -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x (subFV y v_y v) (tsubFV y v_y t) } / [tsize t] @-}
lem_commute_tsubFV_tsubBV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV x v y v_y (TRefn b w p)
  | x == w    = ()
  | otherwise = () ? lem_commute_subFV_subBV x v y v_y p
lem_commute_tsubFV_tsubBV x v y v_y (TFunc w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV x v y v_y t
lem_commute_tsubFV_tsubBV x v y v_y (TExists w t_w t)
  | x == w    = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
  | otherwise = () ? lem_commute_tsubFV_tsubBV x v y v_y t_w
                   ? lem_commute_tsubFV_tsubBV x v y v_y t

{-@ lem_commute_tsubFV_tsubBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> v_y:Value -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x v (tsubFV y v_y t) } @-}
lem_commute_tsubFV_tsubBV1 :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV1 x v y v_y t = lem_commute_tsubFV_tsubBV x v y v_y t
                                             ? toProof (subFV y v_y v === v )

{-@ lem_commute_tsubFV :: x:Vname -> v:Value -> { y:Vname | not ( y == x ) } 
        -> { v_y:Value | not (Set_mem x (fv v_y)) } -> t:Type 
        -> { pf:_ | tsubFV y v_y (tsubFV x v t) 
                 == tsubFV x (subFV y v_y v) (tsubFV y v_y t) } / [tsize t] @-}
lem_commute_tsubFV :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV x v y v_y (TRefn b w p)
              = () ? lem_commute_subFV x v y v_y p
lem_commute_tsubFV x v y v_y (TFunc w t_w t)
              = () ? lem_commute_tsubFV x v y v_y t_w
                   ? lem_commute_tsubFV x v y v_y t
lem_commute_tsubFV x v y v_y (TExists w t_w t)
              = () ? lem_commute_tsubFV x v y v_y t_w
                   ? lem_commute_tsubFV x v y v_y t

----------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of ENVIRONMENTS / BARE-TYPED ENVIRONMENTS
----------------------------------------------------------------------------

{-@ reflect concatE @-}
{-@ concatE :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
                     -> { h:Env | (binds h) == (Set_cup (binds g) (binds g')) } @-}
concatE :: Env -> Env -> Env
concatE g Empty         = g
concatE g (Cons x t g') = Cons x t (concatE g g')

{-@ lem_empty_concatE :: g:Env -> { pf:_ | concatE Empty g == g } @-}
lem_empty_concatE :: Env -> Proof
lem_empty_concatE Empty        = ()
lem_empty_concatE (Cons x t g) = () ? lem_empty_concatE g

{-@ lem_in_env_concat :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
    ->  x:Vname -> {pf:_ | (in_env x (concatE g g')) <=> ((in_env x g) || (in_env x g'))} @-}
lem_in_env_concat :: Env -> Env -> Vname -> Proof
lem_in_env_concat g Empty         x = ()
lem_in_env_concat g (Cons y s g') x = () ? lem_in_env_concat g g' x 

{-@ lem_erase_tsubFV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubFV x e t) == erase t } @-}
lem_erase_tsubFV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubFV x e (TRefn   b   z p) = ()
lem_erase_tsubFV x e (TFunc   z t_z t) = () ? lem_erase_tsubFV x e t_z
                                            ? lem_erase_tsubFV x e t
lem_erase_tsubFV x e (TExists z t_z t) = () ? lem_erase_tsubFV x e t

{-@ lem_erase_tsubBV :: x:Vname -> e:Expr -> t:Type 
                                -> { pf:_ | erase (tsubBV x e t) == erase t } @-}
lem_erase_tsubBV :: Vname -> Expr -> Type -> Proof
lem_erase_tsubBV x e (TRefn   b   z p) = ()
lem_erase_tsubBV x e (TFunc   z t_z t) = () ? lem_erase_tsubBV x e t_z
                                            ? lem_erase_tsubBV x e t
lem_erase_tsubBV x e (TExists z t_z t) = () ? lem_erase_tsubBV x e t

{-@ reflect concatB @-}
{-@ concatB :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) } 
                      -> { h:BEnv  | bindsB h == Set_cup (bindsB g) (bindsB g') } @-}
concatB :: BEnv -> BEnv -> BEnv
concatB g BEmpty         = g
concatB g (BCons x t g') = BCons x t (concatB g g')

{-@ lem_in_env_concatB :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) } 
    ->  x:Vname -> {pf:_ | (in_envB x (concatB g g')) <=> ((in_envB x g) || (in_envB x g'))} @-}
lem_in_env_concatB :: BEnv -> BEnv -> Vname -> Proof
lem_in_env_concatB g BEmpty         x = ()
lem_in_env_concatB g (BCons y s g') x = () ? lem_in_env_concatB g g' x 

{-@ lem_empty_concatB :: g:BEnv -> { pf:_ | concatB BEmpty g == g } @-}
lem_empty_concatB :: BEnv -> Proof
lem_empty_concatB BEmpty        = ()
lem_empty_concatB (BCons x t g) = () ? lem_empty_concatB g

{-@ lem_binds_cons_concatB :: g:BEnv -> g':BEnv -> x:Vname -> t_x:BType
  -> { pf:_ | Set_sub (bindsB (concatB g g')) (bindsB (concatB (BCons x t_x g) g')) && 
              bindsB (concatB (BCons x t_x g) g') == Set_cup (Set_cup (bindsB g) (Set_sng x)) (bindsB g') } @-}
lem_binds_cons_concatB :: BEnv -> BEnv -> Vname -> BType -> Proof
lem_binds_cons_concatB g BEmpty         x t = ()
lem_binds_cons_concatB g (BCons y s g') x t = () ? lem_binds_cons_concatB g g' x t

{-@ lem_erase_concat :: g:Env -> g':Env 
           -> { pf:_ |  erase_env (concatE g g') == concatB (erase_env g) (erase_env g') } @-}
lem_erase_concat :: Env -> Env -> Proof
lem_erase_concat g Empty         = ()
lem_erase_concat g (Cons x t g') = () ? lem_erase_concat g g'


-- -- -- -- -- -- -- -- -- -- -- --
-- Substitutions in Environments --
-- -- -- -- -- -- -- -- -- -- -- --

{-@ reflect esubFV @-}
{-@ esubFV :: x:Vname -> v:Value -> g:Env -> { g':Env | binds g == binds g' } @-}
esubFV :: Vname -> Expr -> Env -> Env
esubFV x e_x Empty          = Empty
esubFV x e_x (Cons z t_z g) = Cons z (tsubFV x e_x t_z) (esubFV x e_x g)

{-@ lem_in_env_esub :: g:Env -> x:Vname -> v_x:Value -> y:Vname
        -> { pf:_ | in_env y (esubFV x v_x g) <=> in_env y g } @-}
lem_in_env_esub :: Env -> Vname -> Expr -> Vname -> Proof
lem_in_env_esub Empty          x v_x y = ()
lem_in_env_esub (Cons z t_z g) x v_x y = () ? lem_in_env_esub g x v_x y
-- toProof ( in_env y (esubFV x v_x (Cons z t_z g))
-- === in_env y (Cons z (tsubFV x v_x t_z) (esubFV x v_x g))
                                               

{-@ lem_erase_esubFV :: x:Vname -> v:Expr -> g:Env
        -> { pf:_ | erase_env (esubFV x v g) == erase_env g } @-}
lem_erase_esubFV :: Vname -> Expr -> Env -> Proof
lem_erase_esubFV x e (Empty)      = ()
lem_erase_esubFV x e (Cons y t g) = () ? lem_erase_esubFV x e g
                                       ? lem_erase_tsubFV x e t

{-@ lem_esubFV_inverse :: g0:Env -> { x:Vname | not (in_env x g0) } -> t_x:Type
        -> { g:Env | Set_emp (Set_cap (binds g0) (binds g)) && not (in_env x g) } 
        -> ProofOf(WFEnv (concatE (Cons x t_x g0) g))
        -> { y:Vname | not (in_env y g) && not (in_env y g0) } 
        -> { pf:Proof | esubFV y (FV x) (esubFV x (FV y) g) == g } @-}
lem_esubFV_inverse :: Env -> Vname -> Type -> Env -> WFEnv -> Vname -> Proof
lem_esubFV_inverse g0 x t_x Empty           p_g0g_wf y = ()
lem_esubFV_inverse g0 x t_x (Cons z t_z g') p_g0g_wf y = case p_g0g_wf of
  (WFEBind env' p_env'_wf _z _tz p_env'_tz) -> case ( x == y ) of
    (True)  -> () ? lem_esubFV_inverse g0 x t_x g' p_env'_wf y
                  ? lem_tsubFV_id x t_z
    (False) -> toProof (
          esubFV y (FV x) (esubFV x (FV y) (Cons z t_z g'))
      === esubFV y (FV x) (Cons z (tsubFV x (FV y) t_z) (esubFV x (FV y) g'))
      === Cons z (tsubFV y (FV x) (tsubFV x (FV y) t_z)) (esubFV y (FV x) (esubFV x (FV y) g'))
        ? lem_esubFV_inverse g0 x t_x g' p_env'_wf y 
      === Cons z (tsubFV y (FV x) (tsubFV x (FV y) t_z)) g'
        ? lem_chain_tsubFV x y (FV x) (t_z ? lem_free_bound_in_env env' t_z p_env'_tz (y ? lem_in_env_concat (Cons x t_x g0) (Cons z t_z g') y ? lem_in_env_concat (Cons x t_x g0) g'))
        ? lem_tsubFV_id x t_z
      === Cons z t_z g' 
      )
-- ? lem_chain_tsubFV x y (FV x) (t_z ? lem_free_subset_binds g' t_z p_g'_tz)
--    | otherwise  = () ? lem_esubFV_inverse g' p_g'_wf x y
  --                    ? lem_chain_tsubFV x y (FV x) (t_z ? lem_free_subset_binds g' t_z p_g'_tz)

--------------------------------------------------------------------------
----- | Properties of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

-- EvalsToP is the transitive/reflexive closure of StepP:
{-@ lemma_evals_trans :: e1:Expr -> e2:Expr -> e3:Expr -> ProofOf( EvalsTo e1 e2)
                    -> ProofOf( EvalsTo e2 e3) -> ProofOf( EvalsTo e1 e3) @-} 
lemma_evals_trans :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo -> EvalsTo
lemma_evals_trans e1 e2 e3 (Refl _e1) p_e2e3 = p_e2e3
lemma_evals_trans e1 e2 e3 (AddStep _e1 e p_e1e _e2 p_ee2) p_e2e3 = p_e1e3
  where
    p_e1e3 = AddStep e1 e p_e1e e3 p_ee3
    p_ee3  = lemma_evals_trans e e2 e3 p_ee2 p_e2e3

{-@ lemma_app_many :: e:Expr -> e':Expr -> v':Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (App e v') (App e' v')) @-}
lemma_app_many :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_many e e' v (Refl _e) = Refl (App e v)
lemma_app_many e e' v (AddStep _e e1 s_ee1 _e' p_e1e') = p_ev_e'v
  where
    p_ev_e'v  = AddStep (App e v) (App e1 v) s_ev_e1v (App e' v) p_e1v_e'v
    s_ev_e1v  = EApp1 e e1 s_ee1 v 
    p_e1v_e'v = lemma_app_many e1 e' v p_e1e' 

{-@ lemma_app_many2 :: v:Value -> e:Expr -> e':Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (App v e) (App v e')) @-}
lemma_app_many2 :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_many2 v e e' (Refl _e) = Refl (App v e)
lemma_app_many2 v e e' (AddStep _e e1 s_ee1 _e' p_e1e') = p_ve_ve'
  where
    p_ve_ve'  = AddStep (App v e) (App v e1) s_ve_ve1 (App v e') p_ve1_ve'
    s_ve_ve1  = EApp2 e e1 s_ee1 v 
    p_ve1_ve' = lemma_app_many2 v e1 e' p_e1e' 

{-@ lemma_app_both_many :: e:Expr -> v:Value -> ProofOf(EvalsTo e v)
                             -> e':Expr -> v':Value -> ProofOf(EvalsTo e' v')
                             -> ProofOf(EvalsTo (App e e') (App v v')) @-}
lemma_app_both_many :: Expr -> Expr -> EvalsTo -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_both_many e v ev_e_v e' v' ev_e'_v' = ev_ee'_vv'
  where
    ev_ee'_ve' = lemma_app_many  e v  e' ev_e_v
    ev_ve'_vv' = lemma_app_many2 v e' v' ev_e'_v'
    ev_ee'_vv' = lemma_evals_trans (App e e') (App v e') (App v v') 
                                   ev_ee'_ve' ev_ve'_vv'

{-@ lemma_let_many :: x:Vname -> e_x:Expr -> e_x':Expr -> e:Expr 
        -> ProofOf(EvalsTo e_x e_x') -> ProofOf(EvalsTo (Let x e_x e) (Let x e_x' e)) @-}
lemma_let_many :: Vname -> Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_let_many x e_x e_x' e (Refl _ex)                               = Refl (Let x e_x e)
lemma_let_many x e_x e_x' e (AddStep _ex e_x1 s_exex1 _ex' p_ex1ex') = p_let_let'
  where
    s_let_let1  = ELet e_x e_x1 s_exex1 x e
    p_let1_let' = lemma_let_many x e_x1 e_x' e p_ex1ex'
    p_let_let'  = AddStep (Let x e_x e) (Let x e_x1 e) s_let_let1 (Let x e_x' e) p_let1_let'

{-@ lemma_annot_many :: e:Expr -> e':Expr -> t:Type -> ProofOf(EvalsTo e e')
                         -> ProofOf(EvalsTo (Annot e t) (Annot e' t)) @-}
lemma_annot_many :: Expr -> Expr -> Type -> EvalsTo -> EvalsTo
lemma_annot_many e e' t (Refl _e) = Refl (Annot e t)
lemma_annot_many e e' t (AddStep _e e1 s_ee1 _e' p_e1e') = p_et_e't
  where
    s_et_e1t  = EAnn e e1 s_ee1 t
    p_e1t_e't = lemma_annot_many e1 e' t p_e1e'
    p_et_e't  = AddStep (Annot e t) (Annot e1 t) s_et_e1t (Annot e' t) p_e1t_e't


-----------------------------------------------------------------------------------------
----- | Properties of JUDGEMENTS : the Bare-Typing Relation and Well-Formedness of Types
-----------------------------------------------------------------------------------------

-- Lemma. All free variables in a (bare) typed expression are bound in the (bare) environment
{-@ lem_fv_bound_in_benv :: g:BEnv -> e:Expr -> t:BType -> ProofOf(HasBType g e t)
                -> { x:Vname | not (in_envB x g) }
                -> { pf:_ | not (Set_mem x (fv e)) } @-}
lem_fv_bound_in_benv :: BEnv -> Expr -> BType -> HasBType -> Vname -> Proof
lem_fv_bound_in_benv g e t (BTBC _g b) x      = ()
lem_fv_bound_in_benv g e t (BTIC _g n) x      = ()
lem_fv_bound_in_benv g e t (BTVar1 _ y _t) x  = ()
lem_fv_bound_in_benv g e t (BTVar2 _ y _t p_y_t z t') x = ()
lem_fv_bound_in_benv g e t (BTPrm _g c) x     = ()
lem_fv_bound_in_benv g e t (BTAbs _g y t_y e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_benv (BCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_benv g e t (BTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) x 
    = () ? lem_fv_bound_in_benv g e1 (BTFunc t_y t') p_e1_tyt' x
         ? lem_fv_bound_in_benv g e2 t_y p_e2_ty x
lem_fv_bound_in_benv g e t (BTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> () ? lem_fv_bound_in_benv g e_y t_y p_ey_ty x
        (False) -> () ? lem_fv_bound_in_benv g e_y t_y p_ey_ty x
                      ? lem_fv_bound_in_benv (BCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_benv g e t (BTAnn _g e' _t ann_t p_e'_t) x 
    = () ? lem_fv_bound_in_benv g e' t p_e'_t x

{-@ lem_fv_subset_bindsB :: g:BEnv -> e:Expr -> t:BType -> ProofOf(HasBType g e t)
                -> { pf:_ | Set_sub (fv e) (bindsB g) } @-}
lem_fv_subset_bindsB :: BEnv -> Expr -> BType -> HasBType -> Proof
lem_fv_subset_bindsB g e t (BTBC _g b)       = ()
lem_fv_subset_bindsB g e t (BTIC _g n)       = ()
lem_fv_subset_bindsB g e t (BTVar1 _ y _t)   = ()
lem_fv_subset_bindsB g e t (BTVar2 _ y _t p_y_t z t') = ()
lem_fv_subset_bindsB g e t (BTPrm _g c)      = ()
lem_fv_subset_bindsB g e t (BTAbs _g y t_y e' t' y' p_e'_t')  
    = () ? lem_fv_subset_bindsB (BCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_subset_bindsB g e t (BTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) 
    = () ? lem_fv_subset_bindsB g e1 (BTFunc t_y t') p_e1_tyt' 
         ? lem_fv_subset_bindsB g e2 t_y p_e2_ty 
lem_fv_subset_bindsB g e t (BTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t')  
    = () ? lem_fv_subset_bindsB g e_y t_y p_ey_ty 
         ? lem_fv_subset_bindsB (BCons y' t_y g) (unbind y y' e') t' p_e'_t' 
lem_fv_subset_bindsB g e t (BTAnn _g e' _t ann_t p_e'_t) 
    = () ? lem_fv_subset_bindsB g e' t p_e'_t 

{-@ lem_free_bound_in_env :: g:Env -> t:Type -> ProofOf(WFType g t)
                -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (free t)) } @-}
lem_free_bound_in_env :: Env -> Type -> WFType -> Vname -> Proof
lem_free_bound_in_env g t (WFRefn _g z b p z' p_z'_p_bl) x
    = case ( x == z' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_benv (BCons z' (BTBase b) (erase_env g)) 
                                             (unbind z z' p) (BTBase TBool) p_z'_p_bl x
lem_free_bound_in_env g t (WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) x
    = case ( x == y' ) of
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x
lem_free_bound_in_env g t (WFExis _g y t_y p_ty_wf t' y' p_y'_t'_wf) x
    = case ( x == y' ) of 
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x

{-@ lem_free_subset_binds :: g:Env -> t:Type -> ProofOf(WFType g t)  
                  -> { pf:_ | Set_sub (free t) (binds g) } @-}
lem_free_subset_binds :: Env -> Type -> WFType -> Proof 
lem_free_subset_binds g t (WFRefn _g z b p z' p_z'_p_bl)
    = () ? lem_fv_subset_bindsB (BCons z' (BTBase b) (erase_env g)) (unbind z z' p) 
                                (BTBase TBool) p_z'_p_bl
lem_free_subset_binds g t (WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf)
    = () ? lem_free_subset_binds g t_y p_ty_wf
         ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf
lem_free_subset_binds g t (WFExis _g y t_y p_ty_wf t' y' p_y'_t'_wf)
    = () ? lem_free_subset_binds g t_y p_ty_wf
         ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf


{-@ lookup_wftype_in_env :: g:Env -> ProofOf(WFEnv g) -> x:Vname -> { t:Type | bound_in x t g }
        -> (Env,WFType)<{\g' pf -> not (in_env x g') && propOf pf == WFType g' t}> @-}
lookup_wftype_in_env :: Env -> WFEnv -> Vname -> Type -> (Env, WFType)
lookup_wftype_in_env g (WFEBind g' p_wf_g' y t_y p_wf_ty) x t
  = case (x == y) of
      (True)  -> (g', p_wf_ty)
      (False) -> lookup_wftype_in_env g' p_wf_g' x t

{-@ lem_truncate_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> ProofOf(WFEnv g) @-}
lem_truncate_wfenv :: Env -> Env -> WFEnv -> WFEnv
lem_truncate_wfenv g Empty         p_g_wf    = p_g_wf          
lem_truncate_wfenv g (Cons x v g') p_xg'g_wf = lem_truncate_wfenv g g' p_g'g_wf
  where
    (WFEBind _ p_g'g_wf _ _ _) = p_xg'g_wf 

