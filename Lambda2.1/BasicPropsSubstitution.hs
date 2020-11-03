{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsSubstitution where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

{-@ reflect foo18 @-}   
foo18 x = Just x 
foo18 :: a -> Maybe a 

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
lem_subFV_value y v_y (BV x)          = ()
lem_subFV_value y v_y (Lambda x e) 
    | x == y    = () -- toProof ( subFV y v_y (Lambda x e) === Lambda x (subFV y v_y e) )
    | otherwise = () 
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
  | otherwise = ()
lem_commute_subFV_subBV x v y v_y (FV w)       
  | y == w    = () 
                   ? lem_subBV_notin x (subFV y v_y v) v_y
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
lem_commute_subFV x v y v_y Crash        = ()



------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in TERMS
------------------------------------------------------------------------------

{-@ lem_subFTV_notin :: a:Vname -> t:Type -> { e:Expr | not (Set_mem a (ftv e)) } 
                               -> { pf:_ | subFTV a t e == e } / [esize e] @-}
lem_subFTV_notin :: Vname -> Type -> Expr -> Proof
lem_subFTV_notin a t (Bc b)           = ()
lem_subFTV_notin a t (Ic n)           = ()
lem_subFTV_notin a t (Prim c)         = ()
lem_subFTV_notin a t (BV y)           = ()
lem_subFTV_notin a t (FV y)           = ()
lem_subFTV_notin a t e@(Lambda w e')  = () ? lem_subFTV_notin  a t e'
lem_subFTV_notin a t (App e1 e2)      = () ? lem_subFTV_notin  a t e1
                                           ? lem_subFTV_notin  a t e2
lem_subFTV_notin a t (LambdaT a' k e) = () ? lem_subFTV_notin  a t e
lem_subFTV_notin a t (AppT e' t')     = () ? lem_subFTV_notin  a t e'
                                           ? lem_tsubFTV_notin a (toBare t) t'  
lem_subFTV_notin a t e@(Let w ew e')  = () ? lem_subFTV_notin  a t ew
                                           ? lem_subFTV_notin  a t e'
lem_subFTV_notin a t (Annot e' t')    = () ? lem_subFTV_notin  a t e'
                                           ? lem_tsubFTV_notin a t t'
lem_subFTV_notin a t (Crash)          = () 

{-@ lem_chgFTV_notin :: a:Vname -> a1:Vname -> { e:Expr | not (Set_mem a (ftv e)) } 
                               -> { pf:_ | chgFTV a a1 e == e } / [esize e] @-}
lem_chgFTV_notin :: Vname -> Vname -> Expr -> Proof
lem_chgFTV_notin a a1 (Bc b)           = ()
lem_chgFTV_notin a a1 (Ic n)           = ()
lem_chgFTV_notin a a1 (Prim c)         = ()
lem_chgFTV_notin a a1 (BV y)           = ()
lem_chgFTV_notin a a1 (FV y)           = ()
lem_chgFTV_notin a a1 e@(Lambda w e')  = () ? lem_chgFTV_notin  a a1 e'
lem_chgFTV_notin a a1 (App e1 e2)      = () ? lem_chgFTV_notin  a a1 e1
                                            ? lem_chgFTV_notin  a a1 e2
lem_chgFTV_notin a a1 (LambdaT a' k e) = () ? lem_chgFTV_notin  a a1 e
lem_chgFTV_notin a a1 (AppT e' t')     = () ? lem_chgFTV_notin  a a1 e'
                                            ? lem_tchgFTV_notin a a1 t'  
lem_chgFTV_notin a a1 e@(Let w ew e')  = () ? lem_chgFTV_notin  a a1 ew
                                            ? lem_chgFTV_notin  a a1 e'
lem_chgFTV_notin a a1 (Annot e' t')    = () ? lem_chgFTV_notin  a a1 e'
                                            ? lem_tchgFTV_notin a a1 t'
lem_chgFTV_notin a a1 (Crash)          = () 

{-@ lem_subBTV_notin :: a:Vname -> t:Type -> { e:Expr | not (Set_mem a (freeBTV e)) } 
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
                                           ? lem_tsubBTV_notin a (toBare t)	 t' 
lem_subBTV_notin a t (Let w ew e)     = () ? lem_subBTV_notin a t ew
                                           ? lem_subBTV_notin a t e
lem_subBTV_notin a t (Annot e' t')    = () ? lem_subBTV_notin  a t e'
                                           ? lem_tsubBTV_notin a t t'
lem_subBTV_notin a t Crash            = ()

{-@ lem_subFTV_unbind_tv :: a:Vname -> a':Vname -> t:Type 
      -> { e:Expr | not (Set_mem a' (ftv e)) }
      -> { pf:_ | subBTV a t e == subFTV a' t (unbind_tv a a' e) } / [esize e] @-}
lem_subFTV_unbind_tv :: Vname -> Vname -> Type -> Expr -> Proof
lem_subFTV_unbind_tv a a' t (Bc b)   = ()
lem_subFTV_unbind_tv a a' t (Ic n)   = ()
lem_subFTV_unbind_tv a a' t (Prim c) = ()
lem_subFTV_unbind_tv a a' t (BV w)   = ()
lem_subFTV_unbind_tv a a' t (FV w)   = ()
lem_subFTV_unbind_tv a a' t (Lambda w e') 
                = () ? lem_subFTV_unbind_tv a a' t e'
lem_subFTV_unbind_tv a a' t (App e1 e2) 
                = () ? lem_subFTV_unbind_tv a a' t e1
                     ? lem_subFTV_unbind_tv a a' t e2
lem_subFTV_unbind_tv a a' t (LambdaT a1 k e')
    | a == a1   = () ? lem_subFTV_notin a' t e' 
    | otherwise = () ? lem_subFTV_unbind_tv a a' t e'
lem_subFTV_unbind_tv a a' t (AppT e' t')
                = () ? lem_subFTV_unbind_tv   a a' t e'  
                     ? lem_tsubFTV_unbind_tvT a a' (toBare t) t'
lem_subFTV_unbind_tv a a' t (Let w ew e')
                = () ? lem_subFTV_unbind_tv a a' t ew
                     ? lem_subFTV_unbind_tv a a' t e'
lem_subFTV_unbind_tv a a' t (Annot e' t')
                = () ? lem_subFTV_unbind_tv   a a' t e'
                     ? lem_tsubFTV_unbind_tvT a a' t t'
lem_subFTV_unbind_tv a a' t (Crash)  = () 

{-@ lem_chgFTV_unbind_tv :: a:Vname -> a':Vname -> a'':Vname
      -> { e:Expr | not (Set_mem a' (ftv e)) }
      -> { pf:_ | unbind_tv a a'' e == chgFTV a' a'' (unbind_tv a a' e) } / [esize e] @-}
lem_chgFTV_unbind_tv :: Vname -> Vname -> Vname -> Expr -> Proof
lem_chgFTV_unbind_tv a a' a'' (Bc b)   = ()
lem_chgFTV_unbind_tv a a' a'' (Ic n)   = ()
lem_chgFTV_unbind_tv a a' a'' (Prim c) = ()
lem_chgFTV_unbind_tv a a' a'' (BV w)   = ()
lem_chgFTV_unbind_tv a a' a'' (FV w)   = ()
lem_chgFTV_unbind_tv a a' a'' (Lambda w e') 
                = () ? lem_chgFTV_unbind_tv a a' a'' e'
lem_chgFTV_unbind_tv a a' a'' (App e1 e2) 
                = () ? lem_chgFTV_unbind_tv a a' a'' e1
                     ? lem_chgFTV_unbind_tv a a' a'' e2
lem_chgFTV_unbind_tv a a' a'' (LambdaT a1 k e')
    | a == a1   = () ? lem_chgFTV_notin a' a'' e' 
    | otherwise = () ? lem_chgFTV_unbind_tv a a' a'' e'
lem_chgFTV_unbind_tv a a' a'' (AppT e' t')
                = () ? lem_chgFTV_unbind_tv   a a' a'' e'  
                     ? lem_tchgFTV_unbind_tvT a a' a'' t'
lem_chgFTV_unbind_tv a a' a'' (Let w ew e')
                = () ? lem_chgFTV_unbind_tv a a' a'' ew
                     ? lem_chgFTV_unbind_tv a a' a'' e'
lem_chgFTV_unbind_tv a a' a'' (Annot e' t')
                = () ? lem_chgFTV_unbind_tv   a a' a'' e'
                     ? lem_tchgFTV_unbind_tvT a a' a'' t'
lem_chgFTV_unbind_tv a a' a'' (Crash)  = () 


{-@ lem_commute_subFTV_subBV :: x:Vname -> v:Value 
        -> a:Vname -> { t_a:Type | not (Set_mem x (tfreeBV t_a)) } -> e:Expr
        -> { pf:_ | subFTV a t_a (subBV x v e) == subBV x (subFTV a t_a v) (subFTV a t_a e) } / [esize e] @-}
lem_commute_subFTV_subBV :: Vname -> Expr -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBV x v a t_a (Bc b)       = ()
lem_commute_subFTV_subBV x v a t_a (Ic n)       = ()
lem_commute_subFTV_subBV x v a t_a (Prim p)     = ()
lem_commute_subFTV_subBV x v a t_a (BV w) 
  | x == w    = () -- ? lem_subFV_notin y v_y (BV x)
  | otherwise = ()
lem_commute_subFTV_subBV x v a t_a (FV w)       = () 
{-
  | y == w    = () 
                   ? lem_subBV_notin x (subFV y v_y v) v_y
  | otherwise = ()-}
lem_commute_subFTV_subBV x v a t_a (Lambda w e)
  | x == w    = () 
  | otherwise = () ? lem_commute_subFTV_subBV x v a t_a e
lem_commute_subFTV_subBV x v a t_a (App e e')
              = () ? lem_commute_subFTV_subBV x v a t_a e
                   ? lem_commute_subFTV_subBV x v a t_a e'
lem_commute_subFTV_subBV x v a t_a (LambdaT a' k e)
              = () ? lem_commute_subFTV_subBV   x v a t_a e
lem_commute_subFTV_subBV x v a t_a (AppT e t) = undefined {-
              = () ? lem_commute_subFTV_subBV   x v a t_a e
                   ? lem_commute_tsubFTV_tsubBV x v a (toBare t_a) t
                   ? lem_tsubBV_notin x v (t ? toProof ( tfreeBV t === S.empty ))
                   ? lem_tsubBV_notin x (subFTV a t_a v) (tsubFTV a t_a t ? toProof ( tfreeBV (tsubFTV a t_a t) === S.empty ))  -}
lem_commute_subFTV_subBV x v a t_a (Let w ew e)
  | x == w    = () ? lem_commute_subFTV_subBV x v a t_a ew
  | otherwise = () ? lem_commute_subFTV_subBV x v a t_a ew
                   ? lem_commute_subFTV_subBV x v a t_a e
lem_commute_subFTV_subBV x v a t_a (Annot e t)
              = () ? lem_commute_subFTV_subBV   x v a t_a e
                   ? lem_commute_tsubFTV_tsubBV x v a t_a t
lem_commute_subFTV_subBV x v a t_a Crash        = ()

{-@ lem_commute_subFTV_subBV1 :: x:Vname -> v:Value 
        -> { a:Vname | not (Set_mem a (ftv v)) } -> { t_a:Type | not (Set_mem x (tfreeBV t_a)) } -> e:Expr
        -> { pf:_ | subFTV a t_a (subBV x v e) == subBV x v (subFTV a t_a e) } @-}
lem_commute_subFTV_subBV1 :: Vname -> Expr -> Vname -> Type -> Expr -> Proof
lem_commute_subFTV_subBV1 x v a t_a e = lem_commute_subFTV_subBV x v a t_a e 
                                            ? lem_subFTV_notin a t_a v 


------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TERM VARIABLES in TYPES
------------------------------------------------------------------------------

{-@ lem_tsubFV_id :: x:Vname -> t:Type -> { pf:_ | tsubFV x (FV x) t == t } / [tsize t] @-}
lem_tsubFV_id :: Vname -> Type -> Proof
lem_tsubFV_id x t@(TRefn b w p)      = () ? lem_subFV_id x p
lem_tsubFV_id x t@(TFunc w t_w t')   = () ? lem_tsubFV_id x t_w
                                          ? lem_tsubFV_id x t'
lem_tsubFV_id x t@(TExists w t_w t') = () ? lem_tsubFV_id x t_w
                                          ? lem_tsubFV_id x t'
lem_tsubFV_id x t@(TPoly a k t')     = () ? lem_tsubFV_id x t'

{-@ lem_tsubFV_notin :: x:Vname -> v:Value -> { t:Type | not (Set_mem x (free t)) } 
                               -> { pf:_ | tsubFV x v t == t } / [tsize t] @-}
lem_tsubFV_notin :: Vname -> Expr -> Type -> Proof
lem_tsubFV_notin x v t@(TRefn b w p)      = () ? lem_subFV_notin x v p
lem_tsubFV_notin x v t@(TFunc w t_w t')   = () ? lem_tsubFV_notin x v t_w
                                               ? lem_tsubFV_notin x v t'
lem_tsubFV_notin x v t@(TExists w t_w t') = () ? lem_tsubFV_notin x v t_w
                                               ? lem_tsubFV_notin x v t'
lem_tsubFV_notin x v t@(TPoly a k t')     = () ? lem_tsubFV_notin x v t'


{-@ lem_tsubBV_notin :: x:Vname -> v_x:Value -> { t:Type | not (Set_mem x (tfreeBV t)) }
                -> { pf:_ | tsubBV x v_x t == t } / [tsize t] @-} 
lem_tsubBV_notin :: Vname -> Expr -> Type -> Proof
lem_tsubBV_notin x v_x (TRefn b y r)       
    | x == y    = ()
    | otherwise = () ? lem_subBV_notin x v_x r
lem_tsubBV_notin x v_x (TFunc z t_z t)       
    | x == z    = () ? lem_tsubBV_notin x v_x t_z
    | otherwise = () ? lem_tsubBV_notin x v_x t_z
                     ? lem_tsubBV_notin x v_x t
lem_tsubBV_notin x v_x (TExists z t_z t)       
    | x == z    = () ? lem_tsubBV_notin x v_x t_z
    | otherwise = () ? lem_tsubBV_notin x v_x t_z
                     ? lem_tsubBV_notin x v_x t
lem_tsubBV_notin x v_x (TPoly a k t) = () ? lem_tsubBV_notin x v_x t

{-@ lem_tsubFV_unbindT :: x:Vname -> y:Vname -> v:Value 
        -> { t:Type | not (Set_mem y (free t)) }
        -> { pf:_ | tsubBV x v t == tsubFV y v (unbindT x y t) } / [tsize t] @-}
lem_tsubFV_unbindT :: Vname -> Vname -> Expr -> Type -> Proof
lem_tsubFV_unbindT x y v t@(TRefn b w p)     
  | x == w     = () ? lem_subFV_notin y v p
  | otherwise  = () ? lem_subFV_unbind x y v p
lem_tsubFV_unbindT x y v t@(TFunc w t_w t')
  | x == w     = ()      ? lem_tsubFV_unbindT x y v t_w
                         ? lem_tsubFV_notin y v t'
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w 
                    ? lem_tsubFV_unbindT x y v t' 
lem_tsubFV_unbindT x y v t@(TExists w t_w t') 
  | x == w     = ()      ? lem_tsubFV_unbindT x y v t_w 
                         ? lem_tsubFV_notin y v t'
  | otherwise  = () ? lem_tsubFV_unbindT x y v t_w
                    ? lem_tsubFV_unbindT x y v t'
lem_tsubFV_unbindT x y v t@(TPoly a k t') = () ? lem_tsubFV_unbindT x y v t'

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
lem_commute_tsubFV_unbindT x y z z' (TPoly a k t)
              = () ? lem_commute_tsubFV_unbindT x y z z' t

{-@ lem_commute_tsubFV_tsubBV :: x:Vname -> v:Value 
        -> y:Vname -> { v_y:Value | not (Set_mem x (freeBV v_y)) }  -> t:Type
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
lem_commute_tsubFV_tsubBV x v y v_y (TPoly a k t) 
              = () ? lem_commute_tsubFV_tsubBV x v y v_y t

{-@ lem_commute_tsubFV_tsubBV1 :: x:Vname -> v:Value 
        -> { y:Vname | not (Set_mem y (fv v)) } -> { v_y:Value | not (Set_mem x (freeBV v_y)) } -> t:Type
        -> { pf:_ | tsubFV y v_y (tsubBV x v t) == tsubBV x v (tsubFV y v_y t) } @-}
lem_commute_tsubFV_tsubBV1 :: Vname -> Expr -> Vname -> Expr -> Type -> Proof
lem_commute_tsubFV_tsubBV1 x v y v_y t = lem_commute_tsubFV_tsubBV x v y v_y t
                                             ? lem_subFV_notin y v_y v

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

{-  These may be false!!
{-@ lem_subBV_strengthen :: x:Vname -> v:Value -> p:Pred -> r:Pred 
        -> { pf:_ | subBV x v (strengthen p r) == strengthen (subBV x v p) (subBV x v r) } @-}
lem_subBV_strengthen :: Vname -> Expr -> Expr -> Expr -> Proof
lem_subBV_strengthen x v p r
  | ( r == Bc True ) = ()
  | ( p == Bc True ) = ()
  | otherwise        = ()

{-@ lem_subBV_push :: x:Vname -> v:Value -> p:Pred -> t:Type
        -> { pf:_ | tsubBV x v (push p t) == push (subBV x v p) (tsubBV x v t) } @-}
lem_subBV_push :: Vname -> Expr -> Expr -> Type -> Proof
lem_subBV_push x v p (TRefn   b z   r) 
  | x == z    = ()
  | otherwise = () -- ? lem_subBV_strengthen x v p r
lem_subBV_push x v p (TFunc   y t_y t) 
  | x == y    = () ? lem_subBV_push x v p t_y
  | otherwise = () ? lem_subBV_push x v p t_y ? lem_subBV_push x v p t
lem_subBV_push x v p (TExists y t_y t) 
  | x == y    = () ? lem_subBV_push x v p t_y
  | otherwise = () ? lem_subBV_push x v p t_y ? lem_subBV_push x v p t 
lem_subBV_push x v p (TPoly   a k   t) = () ? lem_subBV_push x v p t
-}
------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in TYPES
------------------------------------------------------------------------------

{-@ lem_tsubFTV_notin :: a:Vname -> t_a:Type -> { t:Type | not (Set_mem a (freeTV t)) } 
                               -> { pf:_ | tsubFTV a t_a t == t } / [tsize t] @-}
lem_tsubFTV_notin :: Vname -> Type -> Type -> Proof
lem_tsubFTV_notin a t_a t@(TRefn b w p)      = () ? lem_subFTV_notin a t_a p
lem_tsubFTV_notin a t_a t@(TFunc w t_w t')   = () ? lem_tsubFTV_notin a t_a t_w
                                                  ? lem_tsubFTV_notin a t_a t'
lem_tsubFTV_notin a t_a t@(TExists w t_w t') = () ? lem_tsubFTV_notin a t_a t_w
                                                  ? lem_tsubFTV_notin a t_a t'
lem_tsubFTV_notin a t_a t@(TPoly a' k t')    = () ? lem_tsubFTV_notin a t_a t'

{-@ lem_tchgFTV_notin :: a:Vname -> a1:Vname -> { t:Type | not (Set_mem a (freeTV t)) } 
                               -> { pf:_ | tchgFTV a a1 t == t } / [tsize t] @-}
lem_tchgFTV_notin :: Vname -> Vname -> Type -> Proof
lem_tchgFTV_notin a a1 t@(TRefn b w p)      = () ? lem_chgFTV_notin  a a1 p
lem_tchgFTV_notin a a1 t@(TFunc w t_w t')   = () ? lem_tchgFTV_notin a a1 t_w
                                                 ? lem_tchgFTV_notin a a1 t'
lem_tchgFTV_notin a a1 t@(TExists w t_w t') = () ? lem_tchgFTV_notin a a1 t_w
                                                 ? lem_tchgFTV_notin a a1 t'
lem_tchgFTV_notin a a1 t@(TPoly a' k t')    = () ? lem_tchgFTV_notin a a1 t'

{-@ lem_tsubBTV_notin :: a:Vname -> t_a:Type -> { t:Type | not (Set_mem a (tfreeBTV t)) }
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


{-@ lem_tsubFTV_unbind_tvT :: a:Vname -> a':Vname -> t_a:Type 
        -> { t:Type | not (Set_mem a' (freeTV t)) }
        -> { pf:_ | tsubBTV a t_a t == tsubFTV a' t_a (unbind_tvT a a' t) } / [tsize t] @-}
lem_tsubFTV_unbind_tvT :: Vname -> Vname -> Type -> Type -> Proof
lem_tsubFTV_unbind_tvT a a' t_a t@(TRefn b w p)    = case b of 
  (FTV a1) | a1 == a   -> () ? lem_subFTV_unbind_tv   a a' t_a p
           | otherwise -> () ? lem_subFTV_unbind_tv   a a' t_a p
  (BTV a1) | a1 == a   -> () ? lem_subFTV_unbind_tv   a a' t_a p
  _                    -> () ? lem_subFTV_unbind_tv   a a' t_a p
lem_tsubFTV_unbind_tvT a a' t_a (TFunc w t_w t')   = () ? lem_tsubFTV_unbind_tvT a a' t_a t_w 
                                                        ? lem_tsubFTV_unbind_tvT a a' t_a t' 
lem_tsubFTV_unbind_tvT a a' t_a (TExists w t_w t') = () ? lem_tsubFTV_unbind_tvT a a' t_a t_w
                                                        ? lem_tsubFTV_unbind_tvT a a' t_a t'
lem_tsubFTV_unbind_tvT a a' t_a t@(TPoly a1 k t') 
  | a == a1    = () ? lem_tsubFTV_notin        a' t_a t'
  | otherwise  = () ? lem_tsubFTV_unbind_tvT a a' t_a t'

{-@ lem_tchgFTV_unbind_tvT :: a:Vname -> a':Vname -> a'':Vname
        -> { t:Type | not (Set_mem a' (freeTV t)) }
        -> { pf:_ | unbind_tvT a a'' t == tchgFTV a' a'' (unbind_tvT a a' t) } / [tsize t] @-}
lem_tchgFTV_unbind_tvT :: Vname -> Vname -> Vname -> Type -> Proof
lem_tchgFTV_unbind_tvT a a' a'' t@(TRefn b w p)    = case b of 
  (FTV a1) | a1 == a   -> () ? lem_chgFTV_unbind_tv   a a' a'' p
           | otherwise -> () ? lem_chgFTV_unbind_tv   a a' a'' p
  (BTV a1) | a1 == a   -> () ? lem_chgFTV_unbind_tv   a a' a'' p
  _                    -> () ? lem_chgFTV_unbind_tv   a a' a'' p
lem_tchgFTV_unbind_tvT a a' a'' (TFunc w t_w t')   = () ? lem_tchgFTV_unbind_tvT a a' a'' t_w 
                                                        ? lem_tchgFTV_unbind_tvT a a' a'' t' 
lem_tchgFTV_unbind_tvT a a' a'' (TExists w t_w t') = () ? lem_tchgFTV_unbind_tvT a a' a'' t_w
                                                        ? lem_tchgFTV_unbind_tvT a a' a'' t'
lem_tchgFTV_unbind_tvT a a' a'' t@(TPoly a1 k t') 
  | a == a1    = () ? lem_tchgFTV_notin        a' a'' t'
  | otherwise  = () ? lem_tchgFTV_unbind_tvT a a' a'' t'

{-@ lem_commute_tsubFTV_tsubBV :: x:Vname -> v:Value 
        -> a:Vname -> { t_a:Type | not (Set_mem x (tfreeBV t_a)) } -> t:Type
        -> { pf:_ | tsubFTV a t_a (tsubBV x v t) == tsubBV x (subFTV a t_a v) (tsubFTV a t_a t) } / [tsize t] @-}
lem_commute_tsubFTV_tsubBV :: Vname -> Expr -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBV x v a t_a (TRefn b w p) = case b of
  (FTV a') | a == a' && x == w       -> undefined {- () ? toProof (
          tsubBV x (subFTV a t_a v) (tsubFTV a t_a (TRefn (FTV a) x p)) 
      === tsubBV x (subFTV a t_a v) (push (subFTV a t_a p) t_a)
        ? lem_subBV_push x (subFTV a t_a v) (subFTV a t_a p) t_a
        ? lem_tsubBV_notin x (tsubFTV a t_a v) t_a
      === push ( subBV x (subFTV a t_a v) (subFTV a t_a p) ) t_a
        ? lem_commute_subFTV_subBV x v a t_a p
      === push ( subFTV a t_a (subBV x v p) ) t_a
      === tsubFTV a t_a (TRefn (FTV a) x (subBV x v p))

     tsubFTV a t_a (tsubBV x v (TRefn (FTV a) x p))
 === tsubFTV a t_a (TRefn (FTV a) x p)
 === push (subFTV a t_a p) t_a  
-}
           | a == a' && not (x == w) -> undefined {-
     tsubFTV a t_a (tsubBV x v (TRefn (FTV a) w p))
 === tsubFTV a t_a (TRefn (FTV a) w (subBV x v p))
 === push (subFTV a t_a (subBV x v p)) t_a 
        ? lem_commute_subFTV_subBV x v a t_a p 
 === push (subBV x (subFTV a t_a v) (subFTV a t_a p)) t_a 
        ? lem_subBV_push x (subFTV a t_a v) (subFTV a t_a p) t_a -}
           | otherwise -> () ? lem_commute_subFTV_subBV x v a t_a p
  _        | x == w    -> () 
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
        -> { a:Vname | not (Set_mem a (ftv v)) } -> { t_a:BareType | not (Set_mem x (tfreeBV t_a)) } -> t:Type
        -> { pf:_ | tsubFTV a t_a (tsubBV x v t) == tsubBV x v (tsubFTV a t_a t) } @-}
lem_commute_tsubFTV_tsubBV1 :: Vname -> Expr -> Vname -> Type -> Type -> Proof
lem_commute_tsubFTV_tsubBV1 x v a t_a t = lem_commute_tsubFTV_tsubBV x v a t_a t
                                             ? lem_subFTV_notin a t_a v


---------------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in SYSTEM F TYPES
---------------------------------------------------------------------------------------

{-@ lem_ftsubFV_notin :: a:Vname -> t_a:FType -> { t:FType | not (Set_mem a (ffreeTV t)) } 
                               -> { pf:_ | ftsubFV a t_a t == t } / [ftsize t] @-}
lem_ftsubFV_notin :: Vname -> FType -> FType -> Proof
lem_ftsubFV_notin a t_a (FTBasic b)      = () 
lem_ftsubFV_notin a t_a (FTFunc t_w t')  = () ? lem_ftsubFV_notin a t_a t_w
                                              ? lem_ftsubFV_notin a t_a t'
lem_ftsubFV_notin a t_a (FTPoly a' k t') = () ? lem_ftsubFV_notin a t_a t'

{-@ lem_ftsubFV_unbindFT :: a:Vname -> a':Vname -> t_a:FType 
        -> { t:FType | not (Set_mem a' (ffreeTV t)) }
        -> { pf:_ | ftsubBV a t_a t == ftsubFV a' t_a (unbindFT a a' t) } / [ftsize t] @-}
lem_ftsubFV_unbindFT :: Vname -> Vname -> FType -> FType -> Proof
lem_ftsubFV_unbindFT a a' t_a (FTBasic b)      = ()
lem_ftsubFV_unbindFT a a' t_a (FTFunc t_w t')  = () ? lem_ftsubFV_unbindFT a a' t_a t_w 
                                                    ? lem_ftsubFV_unbindFT a a' t_a t' 
lem_ftsubFV_unbindFT a a' t_a (FTPoly a1 k t') 
  | a == a1    = () ? lem_ftsubFV_notin      a' t_a t'
  | otherwise  = () ? lem_ftsubFV_unbindFT a a' t_a t'

{-@ lem_commute_ftsubFV_unbindFT :: a0:Vname -> a1:Vname -> a:Vname 
        -> { a':Vname | a' != a0 } -> t:FType
        -> {pf:_ | ftsubFV a0 (FTBasic (FTV a1)) (unbindFT a a' t) 
                   == unbindFT a a' (ftsubFV a0 (FTBasic (FTV a1)) t)} / [ftsize t] @-}
lem_commute_ftsubFV_unbindFT :: Vname -> Vname -> Vname -> Vname -> FType -> Proof
lem_commute_ftsubFV_unbindFT a0 a1 a a' (FTBasic b) = ()
lem_commute_ftsubFV_unbindFT a0 a1 a a' (FTFunc t1 t2)
  = () ? lem_commute_ftsubFV_unbindFT a0 a1 a a' t1
       ? lem_commute_ftsubFV_unbindFT a0 a1 a a' t2
lem_commute_ftsubFV_unbindFT a0 a1 a a' (FTPoly aa k t)
  | a == aa   = ()
  | otherwise = () ? lem_commute_ftsubFV_unbindFT a0 a1 a a' t
