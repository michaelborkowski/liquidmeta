{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Strengthenings where

import Language.Haskell.Liquid.ProofCombinators hiding (withProof)

import Basics

{-@ lem_strengthen_assoc :: p:Pred -> q:Pred -> r:Pred
        -> { pf:_ | strengthen p (strengthen q r) == strengthen (strengthen p q) r } @-}
lem_strengthen_assoc :: Expr -> Expr -> Expr -> Proof
lem_strengthen_assoc (Conj p1 p2) q           r 
  =  () ? lem_strengthen_assoc p1 (strengthen p2 q) r
        ? lem_strengthen_assoc p2 q r
lem_strengthen_assoc p           (Conj q1 q2) r   =  () 
lem_strengthen_assoc p           q            r   =  ()

{-@ lem_subFV_strengthen :: x:Vname -> v:Value -> p:Pred -> r:Pred
        -> { pf:_ | subFV x v (strengthen p r) == strengthen (subFV x v p) (subFV x v r) } @-}
lem_subFV_strengthen :: Vname -> Expr -> Expr -> Expr -> Proof
lem_subFV_strengthen x v (Conj p1 p2) r = () ? lem_subFV_strengthen  x v p2 r
                                             ? lem_subFV_strengthen  x v p1 (strengthen p2 r)
lem_subFV_strengthen x v (FV y)       r 
    | x == y    = case v of
        (Conj p r) -> impossible ""
        _          -> ()
    | otherwise = () 
lem_subFV_strengthen x v p            r = () 
 
{-@ lem_subFTV_strengthen :: a:Vname -> t_a:UserType -> p:Pred -> r:Pred
        -> { pf:_ | subFTV a t_a (strengthen p r) == strengthen (subFTV a t_a p) (subFTV a t_a r) } @-}
lem_subFTV_strengthen :: Vname -> Type -> Expr -> Expr -> Proof
lem_subFTV_strengthen a t_a p r = case p of
  (Conj p' q) -> () ? lem_subFTV_strengthen a t_a q r
                    ? lem_subFTV_strengthen a t_a p' (strengthen q r)
  _           -> ()  

{-@ lem_chgFTV_strengthen :: a:Vname -> a':Vname -> p:Pred -> r:Pred
        -> { pf:_ | chgFTV a a' (strengthen p r) == strengthen (chgFTV a a' p) (chgFTV a a' r) } @-}
lem_chgFTV_strengthen :: Vname -> Vname -> Expr -> Expr -> Proof
lem_chgFTV_strengthen a a' p r = case p of
  (Conj p' q) -> () ? lem_chgFTV_strengthen a a' q r
                    ? lem_chgFTV_strengthen a a' p' (strengthen q r)
  _           -> ()  

{-@ lem_subBV_strengthen :: x:Vname -> v:Value -> p:Pred -> r:Pred
        -> { pf:_ | subBV x v (strengthen p r) == strengthen (subBV x v p) (subBV x v r) } @-}
lem_subBV_strengthen :: Vname -> Expr -> Expr -> Expr -> Proof
lem_subBV_strengthen x v (Conj p1 p2) r       = () ? lem_subBV_strengthen x v p2 r
                                                   ? lem_subBV_strengthen x v p1 (strengthen p2 r)
lem_subBV_strengthen x v (BV y)       r 
    | x == y    = case v of
        (Conj p r) -> impossible ""
        _          -> () 
    | otherwise = ()
lem_subBV_strengthen x v p            r       = () 
 
{-@ lem_unbind_tv_strengthen :: a:Vname -> a':Vname -> p:Pred -> r:Pred
        -> { pf:_ | unbind_tv a a' (strengthen p r) == strengthen (unbind_tv a a' p) (unbind_tv a a' r) } @-}
lem_unbind_tv_strengthen :: Vname -> Vname -> Expr -> Expr -> Proof
lem_unbind_tv_strengthen a a' p r = case p of
  (Conj p' q) -> () ? lem_unbind_tv_strengthen a a' q r
                    ? lem_unbind_tv_strengthen a a' p' (strengthen q r)
  _                            -> ()  

{-@ lem_subBTV_strengthen :: a:Vname -> t_a:Type -> p:Pred -> r:Pred
        -> { pf:_ | subBTV a t_a (strengthen p r) == strengthen (subBTV a t_a p) (subBTV a t_a r) } @-}
lem_subBTV_strengthen :: Vname -> Type -> Expr -> Expr -> Proof
lem_subBTV_strengthen a t_a p r = case p of
  (Conj p' q) -> () ? lem_subBTV_strengthen a t_a q r
                    ? lem_subBTV_strengthen a t_a p' (strengthen q r)
  _                            -> ()  

{-@ lem_strengthen_trivial :: { p:Pred | isTrivial p } -> { q:Pred | isTrivial q}
        -> { pf:_ | isTrivial (strengthen p q) } @-}
lem_strengthen_trivial :: Expr -> Expr -> Proof
lem_strengthen_trivial (Bc True) r   = ()
lem_strengthen_trivial (Conj p' q') r = case p' of 
   (Bc True) -> () ? lem_strengthen_trivial q' r
                   ? lem_strengthen_trivial (Bc True) (strengthen q' r)
