{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Strengthenings where

import Language.Haskell.Liquid.ProofCombinators hiding (withProof)

import Basics

{-@ reflect withProof' @-}
{-@ withProof' :: x:Proof -> Proof -> { v:_ | v = x } @-}
withProof' :: Proof -> Proof -> Proof
withProof' x _ = x

{-@ lem_strengthen_assoc :: p:Pred -> q:Pred -> r:Pred
        -> { pf:_ | strengthen p (strengthen q r) == strengthen (strengthen p q) r } @-}
lem_strengthen_assoc :: Pred -> Pred -> Pred -> Proof
lem_strengthen_assoc (App p' p2) q           r = case p' of
  (App (Prim Conj) p1) -> () ? lem_strengthen_assoc p1 (strengthen p2 q) r
                             ? lem_strengthen_assoc p2 q r
  _                    -> ()
lem_strengthen_assoc p           (App q' q2) r = case q' of
  (App (Prim Conj) q1) -> () 
  _                    -> ()
lem_strengthen_assoc p           q           r = ()

{-@ reflect isConjunction @-}
isConjunction :: Pred -> Bool
isConjunction (App p q) = case p of
  (App (Prim Conj) _)       -> True
  _                         -> False
isConjunction _         = False

{-@ lem_subFV_conjunction :: x:Vname -> v:Value -> { p:Pred | not (isConjunction p) }
        -> { pf:_ | not (isConjunction (subFV x v p)) } @-}
lem_subFV_conjunction :: Vname -> Expr -> Pred -> Proof
lem_subFV_conjunction x v (App p q) = case p of
  (App p1 p2) -> ()
  _           -> ()
lem_subFV_conjunction x v _ = ()

{-@ lem_subFV_strengthen :: x:Vname -> v:Value -> p:Pred -> r:Pred
        -> { pf:_ | subFV x v (strengthen p r) == strengthen (subFV x v p) (subFV x v r) } @-}
lem_subFV_strengthen :: Vname -> Expr -> Pred -> Pred -> Proof
lem_subFV_strengthen x v (App p' p2) r = case p' of
  (App (Prim Conj) p1) -> () ? lem_subFV_strengthen x v p2 r
                             ? lem_subFV_strengthen x v p1 (strengthen p2 r)
  _                    -> () ? lem_subFV_conjunction x v (App p' p2)
lem_subFV_strengthen x v p           r = () ? lem_subFV_conjunction x v p
 
{-@ lem_subFTV_strengthen :: a:Vname -> t_a:Type -> p:Pred -> r:Pred
        -> { pf:_ | subFTV a t_a (strengthen p r) == strengthen (subFTV a t_a p) (subFTV a t_a r) } @-}
lem_subFTV_strengthen :: Vname -> Type -> Pred -> Pred -> Proof
lem_subFTV_strengthen a t_a p r = case p of
  (App (App (Prim Conj) p') q) -> () ? lem_subFTV_strengthen a t_a q r
                                     ? lem_subFTV_strengthen a t_a p' (strengthen q r)
  _                            -> ()  

{-@ lem_unbind_tv_strengthen :: a:Vname -> a':Vname -> p:Pred -> r:Pred
        -> { pf:_ | unbind_tv a a' (strengthen p r) == strengthen (unbind_tv a a' p) (unbind_tv a a' r) } @-}
lem_unbind_tv_strengthen :: Vname -> Vname -> Pred -> Pred -> Proof
lem_unbind_tv_strengthen a a' p r = case p of
  (App (App (Prim Conj) p') q) -> () ? lem_unbind_tv_strengthen a a' q r
                                     ? lem_unbind_tv_strengthen a a' p' (strengthen q r)
  _                            -> ()  

{-@ lem_subBTV_strengthen :: a:Vname -> t_a:Type -> p:Pred -> r:Pred
        -> { pf:_ | subBTV a t_a (strengthen p r) == strengthen (subBTV a t_a p) (subBTV a t_a r) } @-}
lem_subBTV_strengthen :: Vname -> Type -> Pred -> Pred -> Proof
lem_subBTV_strengthen a t_a p r = case p of
  (App (App (Prim Conj) p') q) -> () ? lem_subBTV_strengthen a t_a q r
                                     ? lem_subBTV_strengthen a t_a p' (strengthen q r)
  _                            -> ()  
