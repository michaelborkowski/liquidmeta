{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Strengthenings where

import Language.Haskell.Liquid.ProofCombinators hiding (withProof)

import Basics

-- reminder: strengthen PEmpty       rs = rs
--           strengthen (PCons p ps) rs = PCons p (strengthen ps rs)

{-@ lem_strengthen_empty :: ps:Preds -> { pf:_ | strengthen ps PEmpty == ps } @-}
lem_strengthen_empty :: Preds -> Proof
lem_strengthen_empty PEmpty       = ()
lem_strengthen_empty (PCons p ps) = () ? lem_strengthen_empty ps

{-@ lem_strengthen_one :: p:Expr -> ps:Preds 
        -> { pf:_ | strengthen (PCons p PEmpty) ps == PCons p ps } @-}
lem_strengthen_one :: Expr -> Preds -> Proof
lem_strengthen_one p ps = ()

{-@ lem_strengthen_assoc :: ps:Preds -> qs:Preds -> rs:Preds
        -> { pf:_ | strengthen ps (strengthen qs rs) == strengthen (strengthen ps qs) rs } @-}
lem_strengthen_assoc :: Preds -> Preds -> Preds -> Proof
lem_strengthen_assoc PEmpty       qs rs = ()
lem_strengthen_assoc (PCons p ps) qs rs = () ? lem_strengthen_assoc ps qs rs

{-@ lem_psubFV_strengthen :: x:Vname -> v:Value -> ps:Preds -> rs:Preds
        -> { pf:_ | psubFV x v (strengthen ps rs) == strengthen (psubFV x v ps) (psubFV x v rs) } @-}
lem_psubFV_strengthen :: Vname -> Expr -> Preds -> Preds -> Proof
lem_psubFV_strengthen x v PEmpty       rs = ()
lem_psubFV_strengthen x v (PCons p ps) rs = () ? lem_psubFV_strengthen x v ps rs

{-@ lem_psubFTV_strengthen :: a:Vname -> t_a:UserType -> ps:Preds -> rs:Preds
        -> { pf:_ | psubFTV a t_a (strengthen ps rs) == strengthen (psubFTV a t_a ps) (psubFTV a t_a rs) } @-}
lem_psubFTV_strengthen :: Vname -> Type -> Preds -> Preds -> Proof
lem_psubFTV_strengthen a t_a PEmpty       rs = ()
lem_psubFTV_strengthen a t_a (PCons p ps) rs = () ? lem_psubFTV_strengthen a t_a ps rs

{-@ lem_unbindP_strengthen :: y:Vname -> ps:Preds -> rs:Preds
        -> { pf:_ | unbindP y (strengthen ps rs) == strengthen (unbindP y ps) (unbindP y rs) } @-}
lem_unbindP_strengthen :: Vname -> Preds -> Preds -> Proof
lem_unbindP_strengthen y PEmpty       rs = ()
lem_unbindP_strengthen y (PCons p ps) rs = () ? lem_unbindP_strengthen y ps rs

{-@ lem_openP_at_strengthen :: j:Index -> y:Vname -> ps:Preds -> rs:Preds
        -> { pf:_ | openP_at j y (strengthen ps rs) == strengthen (openP_at j y ps) (openP_at j y rs) } @-}
lem_openP_at_strengthen :: Index -> Vname -> Preds -> Preds -> Proof
lem_openP_at_strengthen j y PEmpty       rs = ()
lem_openP_at_strengthen j y (PCons p ps) rs = () ? lem_openP_at_strengthen j y ps rs

{-@ lem_psubBV_strengthen :: v:Value -> ps:Preds -> rs:Preds
        -> { pf:_ | psubBV v (strengthen ps rs) == strengthen (psubBV v ps) (psubBV v rs) } @-}
lem_psubBV_strengthen :: Expr -> Preds -> Preds -> Proof
lem_psubBV_strengthen v PEmpty       rs = () 
lem_psubBV_strengthen v (PCons p ps) rs = () ? lem_psubBV_strengthen v ps rs
 
{-@ lem_psubBV_at_strengthen :: j:Index -> v:Value -> ps:Preds -> rs:Preds
        -> { pf:_ | psubBV_at j v (strengthen ps rs) == strengthen (psubBV_at j v ps) (psubBV_at j v rs) } @-}
lem_psubBV_at_strengthen :: Index -> Expr -> Preds -> Preds -> Proof
lem_psubBV_at_strengthen j v PEmpty       rs = () 
lem_psubBV_at_strengthen j v (PCons p ps) rs = () ? lem_psubBV_at_strengthen j v ps rs
 
{-@ lem_open_tvP_at_strengthen :: j:Index -> a':Vname -> ps:Preds -> rs:Preds
        -> { pf:_ | open_tvP_at j a' (strengthen ps rs) == 
                         strengthen (open_tvP_at j a' ps) (open_tvP_at j a' rs) } @-}
lem_open_tvP_at_strengthen :: Index -> Vname -> Preds -> Preds -> Proof
lem_open_tvP_at_strengthen j a' PEmpty       rs = ()
lem_open_tvP_at_strengthen j a' (PCons p ps) rs = () ? lem_open_tvP_at_strengthen j a' ps rs

{-@ lem_psubBTV_strengthen :: t_a:Type -> ps:Preds -> rs:Preds
        -> { pf:_ | psubBTV t_a (strengthen ps rs) == strengthen (psubBTV t_a ps) (psubBTV t_a rs) } @-}
lem_psubBTV_strengthen :: Type -> Preds -> Preds -> Proof
lem_psubBTV_strengthen t_a PEmpty       rs = () 
lem_psubBTV_strengthen t_a (PCons p ps) rs = () ? lem_psubBTV_strengthen t_a ps rs

{-@ lem_psubBTV_at_strengthen :: j:Index -> t_a:Type -> ps:Preds -> rs:Preds
      -> {pf:_ | psubBTV_at j t_a (strengthen ps rs) == strengthen (psubBTV_at j t_a ps) (psubBTV_at j t_a rs)} @-}
lem_psubBTV_at_strengthen :: Index -> Type -> Preds -> Preds -> Proof
lem_psubBTV_at_strengthen j t_a PEmpty       rs = () 
lem_psubBTV_at_strengthen j t_a (PCons p ps) rs = () ? lem_psubBTV_at_strengthen j t_a ps rs
