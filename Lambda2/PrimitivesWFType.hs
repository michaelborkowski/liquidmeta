{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFType where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import PrimitivesWFTypeAnd
import PrimitivesWFTypeOr
import PrimitivesWFTypeNot
import PrimitivesWFTypeEqv 
import PrimitivesWFTypeLeq
import PrimitivesWFTypeLeqn
import PrimitivesWFTypeEq
import PrimitivesWFTypeEqn

{-@ reflect foo15 @-}
foo15 :: a -> Maybe a
foo15 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant Types
{-@ automatic-instances lem_wf_tybc @-}
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b) Base) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = WFRefn g 1 TBool pred y pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (BV 1)) (Bc b)) 
     y          = (fresh_var g)
     g'         = (FCons y (FTBasic TBool) (erase_env g))
     pf_eqv_v   = FTApp g' (Prim Eqv) (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool)) 
                           (FTPrm g' Eqv) (FV y) (FTVar1 (erase_env g) y (FTBasic TBool))
     -- pf_pr_bool :: ProofOf(HasFType g' pred (FTBasic TBool)) @- }
     pf_pr_bool = FTApp g' (App (Prim Eqv) (FV y)) (FTBasic TBool) (FTBasic TBool) 
                           pf_eqv_v (Bc b) (FTBC g' b)

{-@ automatic-instances lem_wf_tyic @-}
{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n) Base) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = WFRefn g 1 TInt pred y pf_pr_bool
  where
    pred        = (App (App (Prim Eq) (BV 1)) (Ic n))
    y           = fresh_var g
    g'          = (FCons y (FTBasic TInt) (erase_env g))
    pf_eq_v     = FTApp g' (Prim Eq) (FTBasic TInt) (FTFunc (FTBasic TInt) (FTBasic TBool)) 
                           (FTPrm g' Eq) (FV y) (FTVar1 (erase_env g) y (FTBasic TInt))
    pf_pr_bool  = FTApp g' (App (Prim Eq) (FV y)) (FTBasic TInt) (FTBasic TBool) 
                           pf_eq_v (Ic n) (FTIC g' n)


{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c) Star) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And) Star      ? lem_wf_ty_and 
lem_wf_ty Or       = makeWFType Empty (ty Or) Star       ? lem_wf_ty_or
lem_wf_ty Not      = makeWFType Empty (ty Not) Star      ? lem_wf_ty_not
lem_wf_ty Eqv      = makeWFType Empty (ty Eqv) Star      ? lem_wf_ty_eqv
lem_wf_ty Leq      = makeWFType Empty (ty Leq) Star      ? lem_wf_ty_leq
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) Star ? lem_wf_ty_leqn n
lem_wf_ty Eq       = makeWFType Empty (ty Eq) Star       ? lem_wf_ty_eq
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n)) Star  ? lem_wf_ty_eqn n

