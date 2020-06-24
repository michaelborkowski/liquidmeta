{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}      -- TODO: assume
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesWFType where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import PrimitivesWFTypeAnd
import PrimitivesWFTypeOr
import PrimitivesWFTypeNot
--import PrimitivesWFTypeEqv   TODO: this one still segfaulting, assume for now
import PrimitivesWFTypeLeq
import PrimitivesWFTypeLeqn
import PrimitivesWFTypeEq
import PrimitivesWFTypeEqn

semantics = (\e e' -> Step e e', \e e' -> EvalsTo e e', \e e' -> AppReduced e e')
typing = (TInt, TBool, \g e t -> HasFType g e t, \g t -> WFType g t, \g -> WFEnv g)

{-@ reflect foo14 @-}
foo14 :: a -> Maybe a
foo14 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------


-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant Types
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

{-@ lem_ty_iswellformed :: c:Prim -> { pf:_ | isWellFormed Empty (ty c) Star && noDefnsInRefns Empty (ty c)
                                                    && Set_emp (free (ty c)) && Set_emp (freeTV (ty c)) } @-}
lem_ty_iswellformed :: Prim -> Proof
lem_ty_iswellformed And       = lem_wf_ty_and
lem_ty_iswellformed Or        = lem_wf_ty_or
lem_ty_iswellformed Not       = lem_wf_ty_not
--lem_ty_iswellformed Eqv       = lem_wf_ty_eqv
lem_ty_iswellformed Leq       = lem_wf_ty_leq
lem_ty_iswellformed (Leqn n)  = lem_wf_ty_leqn n
lem_ty_iswellformed Eq        = lem_wf_ty_eq
lem_ty_iswellformed (Eqn n)   = lem_wf_ty_eqn n

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c) Star) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And) Star      ? lem_ty_iswellformed And
lem_wf_ty Or       = makeWFType Empty (ty Or)  Star      ? lem_ty_iswellformed Or
lem_wf_ty Not      = makeWFType Empty (ty Not) Star      ? lem_ty_iswellformed Not
--lem_wf_ty Eqv      = makeWFType Empty (ty Eqv) Star      ? lem_ty_iswellformed Eqv
lem_wf_ty Leq      = makeWFType Empty (ty Leq) Star      ? lem_ty_iswellformed Leq
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) Star ? lem_ty_iswellformed (Leqn n)
lem_wf_ty Eq       = makeWFType Empty (ty Eq)  Star      ? lem_ty_iswellformed Eq
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n))  Star ? lem_ty_iswellformed (Eqn n)

