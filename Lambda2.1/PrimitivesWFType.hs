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
import PrimitivesWFTypeEql

{-@ reflect foo19 @-}
foo19 :: a -> Maybe a
foo19 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant Types
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b) Base) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = WFRefn g Z TBool (Bc True) (WFBase g TBool (Bc True)) pred y pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (BV 0)) (Bc b)) 
     y          = (fresh_var g)
     g'         = (FCons y (FTBasic TBool) (erase_env g))
     pf_eqv_v   = FTApp g' (Prim Eqv) (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool)) 
                           (FTPrm g' Eqv) (FV y) (FTVar1 (erase_env g) y (FTBasic TBool))
     -- pf_pr_bool :: ProofOf(HasFType g' pred (FTBasic TBool)) @- }
     pf_pr_bool = FTApp g' (App (Prim Eqv) (FV y)) (FTBasic TBool) (FTBasic TBool) 
                           pf_eqv_v (Bc b) (FTBC g' b)

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n) Base) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = WFRefn g Z TInt (Bc True) (WFBase g TInt (Bc True)) pred y pf_pr_bool
  where
    pred        = (App (App (Prim Eq) (BV 0)) (Ic n))
    y           = fresh_var g
    g'          = (FCons y (FTBasic TInt) (erase_env g))
    pf_eq_v     = FTApp g' (Prim Eq) (FTBasic TInt) (FTFunc (FTBasic TInt) (FTBasic TBool)) 
                           (FTPrm g' Eq) (FV y) (FTVar1 (erase_env g) y (FTBasic TInt))
    pf_pr_bool  = FTApp g' (App (Prim Eq) (FV y)) (FTBasic TInt) (FTBasic TBool) 
                           pf_eq_v (Ic n) (FTIC g' n)

{-@ lem_wf_intype :: { c:Prim | not (isEql c) } -> ProofOf(WFType Empty (inType c) Base) @-}
lem_wf_intype :: Prim -> WFType
lem_wf_intype And      = makeWFType Empty (inType And)      Base ? lem_wf_intype_and ()
lem_wf_intype Or       = makeWFType Empty (inType Or)       Base ? lem_wf_intype_or ()
lem_wf_intype Not      = makeWFType Empty (inType Not)      Base ? lem_wf_intype_not ()
lem_wf_intype Eqv      = makeWFType Empty (inType Eqv)      Base ? lem_wf_intype_eqv ()
lem_wf_intype Leq      = makeWFType Empty (inType Leq)      Base ? lem_wf_intype_leq ()
lem_wf_intype (Leqn n) = makeWFType Empty (inType (Leqn n)) Base ? lem_wf_intype_leqn n
lem_wf_intype Eq       = makeWFType Empty (inType Eq)       Base ? lem_wf_intype_eq ()
lem_wf_intype (Eqn n)  = makeWFType Empty (inType (Eqn n))  Base ? lem_wf_intype_eqn n
{-lem_wf_intype (Eql a)  = makeWFType Empty (inType (Eql a))  Base ? lem_wf_intype_eql  a
                                                                 ? lem_wf_intype_eql' a-}

{-@ lem_wf_ty' :: { c:Prim | not (isEql c) } -> y:Int 
        -> ProofOf(WFType (Cons y (inType c) Empty) (unbindT (firstBV c) y (ty' c)) Star) @-}
lem_wf_ty' :: Prim -> Int -> WFType
lem_wf_ty' And      y = makeWFType (Cons y (inType And) Empty) (unbindT (firstBV And) y (ty' And)) 
                                   Star ? lem_wf_ty'_and y
lem_wf_ty' Or       y = makeWFType (Cons y (inType Or)  Empty) (unbindT (firstBV Or)  y (ty' Or)) 
                                   Star ? lem_wf_ty'_or y
lem_wf_ty' Not      y = makeWFType (Cons y (inType Not) Empty) (unbindT (firstBV Not) y (ty' Not)) 
                                   Star ? lem_wf_ty'_not y
lem_wf_ty' Eqv      y = makeWFType (Cons y (inType Eqv) Empty) (unbindT (firstBV Eqv) y (ty' Eqv)) 
                                   Star ? lem_wf_ty'_eqv y
lem_wf_ty' Leq      y = makeWFType (Cons y (inType Leq) Empty) (unbindT (firstBV Leq) y (ty' Leq)) 
                                   Star ? lem_wf_ty'_leq y
lem_wf_ty' (Leqn n) y = makeWFType (Cons y (inType (Leqn n)) Empty) 
                                   (unbindT (firstBV (Leqn n)) y (ty' (Leqn n))) 
                                   Star ? lem_wf_ty'_leqn n y
lem_wf_ty' Eq       y = makeWFType (Cons y (inType Eq)  Empty) (unbindT (firstBV Eq)  y (ty' Eq)) 
                                   Star ? lem_wf_ty'_eq y
lem_wf_ty' (Eqn n) y  = makeWFType (Cons y (inType (Eqn n)) Empty) 
                                   (unbindT (firstBV (Eqn n)) y (ty' (Eqn n))) 
                                   Star ? lem_wf_ty'_eqn n y        

{-@ lem_wf_inside_ty :: a':Vname 
        -> ProofOf(WFType (ConsT a' Base Empty) 
                          (unbind_tvT 1 a' (TFunc (firstBV Eql) (inType Eql) (ty' Eql))) Star) @-}
lem_wf_inside_ty :: Vname -> WFType
lem_wf_inside_ty a' = makeWFType (ConsT a' Base Empty) 
                                 (unbind_tvT 1 a' (TFunc (firstBV Eql) (inType Eql) (ty' Eql)))
                                 Star ? lem_wf_ty_inside_eql a'

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c) Star) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And) Star      ? lem_wf_ty_and ()
lem_wf_ty Or       = makeWFType Empty (ty Or) Star       ? lem_wf_ty_or ()
lem_wf_ty Not      = makeWFType Empty (ty Not) Star      ? lem_wf_ty_not ()
lem_wf_ty Eqv      = makeWFType Empty (ty Eqv) Star      ? lem_wf_ty_eqv ()
lem_wf_ty Leq      = makeWFType Empty (ty Leq) Star      ? lem_wf_ty_leq ()
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) Star ? lem_wf_ty_leqn n
lem_wf_ty Eq       = makeWFType Empty (ty Eq) Star       ? lem_wf_ty_eq ()
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n)) Star  ? lem_wf_ty_eqn n
lem_wf_ty Eql      = makeWFType Empty (ty Eql) Star      ? lem_wf_ty_eql ()
