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

{-@ reflect foo19 @-}
foo19 :: a -> Maybe a
foo19 x = Just x

-----------------------------------------------------------------------------
-- | Properties of BUILT-IN PRIMITIVES
-----------------------------------------------------------------------------

-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Constant Types
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b)) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = WFRefn g 1 TBool pred y pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (BV 1)) (Bc b)) 
     y          = (fresh_var g)
     g'         = (FCons y (FTBasic TBool) (erase_env g))
     pf_eqv_v   = FTApp g' (Prim Eqv) (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool)) 
                           (FTPrm g' Eqv) (FV y) (FTVar1 (erase_env g) y (FTBasic TBool))
     pf_pr_bool = FTApp g' (App (Prim Eqv) (FV y)) (FTBasic TBool) (FTBasic TBool) 
                           pf_eqv_v (Bc b) (FTBC g' b)

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n)) @-}
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

{-@ lem_wf_intype :: c:Prim -> ProofOf(WFType Empty (inType c)) @-}
lem_wf_intype :: Prim -> WFType
lem_wf_intype And      = makeWFType Empty (inType And)      ? lem_wf_intype_and ()
lem_wf_intype Or       = makeWFType Empty (inType Or)       ? lem_wf_intype_or ()
lem_wf_intype Not      = makeWFType Empty (inType Not)      ? lem_wf_intype_not ()
lem_wf_intype Eqv      = makeWFType Empty (inType Eqv)      ? lem_wf_intype_eqv ()
lem_wf_intype Leq      = makeWFType Empty (inType Leq)      ? lem_wf_intype_leq ()
lem_wf_intype (Leqn n) = makeWFType Empty (inType (Leqn n)) ? lem_wf_intype_leqn n
lem_wf_intype Eq       = makeWFType Empty (inType Eq)       ? lem_wf_intype_eq ()
lem_wf_intype (Eqn n)  = makeWFType Empty (inType (Eqn n))  ? lem_wf_intype_eqn n

{-@ lem_wf_ty' :: c:Prim -> y:Int 
        -> ProofOf(WFType (Cons y (inType c) Empty) (unbindT (firstBV c) y (ty' c))) @-}
lem_wf_ty' :: Prim -> Int -> WFType
lem_wf_ty' And      y = makeWFType (Cons y (inType And) Empty) (unbindT (firstBV And) y (ty' And)) 
                                   ? lem_wf_ty'_and y
lem_wf_ty' Or       y = makeWFType (Cons y (inType Or)  Empty) (unbindT (firstBV Or)  y (ty' Or)) 
                                   ? lem_wf_ty'_or y
lem_wf_ty' Not      y = makeWFType (Cons y (inType Not) Empty) (unbindT (firstBV Not) y (ty' Not)) 
                                   ? lem_wf_ty'_not y
lem_wf_ty' Eqv      y = makeWFType (Cons y (inType Eqv) Empty) (unbindT (firstBV Eqv) y (ty' Eqv)) 
                                   ? lem_wf_ty'_eqv y
lem_wf_ty' Leq      y = makeWFType (Cons y (inType Leq) Empty) (unbindT (firstBV Leq) y (ty' Leq)) 
                                   ? lem_wf_ty'_leq y
lem_wf_ty' (Leqn n) y = makeWFType (Cons y (inType (Leqn n)) Empty) 
                                   (unbindT (firstBV (Leqn n)) y (ty' (Leqn n))) 
                                   ? lem_wf_ty'_leqn n y
lem_wf_ty' Eq       y = makeWFType (Cons y (inType Eq)  Empty) (unbindT (firstBV Eq)  y (ty' Eq)) 
                                   ? lem_wf_ty'_eq y
lem_wf_ty' (Eqn n) y  = makeWFType (Cons y (inType (Eqn n)) Empty) 
                                   (unbindT (firstBV (Eqn n)) y (ty' (Eqn n))) 
                                   ? lem_wf_ty'_eqn n y        

{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c)) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And)      ? lem_wf_ty_and ()
lem_wf_ty Or       = makeWFType Empty (ty Or)       ? lem_wf_ty_or ()
lem_wf_ty Not      = makeWFType Empty (ty Not)      ? lem_wf_ty_not ()
lem_wf_ty Eqv      = makeWFType Empty (ty Eqv)      ? lem_wf_ty_eqv ()
lem_wf_ty Leq      = makeWFType Empty (ty Leq)      ? lem_wf_ty_leq ()
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) ? lem_wf_ty_leqn n
lem_wf_ty Eq       = makeWFType Empty (ty Eq)       ? lem_wf_ty_eq ()
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n))  ? lem_wf_ty_eqn n
