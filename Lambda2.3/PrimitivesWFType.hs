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
import SystemFWellFormedness            --(WFFT(..),isWFFT)
import SystemFTyping                    --(HasFType(..),firstBV,inType,ty',refn_pred,ty,erase_ty,
                                        --  noDefnsBaseAppT,checkType,synthType,tybc,tyic)
import CheckSynth
import WellFormedness                   --(WFType(..),noDefnsInRefns,isWellFormed,makeWFType)
import PrimitivesFTyping                --(isEql)

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
lem_wf_tybc g b = makeWFType g (tybc b) Base

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n) Base) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = makeWFType g (tyic n) Base

{-
{-@ lem_wf_intype :: { c:Prim | not (isPoly c) } -> ProofOf(WFType Empty (inType c) Base) @-}
lem_wf_intype :: Prim -> WFType
lem_wf_intype And      = makeWFType Empty (inType And)      Base 
lem_wf_intype Or       = makeWFType Empty (inType Or)       Base 
lem_wf_intype Not      = makeWFType Empty (inType Not)      Base 
lem_wf_intype Imp      = makeWFType Empty (inType Imp)      Base 
lem_wf_intype Eqv      = makeWFType Empty (inType Eqv)      Base 
lem_wf_intype Leq      = makeWFType Empty (inType Leq)      Base 
lem_wf_intype (Leqn n) = makeWFType Empty (inType (Leqn n)) Base 
lem_wf_intype Eq       = makeWFType Empty (inType Eq)       Base 
lem_wf_intype (Eqn n)  = makeWFType Empty (inType (Eqn n))  Base 
{-lem_wf_intype (Eql a)  = makeWFType Empty (inType (Eql a))  Base ? lem_wf_intype_eql  a
                                                                 ? lem_wf_intype_eql' a-}

{-@ lem_wf_ty' :: { c:Prim | not (isPoly c) } -> y:Vname
        -> ProofOf(WFType (Cons y (inType c) Empty) (unbindT y (ty' c)) Star) @-}
lem_wf_ty' :: Prim -> Vname -> WFType
lem_wf_ty' And      y = makeWFType (Cons y (inType And) Empty) (unbindT y (ty' And)) Star 
lem_wf_ty' Or       y = makeWFType (Cons y (inType Or)  Empty) (unbindT y (ty' Or))  Star
lem_wf_ty' Not      y = makeWFType (Cons y (inType Not) Empty) (unbindT y (ty' Not)) Star 
lem_wf_ty' Imp      y = makeWFType (Cons y (inType Imp) Empty) (unbindT y (ty' Imp)) Star 
lem_wf_ty' Eqv      y = makeWFType (Cons y (inType Eqv) Empty) (unbindT y (ty' Eqv)) Star 
lem_wf_ty' Leq      y = makeWFType (Cons y (inType Leq) Empty) (unbindT y (ty' Leq)) Star 
lem_wf_ty' (Leqn n) y = makeWFType (Cons y (inType (Leqn n)) Empty) (unbindT y (ty' (Leqn n))) Star
lem_wf_ty' Eq       y = makeWFType (Cons y (inType Eq)  Empty) (unbindT y (ty' Eq))  Star 
lem_wf_ty' (Eqn n) y  = makeWFType (Cons y (inType (Eqn n)) Empty) (unbindT y (ty' (Eqn n))) Star 
-}
{-
{-@ lem_wf_inside_ty :: a':Vname 
        -> ProofOf(WFType (ConsT a' Base Empty) 
                          (unbind_tvT 1 a' (TFunc (firstBV Eql) (inType Eql) (ty' Eql))) Star) @-}
lem_wf_inside_ty :: Vname -> WFType
lem_wf_inside_ty a' = makeWFType (ConsT a' Base Empty) 
                                 (unbind_tvT 1 a' (TFunc (firstBV Eql) (inType Eql) (ty' Eql)))
                                 Star ? lem_wf_ty_inside_eql a'
-}
{-@ lem_wf_ty :: c:Prim -> ProofOf(WFType Empty (ty c) Star) @-}
lem_wf_ty :: Prim -> WFType
lem_wf_ty And      = makeWFType Empty (ty And) Star   
lem_wf_ty Or       = makeWFType Empty (ty Or) Star     
lem_wf_ty Not      = makeWFType Empty (ty Not) Star    
lem_wf_ty Imp      = makeWFType Empty (ty Imp) Star
lem_wf_ty Eqv      = makeWFType Empty (ty Eqv) Star    
lem_wf_ty Leq      = makeWFType Empty (ty Leq) Star    
lem_wf_ty (Leqn n) = makeWFType Empty (ty (Leqn n)) Star 
lem_wf_ty Eq       = makeWFType Empty (ty Eq) Star      
lem_wf_ty (Eqn n)  = makeWFType Empty (ty (Eqn n)) Star 
lem_wf_ty Leql     = makeWFType Empty (ty Leql) Star    
lem_wf_ty Eql      = makeWFType Empty (ty Eql) Star     
