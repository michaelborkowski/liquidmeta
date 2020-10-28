{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDeltaTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
import PrimitivesWFType
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF
import LemmasWellFormedness
import LemmasTyping
import LemmasSubtyping
import LemmasChangeVarTyp
import LemmasWeakenTyp
import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations
import DenotationsSoundnessTyp
import LemmasExactness
import SubstitutionLemmaEnt
import SubstitutionLemmaTyp
import LemmasSubtypeClosed
import LemmasInvertLambda
import PrimitivesRefinements

{-@ reflect foo61 @-}
foo61 x = Just x
foo61 :: a -> Maybe a

{-

  -- Lemmas to explicitly characterize the possible closing substitutions of certain environments.

{-@ lem_den_env_bl :: th:CSub -> ProofOf(DenotesEnv (Cons 1 (TRefn TBool 2 (Bc True)) Empty) th)
        -> { pf:_ | th == CCons 1 (Bc True) CEmpty || th == CCons 1 (Bc False) CEmpty } @-}
lem_den_env_bl :: CSub -> DenotesEnv -> Proof
lem_den_env_bl th (DExt _ _ _ x t v den_tht_v) = undefined
{- PROBABLY OK = case th of
  (CCons 1 v CEmpty) -> () ? lem_bool_values v pf_v_er_t 
    where
      pf_v_er_t = get_ftyp_from_den (ctsubst th t) v den_tht_v ? lem_ctsubst_refn th TBool 2 (Bc True)
-}
{-@ lem_den_env_blbl :: th:CSub -> ProofOf(DenotesEnv (Cons 3 (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (FV 1)))
                                                          (Cons 1 (TRefn TBool 2 (Bc True)) Empty)) th)
        -> { pf:_ | th == CCons 3 (Bc True)  (CCons 1 (Bc True)  CEmpty) ||
                    th == CCons 3 (Bc False) (CCons 1 (Bc False) CEmpty) } @-}
lem_den_env_blbl :: CSub -> DenotesEnv -> Proof
lem_den_env_blbl = undefined
{-
lem_den_env_blbl th (DExt g' th' den_g'_th' _ _ v3 den_th't3_v3) = case den_th't3_v3 of 
  (DRefn _ _ _ _v3 pf_v_er_t3 ev_th'p3v3_tt) -> case th' of
    (CCons _ v2 CEmpty) -> case (v2 == v3) of 
      True  -> () ? lem_den_env_bl th' den_g'_th' -- bottom value is true or false
      False -> impossible ("by lemma" ? lem_evals_val_det th'p3v3 (Bc True)  ev_th'p3v3_tt 
                                                                  (Bc False) ev_th'p3v3_ff)
        where
          p3      = App (App (Prim Eqv) (BV 3)) (FV 1)
          th'p3v3 = subBV 3 v3 (csubst th' p3)
          (Bc b2) = v2 ? toProof ( ctsubst CEmpty t2 === TRefn TBool 2 (Bc True) )
                       ? toProof ( erase (ctsubst CEmpty t2) === BTBase TBool )
                       ? lem_bool_values v2 (get_btyp_from_den (TRefn TBool 2 (Bc True)) v2 den_t2_v2)
          (Bc b3) = v3 ? lem_bool_values v3 pf_v_er_t3
          (DExt _ th'' _ _ t2 _v2 den_t2_v2) = den_g'_th' 
                       ? toProof ( g' === Cons 1 (TRefn TBool 2 (Bc True)) Empty )
          ev_th'p3v3_1  = reduce_eqv b3 b2 
          ev_th'p3v3_ff = AddStep (App (App (Prim Eqv) v3) v2) (App (delta Eqv v3) v2)
                                  (EApp1 (App (Prim Eqv) v3) (delta Eqv v3) (EPrim Eqv v3) v2)
                                  (Bc (blIff b3 b2)) ev_th'p3v3_1
            ? toProof ( subBV 3 v3 (csubst th' (App (App (Prim Eqv) (BV 3)) (FV 1))) 
                      ? lem_csubst_app th' (App (Prim Eqv) (BV 3)) (FV 1)
                      ? lem_csubst_app th' (Prim Eqv) (BV 3)
                      ? lem_csubst_prim th' Eqv
                      ? lem_csubst_bv th' 3
                    === subBV 3 v3 (App (App (Prim Eqv) (BV 3)) (csubst th' (FV 1)))
                    === subBV 3 v3 (App (App (Prim Eqv) (BV 3)) (csubst CEmpty (subFV 1 v2 (FV 1))))
                    === subBV 3 v3 (App (App (Prim Eqv) (BV 3)) v2)
                    === (App (App (Prim Eqv) v3) v2) )
            ? toProof ( b3 === not b2 )
            ? toProof ( blIff b3 b2 === False )
-}

{-@ lem_den_env_ffbl :: th:CSub 
        -> ProofOf(DenotesEnv (Cons 3 (TRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc False)))
                                                          (Cons 1 (TRefn TBool 2 (Bc True)) Empty)) th)
        -> { pf:_ | th == CCons 3 (Bc False) (CCons 1 (Bc True)  CEmpty) ||
                    th == CCons 3 (Bc False) (CCons 1 (Bc False) CEmpty) } @-}
lem_den_env_ffbl :: CSub -> DenotesEnv -> Proof
lem_den_env_ffbl = undefined {-
lem_den_env_ffbl th (DExt g' th' den_g'_th' _ _ v3 den_th't3_v3) = case den_th't3_v3 of 
  (DRefn _ _ _ _v3 pf_v_er_t3 ev_th'p3v3_tt) -> case th' of
    (CCons _ v2 CEmpty) -> case (v3 == False) of 
      True  -> () ? lem_den_env_bl th' den_g'_th' -- bottom value is true or false
      False -> impossible ("by lemma" ? lem_evals_val_det th'p3v3 (Bc True)  ev_th'p3v3_tt 
                                                                  (Bc False) ev_th'p3v3_ff)
        where
          p3      = App (App (Prim Eqv) (BV 1)) (Bc False)
          th'p3v3 = subBV 1 v3 (csubst th' p3)

          (Bc b2) = v2 ? toProof ( ctsubst CEmpty t2 === TRefn TBool 2 (Bc True) )
                       ? toProof ( erase (ctsubst CEmpty t2) === BTBase TBool )
                       ? lem_bool_values v2 (get_btyp_from_den (TRefn TBool 2 (Bc True)) v2 den_t2_v2)
          (Bc b3) = v3 ? lem_bool_values v3 pf_v_er_t3
          (DExt _ th'' _ _ t2 _v2 den_t2_v2) = den_g'_th' 
                       ? toProof ( g' === Cons 1 (TRefn TBool 2 (Bc True)) Empty )
          ev_th'p3v3_1  = reduce_eqv b3 b2 
          ev_th'p3v3_ff = AddStep (App (App (Prim Eqv) v3) v2) (App (delta Eqv v3) v2)
                                  (EApp1 (App (Prim Eqv) v3) (delta Eqv v3) (EPrim Eqv v3) v2)
                                  (Bc (blIff b3 b2)) ev_th'p3v3_1
            ? toProof ( subBV 3 v3 (csubst th' (App (App (Prim Eqv) (BV 3)) (FV 1))) 
                      ? lem_csubst_app th' (App (Prim Eqv) (BV 3)) (FV 1)
                      ? lem_csubst_app th' (Prim Eqv) (BV 3)
                      ? lem_csubst_prim th' Eqv
                      ? lem_csubst_bv th' 3
                    === subBV 3 v3 (App (App (Prim Eqv) (BV 3)) (csubst th' (FV 1)))
                    === subBV 3 v3 (App (App (Prim Eqv) (BV 3)) (csubst CEmpty (subFV 1 v2 (FV 1))))
                    === subBV 3 v3 (App (App (Prim Eqv) (BV 3)) v2)
                    === (App (App (Prim Eqv) v3) v2) )
            ? toProof ( b3 === not b2 )
            ? toProof ( blIff b3 b2 === False )
-}

-- ----------------------------- 16 Step Plan -------------------------------------------------------------
-- --------------------------------------------------------------------------------------------------------

-- for reference: ty And      = TFunc 1 (TRefn TBool 1 (Bc True))
--                   (TFunc 2 (TRefn TBool 2 (Bc True))                                                                                          (TRefn TBool 3                                                                                                              (App (App (Prim Eqv) (BV 3))
--                                (App (App (Prim And) (BV 1)) (BV 2)) )))   ...... (Bc True) (FV 1)a
--
--  --i.e.--  (TRefn TBool 3 (App (App (Prim Eqv) (BV 3))
--                                (App (App (Prim And) (Bc True)) (FV 1))))

-- First wave of lemmas:               need change of vars!
-- 1:Bool{2:tt}, 3:Bool{3:(BV3)=(FV1)} |-e (FV 3) `Eqv` (True `And` (FV 1))
{-@ entails_refn_and_true :: ProofOf(Entails (Cons 3 (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (FV 1)))
                                               (Cons 1 (TRefn TBool 2 (Bc True)) Empty))
        (App (App (Prim Eqv) (FV 3)) (App (App (Prim And) (Bc True)) (FV 1))) ) @-}
entails_refn_and_true :: Entails
entails_refn_and_true = undefined
{-
entails_refn_and_true = EntPred g refnand ev_func
  where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv g th)
                             -> ProofOf(EvalsTo (csubst th refnand) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g_th = case th of
      (CCons 3 (Bc b)  (CCons 1 (Bc b')  CEmpty)) -> ev_threfn_tt    -- we must have b == b'
           where
             {-@ th_refnand :: { q:Pred | q == csubst th refnand } @-}
             th_refnand   = App (App (Prim Eqv) (Bc b)) (App (App (Prim And) (Bc True)) (Bc b'))
                              ? lem_csubst_app th (App (Prim Eqv) (FV 3)) (App (App (Prim And) (Bc True)) (FV 1))
                              ? lem_csubst_app th (Prim Eqv) (FV 3)
                              ? lem_csubst_prim th Eqv
                              ? lem_csubst_app th (App (Prim And) (Bc True)) (FV 1)
                              ? lem_csubst_app th (Prim And) (Bc True)
                              ? lem_csubst_prim th And
                              ? lem_csubst_bc th True
             --b            = Bc True
             {-@ ev_threfn_tt :: ProofOf(EvalsTo th_refnand (Bc True)) @-}
             ev_threfn_tt = lemma_semantics_refn_and True b b ? lem_den_env_blbl th den_g_th
                                                              ? toProof ( th_refnand === csubst th refnand ) 
      _ -> impossible ("by lemma" ? lem_den_env_blbl th den_g_th)
    g               = Cons 3 (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (FV 1))) 
                        (Cons 1 (TRefn TBool 2 (Bc True)) Empty)
    refnand         = App (App (Prim Eqv) (FV 3)) (App (App (Prim And) (Bc True)) (FV 1))
-}
  -- BV nuimnbers???
{-@ entails_refn_and_false :: ProofOf(Entails (Cons 3 (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (Bc False)))
                                               (Cons 1 (TRefn TBool 2 (Bc True)) Empty))
        (App (App (Prim Eqv) (FV 3)) (App (App (Prim And) (Bc False)) (FV 1))) ) @-}
entails_refn_and_false :: Entails
entails_refn_and_false = undefined
{-
entails_refn_and_false = EntPred g refnand ev_func -- TODO: haven't done this one yet
  where
    {-@ ev_func :: th:CSub -> ProofOf(DenotesEnv g th)
                             -> ProofOf(EvalsTo (csubst th refnand) (Bc True)) @-}
    ev_func :: CSub -> DenotesEnv -> EvalsTo
    ev_func th den_g_th = case th of
      (CCons 3 (Bc b)  (CCons 1 (Bc b')  CEmpty)) -> ev_threfn_tt    -- we must have b == b'
           where
             {-@ th_refnand :: { q:Pred | q == csubst th refnand } @-}
             th_refnand   = App (App (Prim Eqv) (Bc b)) (App (App (Prim And) (Bc True)) (Bc b'))
                              ? lem_csubst_app th (App (Prim Eqv) (FV 3)) (App (App (Prim And) (Bc True)) (FV 1))
                              ? lem_csubst_app th (Prim Eqv) (FV 3)
                              ? lem_csubst_prim th Eqv
                              ? lem_csubst_app th (App (Prim And) (Bc True)) (FV 1)
                              ? lem_csubst_app th (Prim And) (Bc True)
                              ? lem_csubst_prim th And
                              ? lem_csubst_bc th True
             --b            = Bc True
             {-@ ev_threfn_tt :: ProofOf(EvalsTo th_refnand (Bc True)) @-}
             ev_threfn_tt = lemma_semantics_refn_and True b b ? lem_den_env_blbl th den_g_th
                                                              ? toProof ( th_refnand === csubst th refnand ) 
      _ -> impossible ("by lemma" ? lem_den_env_blbl th den_g_th)
    g               = Cons 3 (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (FV 1))) 
                        (Cons 1 (TRefn TBool 2 (Bc True)) Empty)
    refnand         = App (App (Prim Eqv) (FV 3)) (App (App (Prim And) (Bc True)) (FV 1))
-}
-- Second show FV 1 is a subtype of sub 1 True (refn_pred And)
{- @ bool_var_typ_refn_and_tt :: ProofOf(HasType (Cons 1 (TRefn TBool 2 (Bc True)) Empty)  (FV 1)
                                                (TRefn TBool 3 (unbind 2 1 (subBV 1 (Bc True) (refn_pred And))))) @-}
{-@ bool_var_typ_refn_and_tt :: ProofOf(HasType (Cons 1 (TRefn TBool 2 (Bc True)) Empty)  (FV 1)
        (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc True)) (FV 1))))) @-}
bool_var_typ_refn_and_tt :: HasType
bool_var_typ_refn_and_tt = undefined
{-
bool_var_typ_refn_and_tt = TSub g (FV 1) type3 p_x_eqlx type4 type4_wf sub_type3_type4
  where
    g               = Cons 1 type2 Empty
    type2           = TRefn TBool 2 (Bc True)  -- Bool{2 : True `And` (} 
    p_x_tt          = TVar1 Empty 1 type2      -- Proof of g |- (FV 1) : self(type2, x)
    pred3           = App (App (Prim Eqv) (BV 3)) (FV 1)
    type3           = TRefn TBool 3 pred3
    type3_wf        = makeWFType g type3
    sub_self2_type3 = lem_self_tt_sub_eql Empty TBool 2 3 1 -- g |- self(type2, x) <: TBool{3 : (BV 3) = (FV 1)}
    {- @ p_x_eqlx :: ProofOf(HasType g (FV 1) (TRefn TBool 3 pred3)) @-}
    p_x_eqlx        = TSub g (FV 1) (self type2 1) p_x_tt type3 type3_wf sub_self2_type3
    
    {- @ pred4 :: { p:Pred | p == App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc True)) (FV 1)) } @-}  
    pred4           = App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc True)) (FV 1))
                      {- unbind 2 1 (subBV 1 (Bc True) (refn_pred And))
                        ? lem_unbind_sub_refn_pred_and True -}
    type4           = TRefn TBool 3 pred4
    type4_wf        = makeWFType g type4
    sub_type3_type4 = SBase g 3 TBool pred3 3 pred4 3 entails_refn_and_true 
-}

-- Then, third, Show using SBase and SFunc to show delta And b has type ty_del(And, b) == tsubFV 1 (Bc b) ty'(c)
-- ?? Emp |- \x. x : (x:Bool -> TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (FV x)))
-- ?? probably need change of vars here

{- @ id_bool_typ_ty'c_tt :: ProofOf(HasType Empty (Lambda 1 (BV 1)) (TFunc 2 (TRefn TBool 2 (Bc True))
                                     (TRefn TBool 3 (subBV 1 (Bc True) (refn_pred And)))) ) @-}
{-@ id_bool_typ_ty'c_tt :: ProofOf(HasType Empty (Lambda 1 (BV 1)) (TFunc 2 (TRefn TBool 2 (Bc True))
               (TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc True)) (BV 2))))) ) @-}
id_bool_typ_ty'c_tt :: HasType
id_bool_typ_ty'c_tt = undefined
{-
id_bool_typ_ty'c_tt = TSub Empty (Lambda 1 (BV 1)) functype_1 p_id_functype_1 
                                                   functype_2 functype_2_wf sub_func1_func2
  where
    type2           = TRefn TBool 2 (Bc True) 
    type2_wf        = makeWFType Empty type2 
    type4           = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc True)) (FV 1)))
--                        ? lem_unbind_sub_refn_pred_and True
    type4_wf        = makeWFType (Cons 1 type2 Empty) type4
    bound_ty1       = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc True)) (BV 1)))
    functype_1      = TFunc 1 type2 bound_ty1
    p_id_functype_1 = TAbs Empty 1 type2 type2_wf (BV 1) bound_ty1 1 bool_var_typ_refn_and_tt
    bound_ty2       = TRefn TBool 3 (App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc True)) (BV 2)))
-- TRefn TBool 3 (subBV 1 (Bc True) (refn_pred And))
    functype_2      = TFunc 2 type2 bound_ty2 -- ? lem_unbind_sub_refn_pred_and True 
    functype_2_wf   = WFFunc Empty 2 type2 type2_wf bound_ty2 1 type4_wf
    sub_func1_func2 = lem_change_bv_sub_func Empty 1 type2 bound_ty1 2 bound_ty2 1 
                        type2_wf type4_wf WFEEmpty
-}

{-    
-- fourth use SBase and SFunc to show delta And b has type ty_del(And, b) == tsubFV 1 (Bc b) ty'(c)
{-@ lem_delta_typ_ty'c :: c:Prim -> v:Value -> ProofOf(HasType Empty v (inType c))
                              -> ProofOf(HasType Empty (delta c v) (tsubBV (firstBV c) v (ty' c))) @-} 
lem_delta_typ_ty'c :: Prim -> Expr -> HasType -> HasType
lem_delta_typ_ty'c And (Bc True) p_v_bl = id_bool_typ_ty'c_tt ? lem_sub_refn_pred_and True
  -}

{-
-- fifth, handle the case of And False

{-@ lem_delta_and_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim And) (TFunc t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta And v) (tsubBV x v t') } @-} 
lem_delta_and_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType

-}



-- eighth, show
-- x:(TRefn TIntl 1 (Bc True)) |- FV x : TRefn TInt 2 (App (App (Prim Eq) (BV 2)) (FV x))
-- by Entailment, SBase and TSub

-- ninth, show
-- Emp |- \x. x : (x:Int -> TRefn TInt 2 (App (App (Prim Eq) (BV 2)) (FV x)) )
--
-- tenth show the entailment for Leq/Eq
--
--
--
-- thirteenth, the refinement type for \x. (App (Prim Not) (BV x))
--
-- fourteenth, the delta __ type lemmas for eqv
--

-}
{-
-- fifteenth, prove lem_prim_sub_tyc
{-@ lem_prim_tyc_sub :: g:Env -> c:Prim -> t:Type -> ProofOf(HasType g (Prim c) t)
                              -> ProofOf(WFEnv g) -> ProofOf(Subtype g (ty c) t) @-}
lem_prim_tyc_sub :: Env -> Prim -> Type -> HasType -> WFEnv -> Subtype
lem_prim_tyc_sub g c t p_c_t p_wf_g = case (lem_typ_lower_bound g (Prim c) t p_wf_g p_c_t) of 
  (LBForType _g _ _t t' p_t'_t p_c_t') -> case p_c_t' of
    (TPrm {}) -> p_t'_t
-}

{-      
lem_prim_tyc_sub g c t (TPrm _ _)                = lem_subtype_refl g t
lem_prim_tyc_sub g c t (TSub _ _ s p_pc_s _ _ _) = () ? lem_prim_tyc_sub g c s p_pc_s
lem_prim_tyc_sub g c t _                         = impossible "no more matches"
-}


{-

--from the other file:
--{-@ lem_sub_refn_pred_and :: b:Bool -> { pf:_ | subBV 1 (Bc b) (refn_pred And)
--                             == App (App (Prim Eqv) (BV 3)) (App (App (Prim And) (Bc b)) (BV 2)) } @-}

-- Empty |- (\x. x)     : 2:Bool{true} -> Bool{3: 3 `eqv` (True `and` 2)}
-- Empty |- (\x. false) : 2:Bool{true} -> Bool{3: 3 `eqv` (False `and` 2)}
{-@ lem_delta_and_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim And) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta And v) (tsubBV x v t') } @-} 
lem_delta_and_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
--lem_delta_and_typ v x t_x t' p_c_txt' p_v_tx = undefined
lem_delta_and_typ v x t_x t' p_c_txt' p_v_tx = undefined
{-
  = case (lem_typ_lower_bound Empty (Prim And) (TFunc x t_x t') WFEEmpty p_c_txt') of --case p_c_txt' of
      (LBForType _ _ _ t' p_t'_t p_c_t') -> 
  (TPrm Empty And) -> case v of
          (Bc True)  -> TAbs Empty 1 (BTBase TBool) (BV 1) (BTBase TBool)
                              1 (BTVar1 BEmpty 1 (BTBase TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))

{-@ lem_delta_and_false_typ :: ProofOf(HasType (delta And (Bc False)) 
            (TFunc 2 (TRefn TBool 5 (Bc True))
                (TRefn TBool 3 (App (App (Prim Eqv) (BV 3))
                                    (App (App (Prim And) (Bc False)) (BV 2)) ))) ) @-}

          (Bc False) -> BTAbs BEmpty 1 (BTBase TBool) (Bc False) (BTBase TBool)
                              1 (BTBC (BCons 1 (BTBase TBool) BEmpty) False)
          _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)
-}



-- sixth, copy paste fix for Prim Or
{-@ lem_delta_or_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim Or) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta Or v) (tsubBV x v t') } @-} 
lem_delta_or_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_or_typ v x t_x t' p_c_txt' p_v_tx = undefined

-- seventh, simplify for Prim Not
{-@ lem_delta_not_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim Not) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta Not v) (tsubBV x v t') } @-} 
lem_delta_not_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_not_typ v x t_x t' p_c_txt' p_v_tx = undefined

{-@ lem_delta_eqv_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim Eqv) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta Eqv v) (tsubBV x v t') } @-} 
lem_delta_eqv_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_eqv_typ v x t_x t' p_c_txt' p_v_tx = undefined

-- eleventh so the lemma for LEq/Eq
{-@ lem_delta_leq_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim Leq) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta Leq v) (tsubBV x v t') } @-} 
lem_delta_leq_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_leq_typ v x t_x t' p_c_txt' p_v_tx = undefined

-- twelvth, figure for Leqn/Eqn
{-@ lem_delta_leqn_typ :: n:Int -> v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim (Leqn n)) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta (Leqn n) v) (tsubBV x v t') } @-} 
lem_delta_leqn_typ :: Int -> Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_leqn_typ n v x t_x t' p_c_txt' p_v_tx = undefined

{-@ lem_delta_eq_typ :: v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim Eq) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta Eq v) (tsubBV x v t') } @-} 
lem_delta_eq_typ :: Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_eq_typ v x t_x t' p_c_txt' p_v_tx = undefined

{-@ lem_delta_eqn_typ :: n:Int -> v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim (Eqn n)) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta (Eqn n) v) (tsubBV x v t') } @-} 
lem_delta_eqn_typ :: Int -> Expr -> Vname -> Type -> Type -> HasType -> HasType -> HasType
lem_delta_eqn_typ n v x t_x t' p_c_txt' p_v_tx = undefined
-}
-- sixteenth fill in the deatils here  -- dont need the refinements on Prim

{-@ lem_delta_ty'c :: { c:Prim | c != Eql } -> v:Value -> ProofOf(HasType Empty v (inType c))
        -> ProofOf(HasType Empty (delta c v) (tsubBV (firstBV c) v (ty' c))) @-}
lem_delta_ty'c :: Prim -> Expr -> HasType -> HasType
lem_delta_ty'c c v p_v_tx = undefined

{-@ lem_delta_typ :: c:Prim -> v:Value -> x:Vname -> t_x:Type -> t':Type
        -> ProofOf(HasType Empty (Prim c) (TFunc x t_x t')) -> ProofOf(HasType Empty v t_x)
        -> { pf:_ | propOf pf == HasType Empty (delta c v) (tsubBV x v t') } @-} 
lem_delta_typ :: Prim -> Expr -> Vname -> Type -> Type 
                     -> HasType -> HasType -> HasType
lem_delta_typ c v x t_x t' p_c_txt' p_v_tx  = undefined {- CHECKED!
  = case (lem_typ_lower_bound Empty (Prim c) (TFunc x t_x t') WFEEmpty p_c_txt') of 
      (LBForType _ _ _ s p_s_t p_c_s) -> case p_c_s of -- s === ty c
          (TPrm Empty _c) -> TSub Empty (delta c v) ty'cv p_cv_ty'cv 
                                  (tsubBV x v t') k' p_emp_t'v p_ty'cv_t'v
            where
              ty'cv       = tsubBV (firstBV c) v (ty' c)
              (WFFunc _ _ _ _ _ _ k' y p_y_t') = lem_typing_wf Empty (Prim c) (TFunc x t_x t') 
                                                               p_c_txt' WFEEmpty
              p_emp_tx    = lem_typing_wf Empty v t_x p_v_tx WFEEmpty
              p_y_wf      = WFEBind Empty WFEEmpty y t_x Star p_emp_tx 
              p_emp_t'v   = lem_subst_wf  Empty Empty y v t_x p_v_tx p_y_wf (unbindT x y t') k' p_y_t'
                                ? lem_tsubFV_unbindT x y v t'
              (SFunc _ _ _ _ _ p_tx_in _ _ z p_z_ty'c_t') = p_s_t
              p_v_in      = TSub Empty v t_x p_v_tx (inType c) Base (lem_wf_intype c) p_tx_in
              p_cv_ty'cv  = lem_delta_ty'c c v p_v_in
              p_z_wf      = WFEBind Empty WFEEmpty z t_x Star p_emp_tx 
              p_z_t'      = lem_change_var_wf Empty y t_x Empty p_y_wf (unbindT x y t') k' p_y_t' z
                                ? lem_tsubFV_unbindT x y (FV z) t'
              p_zin_ty'c  = lem_wf_ty' c z
              p_ztx_ty'c  = lem_subtype_in_env_wf Empty Empty z t_x (inType c) p_tx_in 
                                                  (unbindT (firstBV c) z (ty' c)) Star p_zin_ty'c
              p_ty'cv_t'v = lem_subst_sub Empty Empty z v t_x p_v_tx p_z_wf 
                                          (unbindT (firstBV c) z (ty' c)) Star p_ztx_ty'c 
                                          (unbindT x z t') k' p_z_t'
                                          p_z_ty'c_t' 
                                ? lem_tsubFV_unbindT (firstBV c) z v (ty' c)
                                ? lem_tsubFV_unbindT x           z v t'
-}
{-
lem_delta_typ And      v x t_x t' p_c_txt' p_v_tx = lem_delta_and_typ    v x t_x t' p_c_txt' p_v_tx
lem_delta_typ Or       v x t_x t' p_c_txt' p_v_tx = lem_delta_or_typ     v x t_x t' p_c_txt' p_v_tx
lem_delta_typ Not      v x t_x t' p_c_txt' p_v_tx = lem_delta_not_typ    v x t_x t' p_c_txt' p_v_tx
lem_delta_typ Eqv      v x t_x t' p_c_txt' p_v_tx = lem_delta_eqv_typ    v x t_x t' p_c_txt' p_v_tx
lem_delta_typ Leq      v x t_x t' p_c_txt' p_v_tx = lem_delta_leq_typ    v x t_x t' p_c_txt' p_v_tx
lem_delta_typ (Leqn n) v x t_x t' p_c_txt' p_v_tx = lem_delta_leqn_typ n v x t_x t' p_c_txt' p_v_tx
lem_delta_typ Eq       v x t_x t' p_c_txt' p_v_tx = lem_delta_eq_typ     v x t_x t' p_c_txt' p_v_tx
lem_delta_typ (Eqn n)  v x t_x t' p_c_txt' p_v_tx = lem_delta_eqn_typ  n v x t_x t' p_c_txt' p_v_tx
-}

{-@ lem_deltaT_typ :: c:Prim -> a:Vname -> k:Kind -> s:Type
        -> ProofOf(HasType Empty (Prim c) (TPoly a k s)) -> t:Type -> ProofOf(WFType Empty t k)
        -> ProofOf(HasType Empty (deltaT c t) (tsubBTV a t s)) @-}
lem_deltaT_typ :: Prim -> Vname -> Kind -> Type -> HasType -> Type -> WFType -> HasType
lem_deltaT_typ Eql a k s p_c_aks t p_emp_t = undefined
lem_deltaT_typ _   a k s p_c_aks t p_emp_t = undefined
-- do I need: also Denotes t[v/x] delta(c,v)
