{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module DenotationsSoundnessTyp where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import PrimitivesFTyping
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
--import SubstitutionLemmaWF
import DenotationsSelfify
import DenotationsSoundnessSub
import PrimitivesSemantics
import PrimitivesDenotations

{-@ reflect foo51 @-}
foo51 x = Just x
foo51 :: a -> Maybe a

{-@ lem_denote_exact_type :: th:CSub -> { x:Vname | not (in_csubst x th) }
        -> { t:Type | Set_sub (free t) (bindsC th) } -> k:Kind -> w:Value 
        -> ProofOf(Denotes (ctsubst th t) w)
        -> ProofOf(Denotes (ctsubst (CCons x w th) (self t (FV x) k)) w) @-}
lem_denote_exact_type :: CSub -> Vname -> Type -> Kind -> Expr -> Denotes -> Denotes
lem_denote_exact_type th x (TRefn b z p) k w den_tht_w = undefined {- case den_tht_w of
  (DRefn _ _ _ _ pf_w_b ev_thpw_tt_) -> DRefn b z p w pf_w_b ev_thpexw_tt
    where
      {- @ thp_exact_w :: { p':Pred | p' == subBV z w thp_exact } @-}
      thp_exact_w  = App (App (Prim And) (subBV z w (csubst th p))) (App (App (equals b) w) w)
                         ? toProof ( subBV z w w === w )  --------------------------------
      thp_exact    = App (App (Prim And) (csubst th p)) (App (App (equals b) (BV z)) w)
              ? () {- toProof ( ctsubst (CCons x w th) (self (TRefn b z p) x) -}
                        ? lem_unroll_ctsubst_left th x w (self (TRefn b z p) (FV x))
                   {- === tsubFV x w (ctsubst th (self (TRefn b z p) x)) -}
                        ? lem_ctsubst_self_notin th (TRefn b z p) x
                   {- === tsubFV x w (self (ctsubst th (TRefn b z p)) x)
                      === tsubFV x w (self (TRefn b z (csubst th p)) x) -}
                        ? lem_tsubFV_value_self b z (csubst th p) x w     
                   {- === TRefn b z (App (App (Prim And) (csubst th p))
                                         (App (App (Prim (equals b)) (BV z)) w)) ) -}
      {-@ ev_thpw_tt :: ProofOf(EvalsTo (subBV z w (csubst th p)) (Bc True)) @-}
      ev_thpw_tt   = ev_thpw_tt_                   
      ev_andthpw1  = lemma_app_many2 (Prim And) (subBV z w (csubst th p)) (Bc True) ev_thpw_tt
                  -- EApp2 (subBV z w (csubst th p)) (Bc True) ev_thpw_tt (Prim And)
      ev_andthpw_t = lemma_add_step_after (App (Prim And) (subBV z w (csubst th p)))
                                          (App (Prim And) (Bc True)) ev_andthpw1
                                          (Lambda 1 (BV 1)) (EPrim And (Bc True))

      eql_w        = App (App (equals b) w) w
      {-@ ev_eqw_tt :: ProofOf(EvalsTo (App (App (equals b) w) w) (Bc True)) @-}
      ev_eqw_tt    = case b of
        TBool -> case w of
          (Bc True)  -> lemma_eqv_semantics (Bc True)  True  (Refl (Bc True))  (Bc True)  True  (Refl (Bc True))
          (Bc False) -> lemma_eqv_semantics (Bc False) False (Refl (Bc False)) (Bc False) False (Refl (Bc False))
          _          -> impossible ("by lemma" ? lem_bool_values w pf_w_b)
        TInt  -> case w of
          (Ic n)     -> lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic n) n (Refl (Ic n))
          _          -> impossible ("by lemma" ? lem_int_values w pf_w_b)

      ev_thpexw_1  = lemma_app_both_many (App (Prim And) (subBV z w (csubst th p)))
                                         (Lambda 1 (BV 1)) ev_andthpw_t 
                                         (App (App (equals b) w) w) (Bc True) ev_eqw_tt
      ev_thpexw_tt = lemma_add_step_after thp_exact_w (App (Lambda 1 (BV 1)) (Bc True))
                                          ev_thpexw_1 (Bc True) (EAppAbs 1 (BV 1) (Bc True)) -}
lem_denote_exact_type th x t@(TFunc z t_z t') k w_ den_tht_w 
    = den_tht_w ? toProof ( ctsubst (CCons x w th) (self t (FV x) k)           
                        === ctsubst (CCons x w th) t
                        === ctsubst th (tsubFV x w t) 
                        === ctsubst th t )
        where
          w = w_ ? lem_den_nofv w_ (ctsubst th t) den_tht_w
                 ? lem_den_nobv w_ (ctsubst th t) den_tht_w
lem_denote_exact_type th x (TExists z t_z t') k w den_tht_w = undefined
lem_denote_exact_type th x t@(TPoly a k_a t') k w_ den_tht_w 
    = den_tht_w ? toProof ( ctsubst (CCons x w th) (self t (FV x) k)           
                        === ctsubst (CCons x w th) t
                        === ctsubst th (tsubFV x w t) 
                        === ctsubst th t )
        where
          w = w_ ? lem_den_nofv w_ (ctsubst th t) den_tht_w
                 ? lem_den_nobv w_ (ctsubst th t) den_tht_w

