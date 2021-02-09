{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple-local"   @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotations where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsEnvironments
import BasicPropsSubstitution
import BasicPropsWellFormedness
import WellFormedness
import PrimitivesWFType
import Typing
import Entailments
import SubtypingFromEntailments
import BasicPropsCSubst
import PrimitivesSemantics
import LemmasTyping
{-import PrimitivesDenotationsAnd
import PrimitivesDenotationsOr
import PrimitivesDenotationsNot
import PrimitivesDenotationsEqv
import PrimitivesDenotationsLeq
import PrimitivesDenotationsEq
import PrimitivesDenotationsEql-}

{-@ reflect foo58 @-}
foo58 x = Just x
foo58 :: a -> Maybe a

{-@ ple reduce_pred_tybc @-}
{-@ reduce_pred_tybc :: b:Bool -> ProofOf(EvalsTo (subBV 0 (Bc b) (App (App (Prim Eqv) (BV 0)) (Bc b))) (Bc True)) @-}
reduce_pred_tybc :: Bool -> EvalsTo
reduce_pred_tybc b = lemma_eqv_semantics (Bc b) b (Refl (Bc b)) (Bc b) b (Refl (Bc b))

-- Lemma. Denotations of Primitive/Constant Types
{-@ lem_den_tybc :: b:Bool -> ProofOf(Denotes (tybc b) (Bc b)) @-}
lem_den_tybc ::  Bool -> Denotes
lem_den_tybc b = DRefn TBool Z (App (App (Prim Eqv) (BV 0)) (Bc b) ? pred_pf) 
                       (Bc b ? val_pf) (FTBC FEmpty b) (reduce_pred_tybc b)
                       ? toProof ( tybc b === TRefn TBool Z (App (App (Prim Eqv) (BV 0)) (Bc b)) )
  where
    val_pf    = toProof ( isValue (Bc b) === True )
    pred_pf   = toProof ( isPred (App (App (Prim Eqv) (BV 0)) (Bc b))
                    === ( isTerm (App (Prim Eqv) (BV 0)) && isTerm (Bc b) )
                    === ( isTerm (Prim Eqv) && isTerm (BV 0) && isTerm (Bc b) )
                    ===    True )
 
{-@ ple reduce_pred_tyic @-}
{-@ reduce_pred_tyic :: n:Int -> ProofOf(EvalsTo (subBV 0 (Ic n) (App (App (Prim Eq) (BV 0)) (Ic n))) (Bc True)) @-}
reduce_pred_tyic :: Int -> EvalsTo
reduce_pred_tyic n = lemma_eq_semantics (Ic n) n (Refl (Ic n)) (Ic n) n (Refl (Ic n))

{-@ lem_den_tyic :: n:Int -> ProofOf(Denotes (tyic n) (Ic n)) @-}
lem_den_tyic :: Int -> Denotes
lem_den_tyic n = DRefn TInt Z (App (App (Prim Eq) (BV 0)) (Ic n) ? pred_pf) 
                       (Ic n ? val_pf) (FTIC FEmpty n) (reduce_pred_tyic n)
                       ? toProof ( tyic n === TRefn TInt Z (App (App (Prim Eq) (BV 0)) (Ic n)) )
  where
    val_pf    = toProof ( isValue (Ic n) === True )
    pred_pf   = toProof ( isPred (App (App (Prim Eq) (BV 0)) (Ic n))
                    === ( isTerm (App (Prim Eq) (BV 0)) && isTerm (Ic n) )
                    === ( isTerm (Prim Eq) && isTerm (BV 0) && isTerm (Ic n) )
                    ===    True )

{-@ lem_den_ty :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
        -> c:Prim -> ProofOf(Denotes (ctsubst th (ty c)) (Prim c)) @-}
lem_den_ty :: Env -> CSub -> DenotesEnv -> Prim -> Denotes
lem_den_ty g th den_g_th c = undefined {-
lem_den_ty g th den_g_th And      = lem_den_and    ? lem_ctsubst_nofree th (ty And)
lem_den_ty g th den_g_th Or       = lem_den_or     ? lem_ctsubst_nofree th (ty Or)
lem_den_ty g th den_g_th Not      = lem_den_not () ? lem_ctsubst_nofree th (ty Not)
lem_den_ty g th den_g_th Eqv      = lem_den_eqv    ? lem_ctsubst_nofree th (ty Eqv)
lem_den_ty g th den_g_th Leq      = lem_den_leq    ? lem_ctsubst_nofree th (ty Leq)
lem_den_ty g th den_g_th (Leqn n) = lem_den_leqn n ? lem_ctsubst_nofree th (ty (Leqn n))
lem_den_ty g th den_g_th Eq       = lem_den_eq     ? lem_ctsubst_nofree th (ty Eq)
lem_den_ty g th den_g_th (Eqn n)  = lem_den_eqn  n ? lem_ctsubst_nofree th (ty (Eqn n))
lem_den_ty g th den_g_th Eql      = lem_den_eql () ? lem_ctsubst_nofree th (ty Eql)
-}
{-@ lem_denote_sound_typ_tprim :: g:Env -> c:Prim 
        ->  th:CSub  -> ProofOf(DenotesEnv g th)
        -> ProofOf(ValueDenoted (csubst th (Prim c)) (ctsubst th (ty c))) @-}
lem_denote_sound_typ_tprim :: Env -> Prim -> CSub -> DenotesEnv -> ValueDenoted
lem_denote_sound_typ_tprim g c th den_g_th 
  = ValDen (Prim c ? lem_csubst_prim th c) (ctsubst th (ty c)) (Prim c ? val_pf ? term_pf) 
           (Refl (Prim c)) den_tyc_c
      where
        den_tyc_c = lem_den_ty g th den_g_th c
        val_pf    = toProof ( isValue (Prim c) === True )
        term_pf   = toProof ( isTerm (Prim c) === True )

-- these are used in lem_exact_type in the (self (ty(b/i)c (b/n)) e k) cases
{-@ ple lem_csub_unbind_refn_bc @-}
{-@ lem_csub_unbind_refn_bc :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) } 
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> b:Bool
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (Prim Eqv) (BV 0)) (Bc b)))
                 == App (App (Prim Eqv) v) (Bc b) } @-}
lem_csub_unbind_refn_bc :: Env -> CSub -> Vname -> Expr -> Bool -> Proof
lem_csub_unbind_refn_bc g th y v b = () ? lem_subBV_notin 0 (FV y) (Bc b)
                                        ? lem_subFV_notin y v      (Bc b)
                                        ? lem_csubst_app  th (App (Prim Eqv) v) (Bc b)
                                        ? lem_csubst_app  th (Prim Eqv) v
                                        ? lem_csubst_prim th Eqv
                                        ? lem_csubst_nofv th v
                                        ? lem_csubst_bc   th b  

{-@ ple lem_csub_unbind_refn'_bc @-}
{-@ lem_csub_unbind_refn'_bc :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) }
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> b:Bool
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (AppT (Prim Eql) (tybc b)) (BV 0)) (Bc b))) 
                 == App (App (AppT (Prim Eql) (tsubBV 0 v (tybc b))) v) (Bc b) } @-}
lem_csub_unbind_refn'_bc :: Env -> CSub -> Vname -> Expr -> Bool -> Proof 
lem_csub_unbind_refn'_bc g th y v b = () ? lem_subBV_notin  0 (FV y) (Bc b)
                                         ? lem_subFV_notin  y v      (Bc b)
                                         ? lem_tsubFV_unbindT 0 y v (tybc b)
                                         ? lem_csubst_app  th (App (AppT (Prim Eql) (tybc b)) v) (Bc b)
                                         ? lem_csubst_app  th (AppT (Prim Eql) (tybc b)) v
                                         ? lem_csubst_appT th (Prim Eql) (tybc b)
                                         ? lem_csubst_prim th Eql
                                         ? lem_ctsubst_nofree th (tybc b)
                                         ? lem_csubst_nofv th v
                                         ? lem_csubst_bc   th b  

{-@ ple lem_csub_unbind_refn_ic @-}
{-@ lem_csub_unbind_refn_ic :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) } 
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> n:Int
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (Prim Eq) (BV 0)) (Ic n)))
                 == App (App (Prim Eq) v) (Ic n) } @-}
lem_csub_unbind_refn_ic :: Env -> CSub -> Vname -> Expr -> Int -> Proof
lem_csub_unbind_refn_ic g th y v n = () ? lem_subBV_notin 0 (FV y) (Ic n)
                                        ? lem_subFV_notin y v      (Ic n)
                                        ? lem_csubst_app  th (App (Prim Eq) v) (Ic n)
                                        ? lem_csubst_app  th (Prim Eq) v
                                        ? lem_csubst_prim th Eq
                                        ? lem_csubst_nofv th v
                                        ? lem_csubst_ic   th n 

{-@ ple lem_csub_unbind_refn'_ic @-}
{-@ lem_csub_unbind_refn'_ic :: g:Env -> th:CSub -> { y:Vname | not (in_csubst y th) }
        -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) } -> n:Int
        -> { pf:_ | csubst (CCons y v th) (unbind 0 y (App (App (AppT (Prim Eql) (tyic n)) (BV 0)) (Ic n))) 
                 == App (App (AppT (Prim Eql) (tsubBV 0 v (tyic n))) v) (Ic n) } @-}
lem_csub_unbind_refn'_ic :: Env -> CSub -> Vname -> Expr -> Int -> Proof 
lem_csub_unbind_refn'_ic g th y v n = () ? lem_subBV_notin  0 (FV y) (Ic n)
                                         ? lem_subFV_notin  y v      (Ic n)
                                         ? lem_tsubFV_unbindT 0 y v (tyic n)
                                         ? lem_csubst_app  th (App (AppT (Prim Eql) (tyic n)) v) (Ic n)
                                         ? lem_csubst_app  th (AppT (Prim Eql) (tyic n)) v
                                         ? lem_csubst_appT th (Prim Eql) (tyic n)
                                         ? lem_csubst_prim th Eql
                                         ? lem_ctsubst_nofree th (tyic n)
                                         ? lem_csubst_nofv th v
                                         ? lem_csubst_ic   th n  

{-@ ple lem_exact_type_tbc @-}
{-@ lem_exact_type_tbc :: g:Env -> v:Value -> t:Type 
        -> { p_v_t:HasType | (propOf p_v_t == HasType g v t) && isTBC p_v_t } -> k:Kind
        -> ProofOf(WFType g t k) -> ProofOf(WFEnv g) -> ProofOf(HasType g v (self t v k)) @-}
lem_exact_type_tbc :: Env -> Expr -> Type -> HasType -> Kind -> WFType -> WFEnv -> HasType
lem_exact_type_tbc g e t (TBC _ b)   Base p_g_t p_g_wf 
  = TSub g (Bc b) (tybc b) (TBC g b) (self (tybc b) (Bc b) Base) Base p_g_self_tybc tybc_self_tybc
      where
        p_er_g_wf      = lem_erase_env_wfenv g p_g_wf
        p_g_tybc       = lem_wf_tybc g b
        p_g_self_tybc  = lem_selfify_wf' g (tybc b) Base p_g_tybc p_g_wf (Bc b) (TBC g b)
        {-@ ev_transf :: th':CSub -> ProofOf(DenotesEnv (Cons (fresh_var g) (TRefn TBool Z refn) g) th')
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn))  (Bc True))
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn')) (Bc True)) @-}
        ev_transf :: CSub -> DenotesEnv -> EvalsTo -> EvalsTo
        ev_transf th' den_g'_th' ev_th'ref_tt = case den_g'_th' of
          (DExt _g th den_g_th y _tybc v den_thtybc_v)
            -> AddStep (App (App (AppT (Prim Eql) (tsubBV 0 v (tybc b))) v) (Bc b))
                       (App (App (Prim Eqv) v) (Bc b)) step1'' (Bc True) (ev_th'ref_tt
                   ? lem_csub_unbind_refn_bc  g th (y ? lem_binds_env_th g th den_g_th) v b)
                   ? lem_csub_unbind_refn'_bc g th (y ? lem_binds_env_th g th den_g_th) v b
                 where
                   step1   = EPrimT Eql (tsubBV 0 v (tybc b) ? lem_erase_tsubBV 0 v (tybc b))
                   step1'  = EApp1 (AppT (Prim Eql) (tsubBV 0 v (tybc b))) (Prim Eqv) step1 v
                   step1'' = EApp1 (App (AppT (Prim Eql) (tsubBV 0 v (tybc b))) v) (App (Prim Eqv) v) step1' (Bc b)
        refn           = App (App (Prim Eqv) (BV 0)) (Bc b)
        refn'          = App (App (AppT (Prim Eql) (tybc b)) (BV 0)) (Bc b)
        tybc_self_tybc = lem_subtype_repetition g p_er_g_wf TBool Z refn p_g_tybc refn' ev_transf
lem_exact_type_tbc g e t p_e_t       Star p_g_t p_g_wf = p_e_t ? ( self t e Star === t )

{-@ ple lem_exact_type_tic @-}
{-@ lem_exact_type_tic :: g:Env -> v:Value -> t:Type 
        -> { p_v_t:HasType | (propOf p_v_t == HasType g v t) && isTIC p_v_t } -> k:Kind
        -> ProofOf(WFType g t k) -> ProofOf(WFEnv g) -> ProofOf(HasType g v (self t v k)) @-}
lem_exact_type_tic :: Env -> Expr -> Type -> HasType -> Kind -> WFType -> WFEnv -> HasType
lem_exact_type_tic g e t (TIC _ n)   Base p_g_t p_g_wf 
  = TSub g (Ic n) (tyic n) (TIC g n) (self (tyic n) (Ic n) Base) Base p_g_self_tyic tyic_self_tyic
      where
        p_er_g_wf      = lem_erase_env_wfenv g p_g_wf
        p_g_tyic       = lem_wf_tyic g n
        p_g_self_tyic  = lem_selfify_wf' g (tyic n) Base p_g_tyic p_g_wf (Ic n) (TIC g n)
        {-@ ev_transf :: th':CSub -> ProofOf(DenotesEnv (Cons (fresh_var g) (TRefn TInt Z refn) g) th')
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn))  (Bc True))
                           -> ProofOf(EvalsTo (csubst th' (unbind 0 (fresh_var g) refn')) (Bc True)) @-}
        ev_transf :: CSub -> DenotesEnv -> EvalsTo -> EvalsTo
        ev_transf th' den_g'_th' ev_th'ref_tt = case den_g'_th' of
          (DExt _g th den_g_th y _tybc v den_thtybc_v)
            -> AddStep (App (App (AppT (Prim Eql) (tsubBV 0 v (tyic n))) v) (Ic n))
                       (App (App (Prim Eq) v) (Ic n)) step1'' (Bc True) (ev_th'ref_tt
                   ? lem_csub_unbind_refn_ic  g th (y ? lem_binds_env_th g th den_g_th) v n)
                   ? lem_csub_unbind_refn'_ic g th (y ? lem_binds_env_th g th den_g_th) v n
                 where
                   step1   = EPrimT Eql (tsubBV 0 v (tyic n) ? lem_erase_tsubBV 0 v (tyic n))
                   step1'  = EApp1 (AppT (Prim Eql) (tsubBV 0 v (tyic n))) (Prim Eq) step1 v
                   step1'' = EApp1 (App (AppT (Prim Eql) (tsubBV 0 v (tyic n))) v) (App (Prim Eq) v) step1' (Ic n)
        refn           = App (App (Prim Eq) (BV 0)) (Ic n)
        refn'          = App (App (AppT (Prim Eql) (tyic n)) (BV 0)) (Ic n)
        tyic_self_tyic = lem_subtype_repetition g p_er_g_wf TInt Z refn p_g_tyic refn' ev_transf
lem_exact_type_tic g e t p_e_t       Star p_g_t p_g_wf = p_e_t ? ( self t e Star === t )
