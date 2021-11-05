{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple-local"   @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesDenotationsEql where

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
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasWellFormedness
import PrimitivesSemantics
import PrimitivesDenotationsEqv
import PrimitivesDenotationsEq

{-@ reflect foo57 @-}
foo57 x = Just x
foo57 :: a -> Maybe a

{-@ lem_den_eqv_p' :: { p:Pred | Set_emp (tfreeBV (TRefn TBool Z p)) }
        -> ProofOf(Denotes (TFunc 1 (TRefn TBool Z p)  
                             (TFunc 2 (TRefn TBool Z p) (TRefn TBool Z 
                               (App (App (Prim Eqv) (BV 0))
                                 (App (App (AppT (Prim Eql) (TRefn TBool Z p)) (BV 1)) (BV 2)))))) (Prim Eqv)) @-}
lem_den_eqv_p' :: Expr -> Denotes
lem_den_eqv_p' p = lem_exch_refn_in_dfunc2 1 (TRefn TBool Z p) 2 (TRefn TBool Z p) TBool Z 
                       (refn_pred Eqv) (Prim Eqv ? val_eqv) (lem_den_eqv_p p) (q ? q_pf) step_func
  where
    val_eqv    = isValue (Prim Eqv) ? isTerm (Prim Eqv)
    {-@ step_func :: v_x:Value -> ProofOf(Denotes (TRefn TBool Z p) v_x) 
             -> v_y:Value -> ProofOf(Denotes (TRefn TBool Z p) v_y) 
             -> v':Value -> ProofOf(Denotes (tsubBV 2 v_y (tsubBV 1 v_x (TRefn TBool Z (refn_pred Eqv)))) v')
             -> ProofOf(CommonEvals (subBV 0 v' (subBV 2 v_y (subBV 1 v_x (refn_pred Eqv))))
                                    (subBV 0 v' (subBV 2 v_y (subBV 1 v_x q)))) @-}
    step_func :: Expr -> Denotes -> Expr -> Denotes -> Expr -> Denotes -> CommonEvals
    step_func v1 den_bzp_v1 v2 den_bzp_v2 v' den_bzqv1v2_v' = common_ev 
      where
        p_v1_bl    = get_ftyp_from_den (TRefn TBool Z p) v1 den_bzp_v1
        p_v2_bl    = get_ftyp_from_den (TRefn TBool Z p) v2 den_bzp_v2
        p_v'_bl    = get_ftyp_from_den (tsubBV 2 v2 (tsubBV 1 v1 (TRefn TBool Z (refn_pred Eqv)))) v' den_bzqv1v2_v'
        (Bc b1)    = v1 ? lem_bool_values v1 (p_v1_bl ? erase (TRefn TBool Z p))
        (Bc b2)    = v2 ? lem_bool_values v2 (p_v2_bl ? erase (TRefn TBool Z p))
        (Bc b')    = v' ? lem_bool_values v' (p_v'_bl ? er_pf)
        compat     = isCompat  Eqv (v' ? lem_bool_values v' (p_v'_bl ? er_pf))
        compatT    = isCompatT Eql (TRefn TBool Z p ? erase (TRefn TBool Z p))
        er_pf      =   erase (tsubBV 2 v2 (tsubBV 1 v1 (TRefn TBool Z (refn_pred Eqv))))
                     ? lem_erase_tsubBV 2 v2 (tsubBV 1 v1 (TRefn TBool Z (refn_pred Eqv)))
                     ? lem_erase_tsubBV 1 v1 (TRefn TBool Z (refn_pred Eqv))
                   === erase (TRefn TBool Z (refn_pred Eqv))

        inner_step = EPrimT Eql (TRefn TBool Z p ? compatT) ? deltaT Eql (TRefn TBool Z p ? compatT)
        midd1_step = EApp1 (AppT (Prim Eql) (TRefn TBool Z p)) (Prim Eqv) inner_step v1
        midd2_step = EApp1 (App (AppT (Prim Eql) (TRefn TBool Z p)) v1) (App (Prim Eqv) v1)
                           midd1_step v2
        midd2_redc = lemma_eqv_semantics v1 b1 (Refl v1) v2 b2 (Refl v2)
        midd2_eval = AddStep (App (App (AppT (Prim Eql) (TRefn TBool Z p)) v1) v2)
                             (App (App (Prim Eqv) v1) v2) midd2_step
                             (Bc (blIff b1 b2)) midd2_redc
        outer_eval = lemma_eqv_semantics v' b' (Refl v') 
                                         (App (App (AppT (Prim Eql) (TRefn TBool Z p)) v1) v2)
                                         (blIff b1 b2) midd2_eval  

        common_ev  = BothEv (subBV 0 v' (subBV 2 v2 (subBV 1 v1 (refn_pred Eqv))))
                            (subBV 0 v' (subBV 2 v2 (subBV 1 v1 q)))
                            (Bc (blIff b' (blIff b1 b2))) 
                            evals_left (outer_eval ? pf_right)
        pf_right   = lem_sub_bvs_in_refn_eql (v1 ? lem_den_nobv v1 (TRefn TBool Z p) den_bzp_v1)
                                             (v2 ? lem_den_nobv v2 (TRefn TBool Z p) den_bzp_v2) v' TBool p
        evals_left = lemma_semantics_refn_eqv b1 b2 b' ? lem_sub_refn_eqv v1 v2 v'

    q          = App (App (Prim Eqv) (BV 0)) (App (App (AppT (Prim Eql) (TRefn TBool Z p)) (BV 1)) (BV 2))
    q_pf       = isPred (App (App (Prim Eqv) (BV 0)) (App (App (AppT (Prim Eql) (TRefn TBool Z p)) (BV 1)) (BV 2)))
               === (isTerm (App (Prim Eqv) (BV 0)) &&
                    isTerm (App (App (AppT (Prim Eql) (TRefn TBool Z p)) (BV 1)) (BV 2)))
               === (isTerm (Prim Eqv) && isTerm (BV 0) && 
                    isTerm (App (AppT (Prim Eql) (TRefn TBool Z p)) (BV 1)) && isTerm (BV 2))
               === (isTerm (AppT (Prim Eql) (TRefn TBool Z p)) && isTerm (BV 1))
               ===  isTerm (Prim Eql)

{-@ lem_den_eq_p' :: { p:Pred | Set_emp (tfreeBV (TRefn TInt Z p)) }
        -> ProofOf(Denotes (TFunc 1 (TRefn TInt Z p)  
                             (TFunc 2 (TRefn TInt Z p) (TRefn TBool Z 
                               (App (App (Prim Eqv) (BV 0))
                                 (App (App (AppT (Prim Eql) (TRefn TInt Z p)) (BV 1)) (BV 2)))))) (Prim Eq)) @-}
lem_den_eq_p' :: Expr -> Denotes
lem_den_eq_p' p = lem_exch_refn_in_dfunc2 1 (TRefn TInt Z p) 2 (TRefn TInt Z p) TBool Z 
                       (refn_pred Eq) (Prim Eq ? val_eq) (lem_den_eq_p p) (q ? q_pf) step_func
  where
    {-@ step_func :: v_x:Value -> ProofOf(Denotes (TRefn TInt Z p) v_x) 
             -> v_y:Value -> ProofOf(Denotes (TRefn TInt Z p) v_y) 
             -> v':Value -> ProofOf(Denotes (tsubBV 2 v_y (tsubBV 1 v_x (TRefn TBool Z (refn_pred Eq)))) v')
             -> ProofOf(CommonEvals (subBV 0 v' (subBV 2 v_y (subBV 1 v_x (refn_pred Eq))))
                                    (subBV 0 v' (subBV 2 v_y (subBV 1 v_x q)))) @-}
    step_func :: Expr -> Denotes -> Expr -> Denotes -> Expr -> Denotes -> CommonEvals
    step_func v1 den_bzp_v1 v2 den_bzp_v2 v' den_bzqv1v2_v' = common_ev
      where
        p_v'_bl    = get_ftyp_from_den (tsubBV 2 v2 (tsubBV 1 v1 (TRefn TBool Z (refn_pred Eq)))) v' den_bzqv1v2_v'
        compat     = isCompat Eqv (v' ? lem_bool_values v' (p_v'_bl ? er_pf))
        compatT    = isCompatT Eql (TRefn TInt Z p ? erase (TRefn TInt Z p))
        er_pf      =   erase (tsubBV 2 v2 (tsubBV 1 v1 (TRefn TBool Z (refn_pred Eq))))
                     ? lem_erase_tsubBV 2 v2 (tsubBV 1 v1 (TRefn TBool Z (refn_pred Eq)))
                     ? lem_erase_tsubBV 1 v1 (TRefn TBool Z (refn_pred Eq))
                   === erase (TRefn TBool Z (refn_pred Eq))
        prim_step  = lem_step_evals (App (Prim Eqv) v') (delta Eqv (v' ? compat)) (EPrim Eqv v')
        inner_step = EPrimT Eql (TRefn TInt Z p ? compatT) ? deltaT Eql (TRefn TInt Z p ? compatT)
        midd1_step = EApp1 (AppT (Prim Eql) (TRefn TInt Z p)) (Prim Eq) inner_step v1
        midd2_step = EApp1 (App (AppT (Prim Eql) (TRefn TInt Z p)) v1) (App (Prim Eq) v1)
                           midd1_step v2
        midd2_eval = lem_step_evals (App (App (AppT (Prim Eql) (TRefn TInt Z p)) v1) v2)
                                    (App (App (Prim Eq) v1) v2) midd2_step
        outer_eval = lemma_app_both_many (App (Prim Eqv) v') (delta Eqv (v' ? compat)) prim_step
                           (App (App (AppT (Prim Eql) (TRefn TInt Z p)) v1) v2) 
                           (App (App (Prim Eq) v1) v2 ? tm_eq12) midd2_eval
        tm_eq12    =   isTerm (App (App (Prim Eq) v1) v2)
                   === (isTerm (App (Prim Eq) v1) && isTerm v2)
                   === (isTerm (Prim Eq) && isTerm v1 && isTerm v2)
         
        common_ev  = BothEv (subBV 0 v' (subBV 2 v2 (subBV 1 v1 (refn_pred Eq))))
                            (subBV 0 v' (subBV 2 v2 (subBV 1 v1 q)))
                            (App (delta Eqv (v' ? compat))  (App (App (Prim Eq) v1) v2))
                            evals_left (outer_eval ? pf_right)
        pf_right   = lem_sub_bvs_in_refn_eql (v1 ? lem_den_nobv v1 (TRefn TInt Z p) den_bzp_v1)
                                             (v2 ? lem_den_nobv v2 (TRefn TInt Z p) den_bzp_v2) v' TInt p
        evals_left = lem_sub_refn_eq_evals   (v1 ? lem_den_nobv v1 (TRefn TInt Z p) den_bzp_v1) 
                            (v2 ? lem_den_nobv v2 (TRefn TInt Z p) den_bzp_v2) (v' ? compat)
    q          = App (App (Prim Eqv) (BV 0)) (App (App (AppT (Prim Eql) (TRefn TInt Z p)) (BV 1)) (BV 2))
    q_pf       =   isPred (App (App (Prim Eqv) (BV 0)) (App (App (AppT (Prim Eql) (TRefn TInt Z p)) (BV 1)) (BV 2)))
               === (isTerm (App (Prim Eqv) (BV 0)) &&
                    isTerm (App (App (AppT (Prim Eql) (TRefn TInt Z p)) (BV 1)) (BV 2)))
               === (isTerm (Prim Eqv) && isTerm (BV 0) && 
                    isTerm (App (AppT (Prim Eql) (TRefn TInt Z p)) (BV 1)) && isTerm (BV 2))
               === (isTerm (AppT (Prim Eql) (TRefn TInt Z p)) && isTerm (BV 1))
               ===  isTerm (Prim Eql)
    val_eq     = isValue (Prim Eq) ? isTerm (Prim Eq)

{-@ lem_den_eql :: () -> ProofOf(Denotes (ty Eql) (Prim Eql)) @-}
lem_den_eql :: () -> Denotes
lem_den_eql () = DPoly 1 Base t'{-(TFunc (firstBV Eql) (inType Eql) (ty' Eql))-} (Prim Eql ? val_eql)
                    (FTPrm FEmpty Eql ? er_pf) val_den_func 
  where
    er_pf   =   erase_ty Eql
            === erase (ty Eql) 
            === erase (TPoly 1 Base (TFunc (firstBV Eql) (inType Eql) (ty' Eql))) 
            === FTPoly 1 Base (erase (TFunc (firstBV Eql) (inType Eql) (ty' Eql)))
    val_eql = isValue (Prim Eql) ? isTerm (Prim Eql)
    {-@ val_den_func :: t_a:UserType -> ProofOf(WFType Empty t_a Base)
                            -> ProofOf(ValueDenoted (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t')) @-}
    val_den_func :: Type -> WFType -> ValueDenoted
    val_den_func t_a pf_emp_ta = case (t_a, erase t_a) of
        (TRefn b z q_, FTBasic TBool) -> ValDen (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t') (Prim Eqv)
                                  (lem_step_evals (AppT (Prim Eql) t_a) (Prim Eqv) (EPrimT Eql (t_a ? comp) ? del)) 
                                  (lem_den_eqv_p' (strengthen (Bc True ? pred) 
                                       (q ? lem_refn_is_pred (TRefn b z q ? isTRefn (TRefn b z q)) b z q) ? nobv) ? typf)
          where
            q         = q_ ? lem_refn_is_pred (TRefn b z q_ ? isTRefn (TRefn b z q_)) b z q_
            p_emp_ttq = lem_push_wf Empty (TRefn TBool Z q) pf_emp_ta (WFFEmpty ? erase_env Empty)
                                    (Bc True ? pred) (1 ? fvpf ? emp) 
                                    (FTBC (FCons 1 (FTBasic TBool) (FEmpty ? femp)) True ? unpf)
                            ? ( push (Bc True) (TRefn TBool Z q ? noExists (TRefn TBool Z q)) 
                            === (TRefn TBool Z (strengthen (Bc True) q)) )
            nobv      = lem_tfreeBV_empty Empty (TRefn TBool Z (strengthen (Bc True) q)) Base p_emp_ttq
            comp = isCompatT Eql (t_a ? (erase t_a === FTBasic TBool))
            del  = deltaT Eql (t_a ? comp)
            erpf = erase (TRefn TBool Z q)
            emp  = not (in_env 1 Empty) === not (S.member 1 (binds Empty))
            femp = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty)) === not (S.member 1 (binds Empty))
            fvpf = fv (Bc True) ? ftv (Bc True) ? binds Empty
            unpf = unbind 0 1 (Bc True) === subBV 0 (FV 1 ? val1) (Bc True) === Bc True
            pred = isPred (Bc True)
            typf = lem_sub_ty_eql b z q
        (TRefn b z q_, FTBasic TInt)  -> ValDen (AppT (Prim Eql) t_a) (tsubBTV 1 t_a t') (Prim Eq)
                                  (lem_step_evals (AppT (Prim Eql) t_a) (Prim Eq)  (EPrimT Eql (t_a ? comp) ? del)) 
                                  (lem_den_eq_p' (strengthen (Bc True ? pred) 
                                       (q ? lem_refn_is_pred (TRefn b z q ? isTRefn (TRefn b z q)) b z q) ? nobv) ? typf)
          where
            q         = q_ ? lem_refn_is_pred (TRefn b z q_ ? isTRefn (TRefn b z q_)) b z q_
            p_emp_ttq = lem_push_wf Empty (TRefn TInt Z q) pf_emp_ta (WFFEmpty ? erase_env Empty)
                                    (Bc True ? pred) (1 ? fvpf ? emp) 
                                    (FTBC (FCons 1 (FTBasic TInt) (FEmpty ? femp)) True ? unpf)
                                    ? ( push (Bc True) (TRefn TInt Z q ? noExists (TRefn TInt Z q)) 
                                    === (TRefn TInt Z (strengthen (Bc True) q)) )
            nobv      = lem_tfreeBV_empty Empty (TRefn TInt Z (strengthen (Bc True) q)) Base p_emp_ttq
            comp = isCompatT Eql (t_a ? (erase t_a === FTBasic TInt))
            del  = deltaT Eql (t_a ? comp)
            erpf = erase (TRefn TInt Z q)
            femp = not (in_envF 1 FEmpty) === not (S.member 1 (bindsF FEmpty)) === not (S.member 1 (binds Empty))
            emp  = not (in_env 1 Empty) === not (S.member 1 (binds Empty))
            fvpf = fv (Bc True) ? ftv (Bc True) 
            unpf = unbind 0 1 (Bc True) === subBV 0 (FV 1 ? val1) (Bc True) === Bc True
            pred = isPred (Bc True)
            typf = lem_sub_ty_eql b z q
        (TRefn b z q_, _)     -> impossible ("by lemmas" ? lem_base_types (erase t_a)
                                               (lem_erase_wftype Empty t_a Base pf_emp_ta ? erase_env Empty))
        (TFunc x s_x s', _)   -> impossible ("by lemmas" ? lem_wf_usertype_base_trefn Empty t_a pf_emp_ta
                                                      ? isTRefn (TFunc x s_x s'))
        (TExists x s_x s', _) -> impossible ("by lemmas" ? lem_wf_usertype_base_trefn Empty t_a pf_emp_ta
                                                      ? isTRefn (TExists x s_x s'))
        (TPoly a1 k1 s', _)   -> impossible ("by lemmas" ? lem_wf_usertype_base_trefn Empty t_a pf_emp_ta
                                                      ? isTRefn (TPoly a1 k1 s'))
    t'   = (TFunc (firstBV Eql) (inType Eql) (ty' Eql))
    val1 = isValue (FV 1) ? isTerm (FV 1)

{-@ ple lem_sub_ty_eql @-}
{-@ lem_sub_ty_eql :: b:Basic -> z:RVname -> q:Pred 
        -> { pf:_ | tsubBTV 1 (TRefn b z q) (TFunc (firstBV Eql) (inType Eql) (ty' Eql)) ==
                      TFunc 1 (TRefn b z (strengthen (Bc True) q))
                        (TFunc 2 (TRefn b z (strengthen (Bc True) q))
                          (TRefn TBool Z (App (App (Prim Eqv) (BV 0))
                            (App (App (AppT (Prim Eql) (TRefn b z (strengthen (Bc True) q))) (BV 1)) (BV 2))))) } @-}
lem_sub_ty_eql :: Basic -> RVname -> Expr -> Proof
lem_sub_ty_eql b z q  = () 

{-@ ple lem_sub_bvs_in_refn_eql @-}
{-@ lem_sub_bvs_in_refn_eql :: { v1:Value | Set_emp (freeBV v1) } -> { v2: Value | Set_emp (freeBV v2) } 
        -> v':Value -> b:Basic -> { p:Pred | Set_emp (tfreeBV (TRefn b Z p)) }
        -> { pf:_ | subBV 0 v' (subBV 2 v2 (subBV 1 v1 (App (App (Prim Eqv) (BV 0)) 
                                 (App (App (AppT (Prim Eql) (TRefn b Z p)) (BV 1)) (BV 2))))) ==
                    App (App (Prim Eqv) v') (App (App (AppT (Prim Eql) (TRefn b Z p)) v1) v2) } @-}
lem_sub_bvs_in_refn_eql :: Expr -> Expr -> Expr -> Basic -> Expr -> Proof
lem_sub_bvs_in_refn_eql v1 v2 v' b p = () ? lem_subBV_notin 2 v2 v1
                                          ? lem_subBV_notin 0 v' v1 ? lem_subBV_notin 0 v' v2
                                          ? lem_tsubBV_notin 0 v' (TRefn b Z p) 
                                          ? lem_tsubBV_notin 2 v2 (TRefn b Z p) 
                                          ? lem_tsubBV_notin 1 v1 (TRefn b Z p)

{-@ ple lem_sub_refn_eqv @-}
{-@ lem_sub_refn_eqv :: { v1:Value | Set_emp (freeBV v1) } -> { v2: Value | Set_emp (freeBV v2) } -> v':Value 
        -> { pf:_ | subBV 0 v' (subBV 2 v2 (subBV 1 v1 (refn_pred Eqv))) ==
                    App (App (Prim Eqv) v') (App (App (Prim Or)
                                    (App (App (Prim And) v1) v2))
                                    (App (App (Prim And) (App (Prim Not) v1))
                                         (App (Prim Not) v2))) } @-}
lem_sub_refn_eqv :: Expr -> Expr -> Expr -> Proof
lem_sub_refn_eqv v1 v2 v' = () ? lem_subBV_notin 2 v2 v1
                               ? lem_subBV_notin 0 v' v1 ? lem_subBV_notin 0 v' v2

{-@ ple lem_sub_refn_eq @-}
{-@ lem_sub_refn_eq :: { v1:Value | Set_emp (freeBV v1) } -> { v2: Value | Set_emp (freeBV v2) } -> v':Value 
        -> { pf:_ | subBV 0 v' (subBV 2 v2 (subBV 1 v1 (refn_pred Eq))) ==
                    App (App (Prim Eqv) v')  (App (App (Prim Eq) v1) v2) } @-}
lem_sub_refn_eq :: Expr -> Expr -> Expr -> Proof
lem_sub_refn_eq v1 v2 v' = () ? lem_subBV_notin 2 v2 v1
                              ? lem_subBV_notin 0 v' v1 ? lem_subBV_notin 0 v' v2

{-@ lem_sub_refn_eq_evals :: { v1:Value | Set_emp (freeBV v1) } -> { v2: Value | Set_emp (freeBV v2) } 
        -> { v':Value | isCompat Eqv v' }
        -> ProofOf(EvalsTo (subBV 0 v' (subBV 2 v2 (subBV 1 v1 (refn_pred Eq))))
                           (App (delta Eqv v')  (App (App (Prim Eq) v1) v2)) ) @-}
lem_sub_refn_eq_evals :: Expr -> Expr -> Expr -> EvalsTo
lem_sub_refn_eq_evals v1 v2 v' = lem_step_evals (subBV 0 v' (subBV 2 v2 (subBV 1 v1 (refn_pred Eq))))
                                                (App (delta Eqv v')  (App (App (Prim Eq) v1) v2))
                                                (outer_step ? lem_sub_refn_eq v1 v2 v')
  where
    inner_step = EPrim Eqv v'
    outer_step = EApp1 (App (Prim Eqv) v') (delta Eqv v') inner_step (App (App (Prim Eq) v1) v2)
