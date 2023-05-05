Require Import SystemRF.BasicDefinitions.
Require Import SystemRF.Names.
Require Import SystemRF.SystemFTyping.
Require Import SystemRF.WellFormedness.
Require Import SystemRF.Typing.
(*Require Import SystemRF.BasicPropsSubstitution.
Require Import SystemRF.BasicPropsEnvironments.*)
Require Import Denotations.ClosingSubstitutions.
Require Import Denotations.Denotations.
Require Import Denotations.BasicPropsCSubst.
Require Import Denotations.PrimitivesSemantics.

(*
{-@ lem_denotations_selfify_trefn :: b:Basic -> z:RVname -> p:Pred 
        -> ProofOf(WFType Empty (TRefn b z p) Base) -> { e:Term | Set_emp (freeBV e) } 
        -> ProofOf(HasFType FEmpty e (FTBasic b)) -> v:Value -> ProofOf(EvalsTo e v) 
        -> ProofOf(Denotes (TRefn b z p) v) -> ProofOf(Denotes (self (TRefn b z p) e Base) v) @-}
lem_denotations_selfify_trefn :: Basic -> RVname -> Expr -> WFType -> Expr -> HasFType -> Expr
                                -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify_trefn b z p p_emp_t e p_e_t v ev_e_v den_t_v 
  = DRefn b z (strengthen  (App (App (AppT (Prim Eql) (TRefn b z p)) (BV 0)) e)  p) --(selfify p b z e) 
          v p_v_b (ev_selfpv_tt
          ? lem_subBV_strengthen 0 v (App (App (AppT (Prim Eql) (TRefn b z p)) (BV 0)) e) p
          ? lem_subBV_notin 0 v e
          ? lem_tsubBV_notin 0 v (TRefn b z p) )
      where
        (DRefn _b _z _p _v p_v_b ev_pv_tt) = den_t_v
        y_           = fresh_var Empty
        y            = y_ ? lem_free_bound_in_env Empty (TRefn b z p) Base p_emp_t y_
                          ? lem_fv_bound_in_fenv FEmpty e (FTBasic b) p_e_t y_
        {-@ ev_rhs_tt :: ProofOf(EvalsTo (App (App (AppT (Prim Eql) (TRefn b z p)) v) e) 
                                         (Bc True)) @-}
        ev_rhs_tt    = lem_equals_evals b z p e v ev_e_v p_v_b 
        p_eqlte_b    = lem_eqlPred_ftyping Empty b z p p_emp_t WFFEmpty y e p_e_t 
        p_emp_er_t   = lem_erase_wftype Empty (TRefn b z p)  Base p_emp_t
        p_y_wf       = WFFBind FEmpty WFFEmpty y (FTBasic b) Base p_emp_er_t
        {-@ p_eqltev_b :: ProofOf(HasFType FEmpty 
                                           (App (App (AppT (Prim Eql) (TRefn b z p)) v) e) 
                                           (FTBasic TBool)) @-}
        p_eqltev_b   = lem_subst_ftyp FEmpty FEmpty y v (FTBasic b) p_v_b p_y_wf
                                      (App (App (AppT (Prim Eql) (TRefn b z p)) (FV y)) e) 
                                      (FTBasic TBool) p_eqlte_b 
                           ? lem_subFV_notin y v e
                           ? lem_subFV_notin y v p
                           ? lem_empty_concatF FEmpty
        {-@ ev_selfpv_tt :: ProofOf(EvalsTo 
                          (strengthen  (App (App (AppT (Prim Eql) (TRefn b z p)) v) e)  (subBV 0 v p)) 
                          (Bc True)) @-}
        ev_selfpv_tt = lem_strengthen_evals_tt (App (App (AppT (Prim Eql) (TRefn b z p)) v) e) 
                                               (subBV 0 v p) p_eqltev_b ev_rhs_tt ev_pv_tt

--- Lemma 7 in the paper version
{-@ lem_denotations_selfify :: t:Type -> k:Kind -> ProofOf(WFType Empty t k)
        -> { e:Term | Set_emp (freeBV e) } -> ProofOf(HasFType FEmpty e (erase t))
        -> v:Value -> ProofOf(EvalsTo e v) -> ProofOf(Denotes t v)
        -> ProofOf(Denotes (self t e k) v) @-}
lem_denotations_selfify :: Type -> Kind -> WFType -> Expr -> HasFType -> Expr
                                -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify t@(TRefn b z p)    Base p_emp_t e p_e_t v ev_e_v den_t_v 
  = lem_denotations_selfify_trefn b z (p ? lem_refn_is_pred t b z p) p_emp_t 
                                  e p_e_t v ev_e_v den_t_v
lem_denotations_selfify (TFunc z t_z t')   k    p_emp_t e p_e_t v ev_e_v den_t_v = den_t_v
lem_denotations_selfify (TExists z t_z t') Base p_emp_t e p_e_t v ev_e_v den_t_v = case den_t_v of
  (DExis _z _tz _t' _v p_v_ert' v_z den_tz_vz den_t'vz_v) 
    -> DExis z t_z (self t' e Base) v p_v_ert' v_z den_tz_vz den_selft'vz_v
         where 
           p_vz_er_tz     = get_ftyp_from_den t_z v_z den_tz_vz
           (WFExis _ _ _ k_z p_g_tz _ k_t' y p_y_t')
                          = lem_wfexis_for_wf_texists Empty  z t_z t' Base p_emp_t 
           p_y_wf         = WFEBind Empty WFEEmpty y t_z k_z p_g_tz
           p_emp_t'vz     = lem_subst_wf Empty Empty y v_z t_z p_vz_er_tz p_y_wf 
                                         (unbindT z y t') k_t' p_y_t'
                                         ? lem_empty_concatE Empty
                                         ? lem_tsubFV_unbindT z y v_z t'
           den_selft'vz_v = lem_denotations_selfify (tsubBV z v_z t') k_t' p_emp_t'vz 
                                                    e (p_e_t ? lem_erase_tsubBV z v_z t')
                                                    v ev_e_v den_t'vz_v
                                                    ? lem_tsubBV_self z v_z t' e Base
lem_denotations_selfify (TPoly a k_a t')   k    p_emp_t e p_e_t v ev_e_v den_t_v = den_t_v
lem_denotations_selfify t                  Star p_emp_t e p_e_t v ev_e_v den_t_v = den_t_v

{-@ lem_denotations_selfify' :: t:UserType -> k:Kind -> ProofOf(WFType Empty t k)
        -> { e:Term | Set_emp (freeBV e) } -> ProofOf(HasFType FEmpty e (erase t))
        -> v:Value -> ProofOf(EvalsTo (App (App (AppT (Prim Eql) t) v) e) (Bc True))
        -> ProofOf(Denotes t v) -> ProofOf(Denotes (self t e k) v) @-}
lem_denotations_selfify' :: Type -> Kind -> WFType -> Expr -> HasFType -> Expr
                                -> EvalsTo -> Denotes -> Denotes
lem_denotations_selfify' t@(TRefn b z p)    Base p_emp_t e p_e_t v ev_rhs_tt den_t_v 
  = lem_denotations_selfify_trefn' b z (p ? lem_refn_is_pred t b z p) p_emp_t 
                                   e p_e_t v ev_rhs_tt den_t_v
lem_denotations_selfify' (TFunc z t_z t')   k    p_emp_t e p_e_t v ev_rhs_tt den_t_v = den_t_v
lem_denotations_selfify' (TPoly a k_a t')   k    p_emp_t e p_e_t v ev_rhs_tt den_t_v = den_t_v
lem_denotations_selfify' t                  Star p_emp_t e p_e_t v ev_rhs_tt den_t_v = den_t_v


{-@ lem_equals_evals :: b:Basic -> z:RVname -> p:Pred -> e:Expr -> v:Value 
        -> ProofOf(EvalsTo e v) -> ProofOf(HasFType FEmpty v (FTBasic b))
        -> ProofOf(EvalsTo (App (App (AppT (Prim Eql) (TRefn b z p)) v) e) 
                           (Bc True)) @-}
lem_equals_evals :: Basic -> RVname -> Expr -> Expr -> Expr -> EvalsTo -> HasFType -> EvalsTo 
lem_equals_evals TBool z p e v ev_e_v p_v_b = case v of -- b in {Bool,Int} is implicit here
  (Bc w)  -> AddStep (App (App (AppT (Prim Eql) (TRefn TBool z p)) v) e) (App (App (Prim Eqv) v) e) step_one
                           (Bc True) ev_eqv_tt
    where
      st_eql_eqv = EPrimT Eql (TRefn TBool z p) -- equals b ~> Prim Eqv
      step_app   = EApp1 (AppT (Prim Eql) (TRefn TBool z p)) (Prim Eqv) st_eql_eqv v
      step_one   = EApp1 (App (AppT (Prim Eql) (TRefn TBool z p)) v) (App (Prim Eqv) v) step_app e
      ev_eqv_tt  = lemma_eqv_semantics v w (Refl v) e w ev_e_v
  _       -> impossible ("by lemma" ? lem_bool_values v p_v_b)
lem_equals_evals TInt  z p e v ev_e_v p_v_b = case v of
  (Ic n) -> AddStep (App (App (AppT (Prim Eql) (TRefn TInt z p)) v) e) (App (App (Prim Eq) v) e) step_one
                    (Bc True) ev_eq_tt
    where
      st_eql_eqv = EPrimT Eql (TRefn TInt z p) -- equals b ~> Prim Eq
      step_app   = EApp1 (AppT (Prim Eql) (TRefn TInt z p)) (Prim Eq) st_eql_eqv v
      step_one   = EApp1 (App (AppT (Prim Eql) (TRefn TInt z p)) v) (App (Prim Eq) v) step_app e
      ev_eq_tt   = lemma_eq_semantics v n (Refl v) e n ev_e_v
  _      -> impossible ("by lemma" ? lem_int_values v p_v_b)
lem_equals_evals b     z p e v ev_e_v p_v_b = impossible ("by lemma" ? lem_base_types_star b p_emp_b)
    where
      p_emp_b = lem_ftyping_wfft FEmpty v (FTBasic b) p_v_b WFFEmpty

{-@ lem_strengthen_evals_tt :: p1:Pred -> p2:Pred
        -> ProofOf(HasFType FEmpty p1 (FTBasic TBool)) 
        -> ProofOf(EvalsTo p1 (Bc True)) -> ProofOf(EvalsTo p2 (Bc True))
        -> ProofOf(EvalsTo (strengthen p1 p2) (Bc True)) @-}
lem_strengthen_evals_tt :: Expr -> Expr -> HasFType -> EvalsTo -> EvalsTo -> EvalsTo
lem_strengthen_evals_tt p1 p2 pf_p1v_bl ev_p1v_tt ev_p2v_tt 
  = lemma_strengthen_semantics p1 True ev_p1v_tt  p2 True ev_p2v_tt pf_p1v_bl

{-@ lem_strengthen_evals_subBV :: p1:Pred -> p2:Pred -> v:Value
        -> ProofOf(HasFType FEmpty (subBV 0 v p1) (FTBasic TBool)) 
        -> ProofOf(EvalsTo (subBV 0 v p1) (Bc True)) -> ProofOf(EvalsTo (subBV 0 v p2) (Bc True)) 
        -> ProofOf(EvalsTo (subBV 0 v (strengthen p1 p2)) (Bc True)) @-}
lem_strengthen_evals_subBV :: Expr -> Expr -> Expr -> HasFType -> EvalsTo -> EvalsTo -> EvalsTo
lem_strengthen_evals_subBV p1 p2 v pf_p1v_bl ev_p1v_tt ev_p2v_tt 
  = lemma_strengthen_semantics (subBV 0 v p1) True ev_p1v_tt (subBV 0 v p2) True ev_p2v_tt pf_p1v_bl
                               ? lem_subBV_strengthen  0 v p1 p2 
*)