{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasFTyping2
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import BasicPropsEraseTyping
import LemmasChangeVarWF
import LemmasWeakenWF

{-@ reflect foo40 @-}
foo40 x = Just x
foo40 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_selfify_wf :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) 
        -> ProofOf(WFFE (erase_env g)) -> e:Expr
        -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFType g (self t e k) k) @-}
lem_selfify_wf :: Env -> Type -> Kind -> WFType -> WFFE -> Expr -> HasFType -> WFType
lem_selfify_wf g t@(TRefn b z p) Base p_g_t p_g_wf e p_e_t 
  = lem_push_wf g t p_g_t p_g_wf (eqlPred t e) y p_yg_p_bl
      where
        y_        = fresh_var g
        y         = y_ ? lem_free_subset_binds g t Base p_g_t   
                       ? lem_fv_bound_in_fenv (erase_env g) e (erase t) p_e_t y_
                       ? lem_freeBV_emptyB (erase_env g) e (erase t) p_e_t
        p_yg_p_bl = lem_eqlPred_ftyping g b z p p_g_t p_g_wf y e p_e_t
                       ? lem_subBV_notin 0 (FV y) (App (AppT (Prim Eql) (TRefn b z p)) (FV y))
                       ? lem_subBV_notin 0 (FV y) e
                       ? lem_fv_subset_bindsF (erase_env g) e (erase t) p_e_t
lem_selfify_wf g t@(TExists z t_z t') Base p_g_t p_g_wf e p_e_t = case p_g_t of 
  (WFExis _ _z _tz k_z p_tz_wf _t' k' y'_ p_y'_t'_wf)
      -> WFExis g z t_z k_z p_tz_wf (self t' e Base) k' y' p_y'g_selft'
    where
      y'           = y'_ ? lem_fv_bound_in_fenv (erase_env g) e (erase t) p_e_t y'_
                         ? lem_freeBV_emptyB (erase_env g) e (erase t) p_e_t
      p_er_g_tz    = lem_erase_wftype g t_z k_z p_tz_wf
      p_y'g_wf     = WFFBind (erase_env g) p_g_wf y' (erase t_z) k_z p_er_g_tz
      p_y'g_e_t    = lem_weaken_ftyp (erase_env g) FEmpty p_g_wf e (erase t) p_e_t y' (erase t_z)
      p_y'g_selft' = lem_selfify_wf (Cons y' t_z g) (unbindT z y' t') Base p_y'_t'_wf p_y'g_wf
                                    e (p_y'g_e_t ? lem_erase_tsubBV z (FV y') t')
                                    ? lem_tsubBV_self z (FV y') t' (e
                                          ? lem_freeBV_emptyB (erase_env g) e (erase t) p_e_t) Base
lem_selfify_wf g t                    k p_g_t p_g_wf e p_e_t = p_g_t

{-@ lem_strengthen_ftyping :: g:FEnv ->  p:Pred -> r:Pred
        -> ProofOf(HasFType g p (FTBasic TBool))
        -> ProofOf(HasFType g r (FTBasic TBool))
        -> ProofOf(HasFType g (strengthen p r) (FTBasic TBool)) @-}
lem_strengthen_ftyping :: FEnv -> Pred -> Pred -> HasFType -> HasFType -> HasFType
lem_strengthen_ftyping g (App (App (Prim Conj) _q) _q') r pf_p_bl pf_r_bl = case pf_p_bl of
  (FTApp _ _p' bl _bl pf_p'_blbl q' pf_q'_bl) -> case pf_p'_blbl of
    (FTApp _ _ _blbl _bl2 pf_conj_bbb q pf_q_bl) -> case pf_conj_bbb of
      (FTPrm _ _) -> lem_strengthen_ftyping g q qr pf_q_bl pf_qr_bl
        where
          qr       = strengthen q' r
          pf_qr_bl = lem_strengthen_ftyping g q' r pf_q'_bl pf_r_bl 
lem_strengthen_ftyping g p r pf_p_bl pf_r_bl 
  = FTApp g (App (Prim Conj) p) (FTBasic TBool) 
          (FTBasic TBool) pf_conjp_blbl r pf_r_bl
      where
        func_type     = (FTFunc (FTBasic TBool) (FTBasic TBool))
        pf_conjp_blbl = FTApp g (Prim Conj) (FTBasic TBool)  func_type
                              (FTPrm g Conj) p pf_p_bl

{-@ lem_eqlPred_ftyping :: g:Env -> b:Basic -> z:RVname -> p:Pred
        -> ProofOf(WFType g (TRefn b z p) Base) -> ProofOf(WFFE (erase_env g))
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> e:Expr -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g))
                            (App (App (AppT (Prim Eql) (TRefn b z p)) (FV y)) e) (FTBasic TBool)) @-}
lem_eqlPred_ftyping :: Env -> Basic -> RVname -> Pred {-> Kind-} -> WFType -> WFFE
                           -> Vname -> Expr -> HasFType -> HasFType
lem_eqlPred_ftyping g b z p {-k-} p_g_b p_g_wf y e p_e_t 
  = FTApp yg (App (AppT (Prim Eql) (TRefn b z p)) (FV y)) (FTBasic b) (FTBasic TBool)
          inner_app e p_yg_e_b
      where
        yg         = FCons y (FTBasic b) (erase_env g)
        inner_app  = FTApp  yg (AppT (Prim Eql) (TRefn b z p)) (FTBasic b)
                            (FTFunc (FTBasic b) (FTBasic TBool)) inner_appt 
                            (FV y) (FTVar1 (erase_env g) y (FTBasic b))
        inner_appt = FTAppT yg (Prim Eql) 1 Base poly_type (FTPrm yg Eql)
                            (TRefn b z (p ? lem_tfreeBV_empty g (TRefn b z p) Base p_g_b
                                         ? lem_free_subset_binds g (TRefn b z p) Base p_g_b))
                            p_er_yg_b
        poly_type  = (FTFunc (FTBasic (BTV 1)) (FTFunc (FTBasic (BTV 1)) (FTBasic TBool)))
        p_er_g_b   = lem_erase_wftype g (TRefn b z p) Base p_g_b
        p_er_yg_b  = lem_weaken_wfft (erase_env g) FEmpty (FTBasic b) Base p_er_g_b y (FTBasic b)
        p_yg_e_b   = lem_weaken_ftyp (erase_env g) FEmpty p_g_wf e (FTBasic b) p_e_t y (FTBasic b)

{-@ lem_push_wf :: g:Env -> t_a:UserType -> ProofOf(WFType g t_a Base) 
        -> ProofOf(WFFE (erase_env g)) -> p:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> ProofOf(HasFType (FCons y (erase t_a) (erase_env g)) (unbind 0 y p) (FTBasic TBool))
        -> ProofOf(WFType g (push p t_a) Base) @-}
lem_push_wf :: Env -> Type -> WFType -> WFFE -> Expr -> Vname -> HasFType -> WFType
lem_push_wf g t_a@(TRefn   b z   r) p_g_ta p_g_wf p y p_yg_p_bl = case p_g_ta of
  (WFBase _ _ _r) -> WFRefn g z b r p_g_ta (strengthen p r) (y ? lem_trivial_nofv r)  p_pr_bl
      where
        p_yg_r_bl  = makeHasFType (FCons y (FTBasic b) (erase_env g)) 
                                  (r ? lem_trivial_nodefns r)
                                  (FTBasic TBool 
                                    ? lem_trivial_check (FCons y (FTBasic b) (erase_env g)) r)
        p_pr_bl    = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p)
                                         (unbind 0 y r) p_yg_p_bl 
                                         (p_yg_r_bl ? lem_subBV_notin 0 (FV y) (r ? lem_trivial_nobv r))
                                         ? lem_subBV_strengthen 0 (FV y) p r
  (WFVar1 _ _ _r _)       -> WFRefn g z b r p_g_ta (strengthen p r) (y ? lem_trivial_nofv r)  p_pr_bl
      where
        p_yg_r_bl  = makeHasFType (FCons y (FTBasic b) (erase_env g)) 
                                  (r ? lem_trivial_nodefns r)
                                  (FTBasic TBool 
                                    ? lem_trivial_check (FCons y (FTBasic b) (erase_env g)) r)
        p_pr_bl    = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p)
                                         (unbind 0 y r) p_yg_p_bl 
                                         (p_yg_r_bl ? lem_subBV_notin 0 (FV y) (r ? lem_trivial_nobv r))
                                         ? lem_subBV_strengthen 0 (FV y) p r
  (WFVar2 _ _ _r _ _ _ _) -> WFRefn g z b r p_g_ta (strengthen p r) (y ? lem_trivial_nofv r)  p_pr_bl
      where
        p_yg_r_bl  = makeHasFType (FCons y (FTBasic b) (erase_env g)) 
                                  (r ? lem_trivial_nodefns r)
                                  (FTBasic TBool 
                                    ? lem_trivial_check (FCons y (FTBasic b) (erase_env g)) r)
        p_pr_bl    = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p)
                                         (unbind 0 y r) p_yg_p_bl 
                                         (p_yg_r_bl ? lem_subBV_notin 0 (FV y) (r ? lem_trivial_nobv r))
                                         ? lem_subBV_strengthen 0 (FV y) p r
  (WFVar3 _ _ _r _ _ _ _) -> WFRefn g z b r p_g_ta (strengthen p r) (y ? lem_trivial_nofv r) p_pr_bl
      where
        p_yg_r_bl  = makeHasFType (FCons y (FTBasic b) (erase_env g)) 
                                  (r ? lem_trivial_nodefns r)
                                  (FTBasic TBool 
                                    ? lem_trivial_check (FCons y (FTBasic b) (erase_env g)) r)
        p_pr_bl    = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p)
                                         (unbind 0 y r) p_yg_p_bl
                                         (p_yg_r_bl ? lem_subBV_notin 0 (FV y) (r ? lem_trivial_nobv r))
                                         ? lem_subBV_strengthen 0 (FV y) p r
  (WFRefn _ _ _ tt p_g_tt _r y' p_y'g_r_bl) -> WFRefn g z b tt p_g_tt (strengthen p r) 
                                                 (y ? lem_free_bound_in_env g t_a Base p_g_ta y) p_pr_bl
      where
        p_er_g_ta  = lem_erase_wftype g t_a Base p_g_ta
        p_y'g_wf   = WFFBind (erase_env g) p_g_wf y' (erase t_a) Base p_er_g_ta
        p_yg_r_bl  = lem_change_var_ftyp (erase_env g) y' (erase t_a) FEmpty p_y'g_wf
                                         (unbind 0 y' r) (FTBasic TBool) p_y'g_r_bl y
                                         ? lem_subFV_unbind 0 y' (FV y) r
        p_pr_bl    = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p)
                                         (unbind 0 y r) p_yg_p_bl p_yg_r_bl
                                         ? lem_subBV_strengthen 0 (FV y) p r
lem_push_wf g (TFunc   z t_z t) p_g_ta p_g_wf p y p_yg_p_bl = p_g_ta
lem_push_wf g (TPoly   a' k' t) p_g_ta p_g_wf p y p_yg_p_bl = p_g_ta

{-@ lem_push_trivial_wf :: g:Env -> t_a:UserType -> k_a:Kind -> ProofOf(WFType g t_a k_a) 
        -> ProofOf(WFFE (erase_env g)) -> { tt:Pred | isTrivial tt } 
        -> ProofOf(WFType g (push tt t_a) k_a) @-}
lem_push_trivial_wf :: Env -> Type -> Kind -> WFType -> WFFE -> Expr -> WFType
lem_push_trivial_wf g t_a@(TRefn   b z   r) Base p_g_ta p_g_wf tt 
  = lem_push_wf g t_a p_g_ta p_g_wf tt (y ? lem_trivial_nofv tt) p_yg_tt_bl
      where
        y          = fresh_var g
        p_yg_tt_bl = makeHasFType (FCons y (FTBasic b) (erase_env g))
                                  (tt ? lem_trivial_nodefns tt)
                                  (FTBasic TBool 
                                     ? lem_trivial_check (FCons y (FTBasic b) (erase_env g)) tt)
                                  ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)
lem_push_trivial_wf g t_a@(TRefn   b z   r) Star p_g_ta p_g_wf tt  = case p_g_ta of
  (WFVar1 g' a _r _) -> WFVar1 g' a (strengthen tt r ? lem_strengthen_trivial tt r) Star
  (WFVar2 g' a _r _ p_g'_ta y t) -> WFVar2 g' a (strengthen tt r ? lem_strengthen_trivial tt r) Star
                                           p_g'_ttr y t
    where
      (WFFBind _ p_g'_wf _ _ _ _) = p_g_wf
      p_g'_ttr = lem_push_trivial_wf g' t_a Star p_g'_ta p_g'_wf tt
  (WFVar3 g' a _r _ p_g'_ta a' k') -> WFVar3 g' a (strengthen tt r ? lem_strengthen_trivial tt r) Star
                                             p_g'_ttr a' k'
    where
      (WFFBindT _ p_g'_wf _ _) = p_g_wf
      p_g'_ttr = lem_push_trivial_wf g' t_a Star p_g'_ta p_g'_wf tt
  (WFKind _ _ p_g_ta_base) -> WFKind g (push tt t_a) p_g_ttr_base
    where
      p_g_ttr_base = lem_push_trivial_wf g t_a Base p_g_ta_base p_g_wf tt
lem_push_trivial_wf g (TFunc  z t_z t) k p_g_ta p_g_wf tt = p_g_ta
lem_push_trivial_wf g (TPoly  a' k' t) k p_g_ta p_g_wf tt = p_g_ta 

{-@ lem_subtype_in_env_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> { x:Vname | (not (in_env x g)) && not (in_env x g') }
      -> s_x:Type -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> t:Type -> k:Kind
      -> ProofOf(WFType (concatE (Cons x t_x g) g') t k)
      -> ProofOf(WFType (concatE (Cons x s_x g) g') t k) @-} 
lem_subtype_in_env_wf :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Type -> Kind -> WFType -> WFType
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFBase env b tt)
    = WFBase (concatE (Cons x s_x g) g') b tt
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFRefn env z b tt p_env_b p z'_ p_z'env_p_bl) 
    = WFRefn (concatE (Cons x s_x g) g') z b tt p_env'_b p z' p_z'env'_p_bl
        where
          z'              = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_
                                ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_b        = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx (TRefn b Z tt) Base p_env_b
          p_z'env'_p_bl   = p_z'env_p_bl ? lem_erase_concat (Cons x s_x g) g' -- (Cons z' (FTBasic b) g')
                                         ? lem_erase_concat (Cons x t_x g) g' -- (Cons z' (FTBasic b) g')
                                         ? lem_erase_subtype g s_x t_x p_sx_tx
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFVar1 env a tt k_a) = case g' of
    Empty              -> impossible "a <> x"
    (ConsT _a _ka g'') -> WFVar1 (concatE (Cons x s_x g) g'') a tt k_a
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFVar2 env a_ tt k_a p_env_a z t_z) = case g' of
    Empty             -> WFVar2 g                            a_ tt k_a p_env_a  z s_x
    (Cons _z _tz g'') -> WFVar2 (concatE (Cons x s_x g) g'') a  tt k_a p_env'_a z t_z
      where
        a        = a_ ? lem_in_env_concat (Cons x t_x g) g'' a_
                      ? lem_in_env_concat (Cons x s_x g) g'' a_
        p_env'_a = lem_subtype_in_env_wf g g'' x s_x t_x p_sx_tx (TRefn (FTV a) Z tt) k_a p_env_a
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFVar3 env a_ tt k_a p_env_a a1 k1) = case g' of
    Empty               -> impossible "a1 <> x"
    (ConsT _a1 _k1 g'') -> WFVar3 (concatE (Cons x s_x g) g'') a  tt k_a p_env'_a a1 k1
      where
        a        = a_ ? lem_in_env_concat (Cons x t_x g) g'' a_
                      ? lem_in_env_concat (Cons x s_x g) g'' a_
        p_env'_a = lem_subtype_in_env_wf g g'' x s_x t_x p_sx_tx (TRefn (FTV a) Z tt) k_a p_env_a
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFFunc env z t_z k_z p_env_tz t' k' z'_ p_z'env_t')
    = WFFunc (concatE (Cons x s_x g) g') z t_z k_z p_env'_tz t' k' z' p_z'env'_t'
        where
          z'          = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                            ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z k_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') k' p_z'env_t'
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFExis env z t_z k_z p_env_tz t' k' z'_ p_z'env_t')
    = WFExis (concatE (Cons x s_x g) g') z t_z k_z p_env'_tz t' k' z' p_z'env'_t'
        where
          z'          = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                            ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z k_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') k' p_z'env_t'
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFPoly env a k_a t' k_t' a'_ p_a'env_t')
    = WFPoly (concatE (Cons x s_x g) g') a k_a t' k_t' a' p_a'_env'_t'
        where
          a'           = a'_ ? lem_in_env_concat (Cons x t_x g) g' a'_
                             ? lem_in_env_concat (Cons x s_x g) g' a'_
          p_a'_env'_t' = lem_subtype_in_env_wf g (ConsT a' k_a g') x s_x t_x p_sx_tx 
                                               (unbind_tvT a a' t') k_t' p_a'env_t'
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFKind env _t p_env_t_base)
    = WFKind (concatE (Cons x s_x g) g') t p_env'_t_base
        where
          p_env'_t_base = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t Base p_env_t_base

{-@ lem_narrow_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type
        -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> k_x:Kind -> ProofOf(WFType g s_x k_x)
        -> ProofOf(WFEnv (concatE (Cons x t_x g) g') )
        -> ProofOf(WFEnv (concatE (Cons x s_x g) g') ) / [envsize g'] @-}
lem_narrow_wfenv :: Env -> Env -> Vname -> Type -> Type -> Subtype 
                        -> Kind -> WFType -> WFEnv -> WFEnv
lem_narrow_wfenv g Empty           x s_x t_x p_sx_tx k_x p_g_sx p_xg_wf  = case p_xg_wf of
  (WFEBind  _g p_g_wf _x _tx _kx p_env'_tx) -> WFEBind g p_g_wf x s_x k_x p_g_sx
lem_narrow_wfenv g (Cons z t_z g') x s_x t_x p_sx_tx k_x p_g_sx p_env_wf = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz k_z p_env'_tz) -> WFEBind env'' p_env''_wf z t_z k_z p_env''_tz
      where
        env''        = concatE (Cons x s_x g) g'
        p_env''_wf   = lem_narrow_wfenv      g g' x s_x t_x p_sx_tx k_x p_g_sx p_env'_wf
        p_env''_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z k_z p_env'_tz
lem_narrow_wfenv g (ConsT a k  g') x s_x t_x p_sx_tx k_x p_g_sx p_env_wf = case p_env_wf of
  (WFEBindT env' p_env'_wf _a _k) -> WFEBindT env'' p_env''_wf a k 
      where
        env''        = concatE (Cons x s_x g) g'
        p_env''_wf   = lem_narrow_wfenv      g g' x s_x t_x p_sx_tx k_x p_g_sx p_env'_wf
