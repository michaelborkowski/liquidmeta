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
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import SystemFAlphaEquivalence
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF

{-@ reflect foo40 @-}
foo40 x = Just x
foo40 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_selfify_wf :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) -> e:Expr
        -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFType g (self t e k) k) @-}
lem_selfify_wf :: Env -> Type -> Kind -> WFType -> Expr -> HasFType -> WFType
lem_selfify_wf g t@(TRefn b z p) k p_g_t e p_e_t = case p_g_t of
  (WFBase _g b tt)                       -> case b of
    TBool -> undefined
    TInt  -> undefined 
  (WFRefn _g _z _b tt p_g_b _p  y pf_p_bl) -> case b of
    TBool -> undefined {- WFRefn g' z b p' w pf_p'_bl 
      where
        g'          = Cons x t g
        w           = fresh_var g' ? lem_free_subset_binds g t p_g_t
        g''         = BCons w (BTBase b) (erase_env g')
        pf_pw_bl    = lem_change_var_btyp (erase_env g) y (BTBase b) BEmpty (unbind z y p) (BTBase TBool) 
                                          pf_p_bl w ? lem_subFV_unbind z y (FV w) p
        pf_pwx_bl   = lem_weaken_btyp (erase_env g) (BCons w (BTBase b) BEmpty) (unbind z w p) (BTBase TBool)
                                          pf_pw_bl x (BTBase TBool) -- erase t
        p'          = App (App (Prim And) p) (App (App (Prim Eqv) (BV z)) (FV x))
        blbl        = BTFunc (BTBase TBool) (BTBase TBool)
        app_eqv1    = BTApp g'' (Prim Eqv) (BTBase TBool) blbl (BTPrm g'' Eqv) 
                            (FV w) (BTVar1 (erase_env g') w (BTBase b))
        app_eqv2    = BTApp g'' (App (Prim Eqv) (FV w)) (BTBase TBool) (BTBase TBool) app_eqv1
                            (FV x) (BTVar2 (erase_env g') x (BTBase TBool) 
                                           (BTVar1 (erase_env g) x (BTBase TBool)) w (BTBase b))
        app_and1    = BTApp g'' (Prim And) (BTBase TBool) blbl (BTPrm g'' And)
                            (unbind z w p) pf_pwx_bl
        {-@ pf_p'_bl :: ProofOf(HasBType g'' (unbind z w p') (BTBase TBool)) @-}
        pf_p'_bl    = BTApp g'' (App (Prim And) (unbind z w p)) (BTBase TBool) (BTBase TBool) app_and1
                            (App (App (Prim Eqv) (FV w)) (FV x)) app_eqv2
--                            ? lem_fv_subset_bindsB g'' (unbind z w  -}
    TInt  -> undefined {-WFRefn g' z b p' w pf_p'_bl
      where
        g'          = Cons x t g
        w           = fresh_var g' ? lem_free_subset_binds g t p_g_t
        g''         = BCons w (BTBase b) (erase_env g')
        pf_pw_bl    = lem_change_var_btyp (erase_env g) y (BTBase b) BEmpty (unbind z y p) (BTBase TBool) 
                                          pf_p_bl w ? lem_subFV_unbind z y (FV w) p
        pf_pwx_bl   = lem_weaken_btyp (erase_env g) (BCons w (BTBase b) BEmpty) (unbind z w p) (BTBase TBool)
                                          pf_pw_bl x (BTBase TInt) -- erase t
        p'          = App (App (Prim And) p) (App (App (Prim Eq) (BV z)) (FV x))
        blbl        = BTFunc (BTBase TBool) (BTBase TBool)
        intbl       = BTFunc (BTBase TInt) (BTBase TBool)
        app_eqv1    = BTApp g'' (Prim Eq) (BTBase TInt) intbl (BTPrm g'' Eq) 
                            (FV w) (BTVar1 (erase_env g') w (BTBase b))
        app_eqv2    = BTApp g'' (App (Prim Eq) (FV w)) (BTBase TInt) (BTBase TBool) app_eqv1
                            (FV x) (BTVar2 (erase_env g') x (BTBase TInt) 
                                           (BTVar1 (erase_env g) x (BTBase TInt)) w (BTBase b))
        app_and1    = BTApp g'' (Prim And) (BTBase TBool) blbl (BTPrm g'' And)
                            (unbind z w p) pf_pwx_bl
        {-@ pf_p'_bl :: ProofOf(HasBType g'' (unbind z w p') (BTBase TBool)) @-}
        pf_p'_bl    = BTApp g'' (App (Prim And) (unbind z w p)) (BTBase TBool) (BTBase TBool) app_and1
                            (App (App (Prim Eq) (FV w)) (FV x)) app_eqv2-}
    (FTV a) -> undefined
    (BTV a) -> undefined
  (WFVar1 {}) -> undefined
  (WFVar2 {}) -> undefined
  (WFVar3 {}) -> undefined
  (WFKind {}) -> undefined
lem_selfify_wf g t@(TExists z t_z t') k p_g_t e p_e_t = undefined
lem_selfify_wf g t                    k p_g_t e p_e_t = p_g_t

{-@ lem_strengthen_ftyping :: g:FEnv ->  p:Pred -> r:Pred
        -> ProofOf(HasFType g p (FTBasic TBool))
        -> ProofOf(HasFType g r (FTBasic TBool))
        -> ProofOf(HasFType g (strengthen p r) (FTBasic TBool)) @-}
lem_strengthen_ftyping :: FEnv -> Pred -> Pred -> HasFType -> HasFType -> HasFType
lem_strengthen_ftyping g (App (App (Prim Conj) q) q') r pf_p_bl pf_r_bl = case pf_p_bl of
  (FTApp _ _p' bl _bl pf_p'_blbl _q' pf_q'_bl) -> case pf_p'_blbl of
    (FTApp _ _ _blbl _bl2 _ _ pf_q_bl) -> undefined {-lem_strengthen_ftyping g q qr pf_q_bl pf_qr_bl
      where
        qr       = strengthen q' r
        pf_qr_bl = lem_strengthen_ftyping g q' r pf_q'_bl pf_r_bl -}
lem_strengthen_ftyping g p r pf_p_bl pf_r_bl 
  = FTApp g (App (Prim Conj) p) (FTBasic TBool) 
          (FTBasic TBool) pf_conjp_blbl r pf_r_bl
      where
        func_type     = (FTFunc (FTBasic TBool) (FTBasic TBool))
        pf_conjp_blbl = FTApp g (Prim Conj) (FTBasic TBool)  func_type
                              (FTPrm g Conj) p pf_p_bl

{-@ lem_push_wf :: g:Env -> t_a:UserType -> ProofOf(WFType g t_a Base) 
        -> x:Vname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> ProofOf(HasFType (FCons y (erase t_a) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(WFType g (push p t_a) Base) @-}
lem_push_wf :: Env -> Type -> WFType -> Vname -> Expr -> Vname -> HasFType -> WFType
lem_push_wf g t_a@(TRefn   b z   r) p_g_ta x p y p_yg_p_bl = undefined {-
  = WFRefn g z b tt p_g_tt (strengthen p r) y p_pr_bl
      where
        

makeWFType (Cons y t_a g) (TRefn b z (strengthen p r)) Base
               ? lem_subBV_strengthen 0 (FV y) p r-}
lem_push_wf g (TFunc   z t_z t) p_g_ta x p y p_yg_p_bl = p_g_ta
lem_push_wf g (TPoly   a' k' t) p_g_ta x p y p_yg_p_bl = p_g_ta

{-
{-@ lem_ftyping_eqlPred :: g:Env -> b:Basic -> z:RVname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> ProofOf(HasFType (FCons y (erase t_a) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) 
                       (App (App (AppT (Prim Eql) (TRefn b z p)) (FV y)) e) (FTBasic TBool)) @-}
lem_ftyping_eqlPred ::
lem_ftyping_eqlPred g b z p y p_g_ta ? pf_p_bl pf_e_b = undefined {-
  = FTApp yg (App (AppT (Prim Eql) (TRefn b z p)) (FV y)) 
      where
        yg         = FCons y (FTBasic b) (erase_env g)
        p_yg_ta    =
        a'_        = fresh_varF yg
        a'         = a'_ ? lem_fv_bound_in_fenv (erase_env g) e (FTBasic b) p_e_b a'_
        poly_type  = (FTFunc (FTBasic (BTV 1)) (FTFunc (FTBasic (BTV 1)) (FTBasic TBool)))
        pf_appt_?  = FTAppT yg (Prim Eql) 1 Base poly_type a' (TRefn b z p)  -- lemma using p_g_ta
                            p_yg_ta
-}
-}

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
          ae_sx_tx        = lem_erase_subtype g s_x t_x p_sx_tx
          eqv_z'env'_p_bl = lem_alpha_in_env_ftyp (erase_env g) (FCons z' (FTBasic b) (erase_env g')) 
                                                  x (erase s_x) (erase t_x) ae_sx_tx 
                                                  (unbind 0 z' p) (FTBasic TBool) (p_z'env_p_bl
                                                  ? lem_erase_concat (Cons x t_x g) g')
          p_z'env'_p_bl   = lem_eqvftyping_basic (FCons z' (FTBasic b) 
                                (concatF (FCons x (erase s_x) (erase_env g)) (erase_env g'))) 
                                (unbind 0 z' p) TBool eqv_z'env'_p_bl
                                ? lem_erase_concat (Cons x s_x g) g'
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
