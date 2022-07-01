{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import LocalClosure
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasWeaken
import Typing

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_unbindFT_equals :: a:Vname -> { t1:FType | not (Set_mem a (ffreeTV t1)) }
        -> { t2:FType | unbindFT a t1 == unbindFT a t2 && not (Set_mem a (ffreeTV t2)) }
        -> { pf:_ | t1 == t2 } @-}
lem_unbindFT_equals :: Vname -> FType -> FType -> Proof
lem_unbindFT_equals a t1 t2 = lem_openFT_at_equals 0 a t1 t2

{-@ lem_openFT_at_equals :: j:Index -> a:Vname -> { t1:FType | not (Set_mem a (ffreeTV t1)) }
        -> { t2:FType | openFT_at j a t1 == openFT_at j a t2 && not (Set_mem a (ffreeTV t2)) }
        -> { pf:_ | t1 == t2 } @-}
lem_openFT_at_equals :: Index -> Vname -> FType -> FType -> Proof
lem_openFT_at_equals j a (FTBasic b) (FTBasic _) = case b of
  (BTV i) | i == j -> ()
  _                -> ()
lem_openFT_at_equals j a (FTFunc t11 t12) (FTFunc t21 t22)
  = () ? lem_openFT_at_equals j a t11 t21
       ? lem_openFT_at_equals j a t12 t22
lem_openFT_at_equals j a (FTPoly k t1') (FTPoly _ t2')
  = () ? lem_openFT_at_equals (j+1) a t1' t2'

-- LEMMA 6. If G |- s <: t, then if we erase the types then (erase s) == (erase t)
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type 
        -> { p_t1_t2:Subtype | propOf p_t1_t2 == Subtype g t1 t2 }
        -> { pf:_ | erase t1 == erase t2 } / [subtypSize p_t1_t2] @-}
lem_erase_subtype :: Env -> Type -> Type  -> Subtype -> Proof
lem_erase_subtype g t1 t2 (SBase _g b p1 p2 _ _) = ()
lem_erase_subtype g s  t  (SFunc _g s1 t1 p_t1_s1 s2 t2 nms mk_p_s2_t2)
  = () ? lem_erase_subtype  g t1  s1  p_t1_s1
       ? lem_erase_subtype (Cons y t1 g) (unbindT y s2) (unbindT y t2)  (mk_p_s2_t2 y)
      where 
        y         = fresh_var nms g
lem_erase_subtype g t1  t2 (SWitn _g v t_x p_v_tx _t1 t' p_t1_t'v)
  = () ? lem_erase_subtype g t1 (tsubBV v t')  p_t1_t'v 
lem_erase_subtype g t1  t2 (SBind _g t_x t _t2 nms mk_p_t_t')
  = () ? lem_erase_subtype (Cons y t_x g) (unbindT y t)  t2  (mk_p_t_t' y)
      where
        y         = fresh_var nms g 
lem_erase_subtype g t1 t2  (SPoly _g k t1' t2' nms mk_p_ag_t1'_t2')
  = () ? lem_erase_subtype (ConsT a k g) 
                      (unbind_tvT a t1'   ? lem_erase_unbind_tvT a t1')
                      (unbind_tvT a t2'   ? lem_erase_unbind_tvT a t2')
                      (mk_p_ag_t1'_t2' a) ? lem_unbindFT_equals a (erase t1') (erase t2')
          where
            a = fresh_varFTs nms g (erase t1') (erase t2') 

{-@ lem_selfify_wf :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k) -> e:Expr
        -> ProofOf(HasFType (erase_env g) e (erase t))
        -> ProofOf(WFType g (self t e k) k) / [tsize t] @-}
lem_selfify_wf :: Env -> Type -> Kind -> WFType  -> Expr -> HasFType -> WFType
lem_selfify_wf g t@(TRefn b ps) Base p_g_t  e p_e_t 
  = lem_push_wf g t p_g_t         (PCons  (eqlPred (TRefn b ps) e) PEmpty)
                nms mk_p_yg_p_bl
      where
        {-@ mk_p_yg_p_bl :: { y:Vname | NotElem y nms }
               -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env g))
                            (PCons (unbind y (eqlPred (TRefn b ps) e)) PEmpty)) @-}
        mk_p_yg_p_bl y = PFTCons (FCons y (FTBasic b) (erase_env g))
                                 (unbind y  (eqlPred (TRefn b ps) e)) p_eqlPred_bl
                                 PEmpty (PFTEmp (FCons y (FTBasic b) (erase_env g))) 
                                 ? toProof ( unbindP y PEmpty === PEmpty )
                             ? lem_ftyp_islc (erase_env g) e (erase t) p_e_t
          where
            p_eqlPred_bl = lem_eqlPred_ftyping g b ps p_g_t y e p_e_t
        nms       = unionEnv [] g
lem_selfify_wf g t@(TExists t_z t') Base p_g_t  e p_e_t = case p_g_t of 
  (WFExis _ _tz k_z p_tz_wf _t' k' nms mk_p_y_t'_wf)
      -> WFExis g t_z k_z p_tz_wf (self t' e Base) k' nms' mk_p_y_selft'
    where
      {-@ mk_p_y_selft' :: { y:Vname | NotElem y nms' }
                -> ProofOf(WFType (Cons y t_z g) (unbindT y (self t' e Base)) k') @-}
      mk_p_y_selft' y = lem_selfify_wf (Cons y t_z g) (unbindT y t') Base (mk_p_y_t'_wf y)
                                       e (p_yg_e_t) ? lem_unbindT_self y t' (e 
                                           ? lem_ftyp_islc (erase_env g) e (erase t) p_e_t) Base
        where                           
          p_yg_e_t    = lem_weaken_ftyp (erase_env g) FEmpty  e (erase t) p_e_t y (erase t_z)
      nms'            = unionEnv nms g
lem_selfify_wf g t                    k p_g_t  e p_e_t = p_g_t

{-@ lem_strengthen_ftyping :: g:FEnv ->  ps:Preds -> rs:Preds
        -> ProofOf(PHasFType g ps) -> ProofOf(PHasFType g rs)
        -> ProofOf(PHasFType g (strengthen ps rs)) @-}
lem_strengthen_ftyping :: FEnv -> Preds -> Preds -> PHasFType -> PHasFType -> PHasFType
lem_strengthen_ftyping g ps rs (PFTEmp  _)                       p_rs_bl = p_rs_bl 
lem_strengthen_ftyping g ps rs (PFTCons _ p p_p_bl ps' p_ps'_bl) p_rs_bl
    = PFTCons g p p_p_bl (strengthen ps' rs) p_ps'rs_bl
        where
          p_ps'rs_bl = lem_strengthen_ftyping g ps' rs p_ps'_bl p_rs_bl

{-@ lem_eqlPred_ftyping :: g:Env -> b:Basic -> ps:Preds -> ProofOf(WFType g (TRefn b ps) Base)   
        -> { y:Vname | not (in_env y g) } -> e:Expr -> ProofOf(HasFType (erase_env g) e (FTBasic b))
        -> ProofOf(HasFType (FCons y (FTBasic b) (erase_env g)) 
                            (unbind y (eqlPred (TRefn b ps) e)) (FTBasic TBool)) @-}
lem_eqlPred_ftyping :: Env -> Basic -> Preds -> WFType -> Vname -> Expr -> HasFType -> HasFType
lem_eqlPred_ftyping g b ps  p_g_b y e p_e_t 
  = FTApp yg (App (AppT (Prim Eql) (TRefn b PEmpty)) (FV y))  (FTBasic b) (FTBasic TBool)
          inner_app e p_yg_e_b   ? lem_ftyp_islc (erase_env g) e (FTBasic b) p_e_t
                                 ? lem_open_at_lc_at 0 y 0 0 e
                                 ? lem_open_at_eqlPred  y  b ps e
      where
        yg         = FCons y (FTBasic b) (erase_env g)
        inner_app  = FTApp  yg (AppT (Prim Eql)  (TRefn b PEmpty)) 
                            (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool)) inner_appt 
                            (FV y) (FTVar1 (erase_env g) y (FTBasic b))
        inner_appt = FTAppT yg (Prim Eql) Base poly_type (FTPrm yg Eql)
                            (TRefn b PEmpty ? lem_wftype_islct g (TRefn b PEmpty) Base p_g_b'
                                            ? lem_free_subset_binds g (TRefn b PEmpty) Base p_g_b')
                            p_er_yg_b
        poly_type  = (FTFunc (FTBasic (BTV 0)) (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))
        p_g_b'     = lem_wf_pempty_for_wf_trefn g b ps Base p_g_b
        p_er_g_b   = lem_erase_wftype g (TRefn b ps) Base p_g_b
        p_er_yg_b  = lem_weaken_wfft (erase_env g) FEmpty (FTBasic b) Base p_er_g_b y (FTBasic b)
        p_yg_e_b   = lem_weaken_ftyp (erase_env g) FEmpty e (FTBasic b) p_e_t y (FTBasic b)

{-@ lem_push_wf :: g:Env -> t_a:UserType -> ProofOf(WFType g t_a Base) 
        -> ps:Preds -> nms:Names
        -> ( { y:Vname | NotElem y nms }
                 -> ProofOf(PHasFType (FCons y (erase t_a) (erase_env g)) (unbindP y ps)) )
        -> ProofOf(WFType g (push ps t_a) Base) @-}
lem_push_wf :: Env -> Type -> WFType -> Preds -> Names -> (Vname -> PHasFType) -> WFType
lem_push_wf g t_a@(TRefn  b rs) p_g_ta ps nms mk_p_yg_ps_bl = case ps of
  PEmpty        -> p_g_ta ? lem_push_empty t_a --_wf g t_a Base p_g_ta 
  (PCons p ps') -> case rs of
    PEmpty           -> WFRefn g b p_g_ta ps nms mk_p_yg_ps_bl  ? lem_strengthen_empty ps
    (PCons r rs')    -> case p_g_ta of
      (WFRefn _ _ p_g_b _rs nms' mk_p_yg_rs_bl) -> WFRefn g b p_g_b (strengthen ps rs)
                                                      nms'' mk_p_yg_psrs_bl
        where
          {-@ mk_p_yg_psrs_bl :: { y:Vname | NotElem y nms'' }
                -> ProofOf(PHasFType (FCons y (FTBasic b) (erase_env g))
                                     (unbindP y (strengthen ps rs))) @-}
          mk_p_yg_psrs_bl y = lem_strengthen_ftyping (FCons y (FTBasic b) (erase_env g)) (unbindP y ps)
                                           (unbindP y rs) (mk_p_yg_ps_bl y) (mk_p_yg_rs_bl y)
                                           ? lem_unbindP_strengthen y ps rs
          nms''             = unionFEnv (union nms nms') (erase_env g)
lem_push_wf g (TFunc   t_z t) p_g_ta ps nms mk_p_yg_p_bl = p_g_ta
lem_push_wf g (TPoly    k' t) p_g_ta ps nms mk_p_yg_p_bl = p_g_ta

{-@ lem_tvar_v_in_env :: g:Env -> x:Vname -> t:Type -> ProofOf(HasType g (FV x) t)
          -> { pf:_ | S.member x (vbinds g) } @-}
lem_tvar_v_in_env :: Env -> Vname -> Type -> HasType -> Proof
lem_tvar_v_in_env g x t (TVar1 _  _x _t _ _) = ()
lem_tvar_v_in_env g x t (TVar2 g' _x _t p_g'_x_t y t_y)
  = lem_tvar_v_in_env g' x t p_g'_x_t
lem_tvar_v_in_env g x t (TVar3 g' _x _t p_g'_x_t a k_a)
  = lem_tvar_v_in_env g' x t p_g'_x_t
lem_tvar_v_in_env g x t (TSub _ _ s p_x_s _ k p_g_t p_s_t)
  = lem_tvar_v_in_env g x s p_x_s

{-@ lem_narrow_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> { x:Vname | (not (in_env x g)) && not (in_env x g') } 
      -> s_x:Type -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> t:Type -> k:Kind
      -> ProofOf(WFType (concatE (Cons x t_x g) g') t k)
      -> ProofOf(WFType (concatE (Cons x s_x g) g') t k) / [ tsize t, envsize g', ksize k] @-} 
lem_narrow_wf :: Env -> Env -> Vname -> Type -> Type
                     -> Subtype -> Type -> Kind -> WFType -> WFType
lem_narrow_wf g g' x s_x t_x  p_sx_tx t k (WFBase env b)
    = WFBase (concatE (Cons x s_x g) g') b
lem_narrow_wf g g' x s_x t_x  p_sx_tx t k 
              (WFRefn env b p_env_b ps nms mk_p_zenv_ps_bl) 
    = WFRefn (concatE (Cons x s_x g) g') b p_env'_b ps nms' mk_p_zenv'_ps_bl
        where
          p_env'_b           = lem_narrow_wf g g' x s_x t_x p_sx_tx (TRefn b PEmpty) Base p_env_b
          mk_p_zenv'_ps_bl   = mk_p_zenv_ps_bl 
                                         ? lem_erase_concat (Cons x s_x g) g' 
                                         ? lem_erase_concat (Cons x t_x g) g' 
                                         ? lem_erase_subtype g s_x t_x  p_sx_tx
          nms'             = unionEnv nms g
lem_narrow_wf g g' x s_x t_x p_sx_tx t k (WFVar1 env a k_a) = case g' of
    Empty              -> impossible "a <> x"
    (ConsT _a _ka g'') -> WFVar1 (concatE (Cons x s_x g) g'') a k_a
lem_narrow_wf g g' x s_x t_x p_sx_tx t k (WFVar2 env a_ k_a p_env_a z t_z) = case g' of
    Empty             -> WFVar2 g                            a_ k_a p_env_a  z  s_x
    (Cons _z _tz g'') -> WFVar2 (concatE (Cons x s_x g) g'') a  k_a p_env'_a z  t_z
      where
        a        = a_ ? lem_in_env_concat (Cons x t_x g) g'' a_
                      ? lem_in_env_concat (Cons x s_x g) g'' a_
        p_env'_a = lem_narrow_wf g g'' x s_x t_x p_sx_tx (TRefn (FTV a) PEmpty) k_a p_env_a
lem_narrow_wf g g' x s_x t_x p_sx_tx t k (WFVar3 env a_ k_a p_env_a a1  k1) = case g' of
    Empty               -> impossible "a1 <> x"
    (ConsT _a1 _k1 g'') -> WFVar3 (concatE (Cons x s_x g) g'') a  k_a p_env'_a a1 k1
      where
        a        = a_ ? lem_in_env_concat (Cons x t_x g) g'' a_
                      ? lem_in_env_concat (Cons x s_x g) g'' a_
        p_env'_a = lem_narrow_wf g g'' x s_x t_x p_sx_tx (TRefn (FTV a) PEmpty) k_a p_env_a
lem_narrow_wf g g' x s_x  t_x  p_sx_tx t k 
              (WFFunc env t_z k_z p_env_tz t' k' nms mk_p_zenv_t')
    = WFFunc (concatE (Cons x s_x g) g') t_z k_z p_env'_tz t' k' nms' mk_p_zenv'_t'
        where
          p_env'_tz       = lem_narrow_wf g g' x s_x  t_x p_sx_tx t_z k_z p_env_tz
          {-@ mk_p_zenv'_t' :: { z:Vname | NotElem z nms' }
                -> ProofOf(WFType (Cons z t_z (concatE (Cons x s_x g) g')) (unbindT z t') k') @-}
          mk_p_zenv'_t' z = lem_narrow_wf g (Cons z t_z g') x s_x t_x
                                          p_sx_tx (unbindT z t') k' (mk_p_zenv_t' z)
          nms'            = x:(unionEnv nms (concatE g g'))
lem_narrow_wf g g' x s_x t_x  p_sx_tx t k 
              (WFExis env t_z k_z p_env_tz t' k' nms mk_p_zenv_t')
    = WFExis (concatE (Cons x s_x g) g') t_z k_z p_env'_tz t' k' nms' mk_p_zenv'_t'
        where
          p_env'_tz       = lem_narrow_wf g g' x s_x  t_x  p_sx_tx t_z k_z p_env_tz
          {-@ mk_p_zenv'_t' :: { z:Vname | NotElem z nms' }
                -> ProofOf(WFType (Cons z t_z (concatE (Cons x s_x g) g')) (unbindT z t') k') @-}
          mk_p_zenv'_t' z = lem_narrow_wf g (Cons z t_z g') x s_x  t_x 
                                          p_sx_tx (unbindT z t') k' (mk_p_zenv_t' z)
          nms'            = x:(unionEnv nms (concatE g g'))
lem_narrow_wf g g' x s_x  t_x p_sx_tx t k (WFPoly env k_a t' k_t' nms mk_p_aenv_t')
    = WFPoly (concatE (Cons x s_x g) g') k_a t' k_t' nms' mk_p_aenv'_t'
        where
          {-@ mk_p_aenv'_t' :: { a:Vname | NotElem a nms' }
                -> ProofOf(WFType (ConsT a k_a (concatE (Cons x s_x g) g')) (unbind_tvT a t') k_t') @-}
          mk_p_aenv'_t' a = lem_narrow_wf g (ConsT a k_a g') x s_x t_x 
                                          p_sx_tx (unbind_tvT a t') k_t' (mk_p_aenv_t' a)
          nms'            = x:(unionEnv nms (concatE g g'))
lem_narrow_wf g g' x s_x  t_x  p_sx_tx t k (WFKind env _t p_env_t_base)
    = WFKind (concatE (Cons x s_x g) g') t p_env'_t_base
        where
          p_env'_t_base = lem_narrow_wf g g' x s_x t_x  p_sx_tx t Base p_env_t_base

{-@ lem_strengthen_wftype_base :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { x:Vname | not (in_env x g) && not (in_env x g') } 
        -> t_x:Type -> t:Type -> { p_g'g_t:WFType | propOf p_g'g_t == WFType (concatE g g') t Star }
        -> ProofOf(WFType (concatE (Cons x t_x g) g') t Base) 
        -> { pf:WFType | propOf pf == WFType (concatE g g') t Base } / [tsize t, envsize g'] @-}
lem_strengthen_wftype_base :: Env -> Env -> Vname -> Type -> Type -> WFType -> WFType -> WFType
lem_strengthen_wftype_base g g'  x t_x t@(TRefn b ps) p_g'g_t p_g'xg_t = case p_g'xg_t of
    (WFBase env _b)                                -> WFBase (concatE g g') b
    (WFRefn env _b p_env_b_b _ps nms mk_p_yenv_ps) -> case p_g'g_t of
        (WFKind _g'g _t p_g'g_t_b) -> p_g'g_t_b
    (WFVar1 env' a _base)                          -> case g' of
        Empty             -> impossible ""
        (Cons  _w _  g'') -> impossible ""
        (ConsT _a _b g'') -> WFVar1 (concatE g g'') a Base 
    (WFVar2 env' a _base p_env'_t_b y t_y)         -> case g' of
        Empty {-x == y -} -> p_env'_t_b
        (Cons _y _ty g'') -> case p_g'g_t of
            (WFVar2 _g''g _a _star p_g''g_t_st _ _) 
                -> WFVar2 (concatE g g'') a Base p_g''g_t_b y t_y
                     where
                       p_g''g_t_b = lem_strengthen_wftype_base g g'' x t_x t p_g''g_t_st p_env'_t_b
            (WFKind _g'g _t p_g'g_t_b)              -> p_g'g_t_b
        (ConsT _a' _ g'') -> impossible ""
    (WFVar3 env' a _base p_env'_t_b a1 k1)         -> case g' of 
        Empty {- x <> a1 -} -> impossible ""
        (Cons   _y _ty g'') -> impossible ""
        (ConsT _a1 _k1 g'') -> case p_g'g_t of
           (WFVar3 _g''g _a _star p_g''g_t_st _ _) 
               -> WFVar3 (concatE g g'') a Base p_g''g_t_b a1 k1
                    where
                      p_g''g_t_b = lem_strengthen_wftype_base g g'' x t_x t p_g''g_t_st p_env'_t_b
           (WFKind _g'g _t p_g'g_t_b)              -> p_g'g_t_b
lem_strengthen_wftype_base g g'  x t_x (TFunc t_z t') p_g'g_t p_g'xg_t
  = impossible ("by lemma" ? lem_wf_tfunc_star (concatE (Cons x t_x g) g') t_z t' p_g'xg_t)
lem_strengthen_wftype_base g g'  x t_x (TExists t_z t') p_g'g_t p_g'xg_t = case p_g'g_t of
  (WFExis _g'g _tz k_z p_g'g_tz _t' _st nms mk_p_yg'g_t') -- -> p_g'g_t_base
        -> WFExis (concatE g g') t_z k_z p_g'g_tz t' Base nms'' mk_p_yg'g_t'_b
    where
      {-@ mk_p_yg'g_t'_b :: { y:Vname | NotElem y nms'' }
            -> ProofOf(WFType (Cons y t_z (concatE g g')) (unbindT y t') Base) @-}
      mk_p_yg'g_t'_b y = lem_strengthen_wftype_base g (Cons y t_z g' ? lem_in_env_concat g g' y) x t_x 
                                        (unbindT y t') (mk_p_yg'g_t' y) (mk_p_yg'xg_t' y)
      (WFExis _ _ _ _ _ _base nms' mk_p_yg'xg_t') = p_g'xg_t
      nms''         = x:(unionEnv (union nms nms') (concatE g g'))
  (WFKind _g'g _t p_g'g_t_base)      -> p_g'g_t_base
lem_strengthen_wftype_base g g'  x t_x (TPoly k t') p_g'g_t p_g'xg_t
  = impossible ("by lemma" ? lem_wf_tpoly_star (concatE (Cons x t_x g) g') k t' p_g'xg_t)

{-@ lem_strengthen_tv_wftype_base :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> { a:Vname | not (in_env a g) && not (in_env a g') } 
        -> k_a:Kind -> t:Type -> { p_g'g_t:WFType | propOf p_g'g_t == WFType (concatE g g') t Star }
        -> ProofOf(WFType (concatE (ConsT a k_a g) g') t Base) 
        -> { pf:WFType | propOf pf == WFType (concatE g g') t Base } / [tsize t, envsize g'] @-}
lem_strengthen_tv_wftype_base :: Env -> Env -> Vname -> Kind -> Type -> WFType -> WFType -> WFType
lem_strengthen_tv_wftype_base g g'  a k_a t@(TRefn b ps) p_g'g_t p_g'ag_t = case p_g'ag_t of
    (WFBase env _b)                                -> WFBase (concatE g g') b
    (WFRefn env _b p_env_b_b _ps nms mk_p_yenv_ps) -> case p_g'g_t of
        (WFKind _g'g _t p_g'g_t_b) -> p_g'g_t_b
    (WFVar1 env' a' _base)                        -> case g' of
        Empty {- a <> a'-} -> impossible ("by" ? lem_free_bound_in_env g (TRefn (FTV a') PEmpty) 
                                                                       Star p_g'g_t a')
        (Cons  _w  _  g'') -> impossible ""
        (ConsT _a' _b g'') -> WFVar1 (concatE g g'') a' Base 
    (WFVar2 env' a' _base p_env'_t_b y t_y)         -> case g' of
        Empty {-a <> y -} -> impossible ""
        (Cons _y _ty g'') -> case p_g'g_t of
            (WFVar2 _g''g _a' _star p_g''g_t_st _ _) 
                -> WFVar2 (concatE g g'') a' Base p_g''g_t_b y t_y
                     where
                       p_g''g_t_b = lem_strengthen_tv_wftype_base g g'' a k_a t p_g''g_t_st p_env'_t_b
            (WFKind _g'g _t p_g'g_t_b)              -> p_g'g_t_b
        (ConsT _a' _ g'') -> impossible ""
    (WFVar3 env' a' _base p_env'_t_b a1 k1)         -> case g' of 
        Empty {- a' == a1 -} -> p_env'_t_b
        (Cons   _y _ty g'')  -> impossible ""
        (ConsT _a1 _k1 g'')  -> case p_g'g_t of
           (WFVar3 _g''g _a' _star p_g''g_t_st _ _) 
               -> WFVar3 (concatE g g'') a' Base p_g''g_t_b a1 k1
                    where
                      p_g''g_t_b = lem_strengthen_tv_wftype_base g g'' a k_a t p_g''g_t_st p_env'_t_b
           (WFKind _g'g _t p_g'g_t_b)              -> p_g'g_t_b
lem_strengthen_tv_wftype_base g g'  a k_a (TFunc t_z t') p_g'g_t p_g'ag_t
  = impossible ("by lemma" ? lem_wf_tfunc_star (concatE (ConsT a k_a g) g') t_z t' p_g'ag_t)
lem_strengthen_tv_wftype_base g g'  a k_a (TExists t_z t') p_g'g_t p_g'ag_t = case p_g'g_t of
  (WFExis _g'g _tz k_z p_g'g_tz _t' _st nms mk_p_yg'g_t') 
        -> WFExis (concatE g g') t_z k_z p_g'g_tz t' Base nms'' mk_p_yg'g_t'_b
    where
      {-@ mk_p_yg'g_t'_b :: { y:Vname | NotElem y nms'' }
            -> ProofOf(WFType (Cons y t_z (concatE g g')) (unbindT y t') Base) @-}
      mk_p_yg'g_t'_b y = lem_strengthen_tv_wftype_base g (Cons y t_z g' ? lem_in_env_concat g g' y) 
                                        a k_a (unbindT y t') (mk_p_yg'g_t' y) (mk_p_yg'ag_t' y)
      (WFExis _ _ _ _ _ _base nms' mk_p_yg'ag_t') = p_g'ag_t
      nms''         = a:(unionEnv (union nms nms') (concatE g g'))
  (WFKind _g'g _t p_g'g_t_base)      -> p_g'g_t_base
lem_strengthen_tv_wftype_base g g'  a k_a (TPoly k t') p_g'g_t p_g'ag_t
  = impossible ("by lemma" ? lem_wf_tpoly_star (concatE (ConsT a k_a g) g') k t' p_g'ag_t)
