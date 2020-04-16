{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module STLCLemmas where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Environments
import Semantics
import BareTyping
import WellFormedness
import Typing

-- force these into scope fpr LH
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv, ValueDenoted)

------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- -- -- -- -- -- 
-- SEMANTICS: Basic Facts and Lemmas - -- used in the later metatheory too
-- -- -- -- -- -- -- -- -- -- -- -- --

-- Determinism of the Operational Semantics
{-@ lem_value_stuck :: e:Expr -> e':Expr -> ProofOf(Step e e') 
                   -> { proof:_ | not (isValue e) } @-}
lem_value_stuck :: Expr -> Expr -> Step -> Proof
lem_value_stuck e  e' (EPrim _ _)      
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EApp1 _ _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EApp2 _ _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAppAbs _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELet _ _ _ _ _) 
    = case e of 
        (Let _ _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELetV _ _ _)    
    = case e of 
        (Let _ _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnn _ _ _ _)   
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnnV _ _)      
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""

{-@ lem_value_refl :: { v:Expr | isValue v } -> v':Expr -> ProofOf(EvalsTo v v')
                -> { pf:_ | v == v' } @-}
lem_value_refl :: Expr -> Expr -> EvalsTo -> Proof
lem_value_refl v v' (Refl _v) = ()
lem_value_refl v v' (AddStep _v v1 st_v_v1 _v' ev_v1_v') 
    = impossible ("stuck" ? lem_value_stuck v v1 st_v_v1)

{-@ lem_sem_det :: e:Expr -> e1:Expr -> ProofOf(Step e e1)
                   -> e2:Expr -> ProofOf(Step e e2) -> { x:_ | e1 == e2 } @-}
lem_sem_det :: Expr -> Expr -> Step -> Expr -> Step -> Proof
lem_sem_det e e1 p1@(EPrim _ _) e2 p2  -- e = App (Prim c) w
    = case p2 of    
        (EPrim _ _)            -> ()            
        (EApp1 f f' p_f_f' f1) -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EApp2 f f' p_f_f' v)  -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppAbs {})           -> impossible "OK"
        (_)                    -> impossible ""
lem_sem_det e e' (EApp1 e1 e1' p_e1e1' e2) e'' pf_e_e''
    = case pf_e_e'' of
        (EPrim _ _)                 -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EApp1 _e1 e1'' p_e1e1'' _) -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''  
        (EApp2 g g' p_g_g' v)       -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EAppAbs {})                -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                         -> impossible "" 
    -- e = e1 e2, e' = e1' e2, e'' = e1'' e2
lem_sem_det e e' (EApp2 e1 e1' p_e1e1' v1) e'' pf_e_e''
    = case pf_e_e'' of
        (EPrim _ _)                 -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EApp1 _v1 v1' p_v1v1' _)   -> impossible ("by lem" ? lem_value_stuck _v1 v1' p_v1v1')
        (EApp2 _ e1'' p_e1e1'' _)   -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''
        (EAppAbs {})                -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                         -> impossible ""
    -- e = v1 e1, e' = v1 e1', e'' = v1 e1''
lem_sem_det e e1 (EAppAbs x e' v) e2 pf_e_e2
    = case pf_e_e2 of 
        (EPrim {})                  -> impossible ""
        (EApp1 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EApp2 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppAbs _x _e' _v)         -> ()
        (_)                         -> impossible ""
lem_sem_det e e1 (ELet e_x e_x' p_ex_ex' x e1') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet _ e_x'' p_ex_ex'' _x _) -> () ? lem_sem_det e_x e_x' p_ex_ex' e_x'' p_ex_ex''
        (ELetV _ _ _)                 -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (_)                           -> impossible ""
lem_sem_det e e1 (ELetV x v e') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet e_x e_x' p_ex_ex' _x _) -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (ELetV _ _ _)                 -> ()
        (_)                           -> impossible ""
lem_sem_det e e1 (EAnn e' e1' p_e_e1' t) e2 pf_e_e2
    = case pf_e_e2 of
        (EAnn _e' e2' p_e_e2' _t) -> () ? lem_sem_det e' e1' p_e_e1' e2' p_e_e2'
        (EAnnV {})                -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (_)                       -> impossible ""
lem_sem_det e e1 (EAnnV v t) e2 pf_e_e2
    = case pf_e_e2 of 
        (EAnn e' e1' p_e_e1' t)   -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (EAnnV _v _t)             -> ()
        (_)                       -> impossible "" 

-- -- -- -- -- -- -- --
-- TECHNICAL LEMMAS ---
-- -- -- -- -- -- -- -- 

-- Lemma. If G |- e : t, then Set_emp (freeBV e)
{-@ lem_freeBV_unbind_empty :: x:Vname -> y:Vname -> { e:Expr | Set_emp (freeBV (unbind x y e)) }
	-> { pf:_ | Set_emp (freeBV e) || freeBV e == Set_sng x } @-}
lem_freeBV_unbind_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBV_unbind_empty x y e = toProof ( S.empty === freeBV (unbind x y e)
                                      === S.difference (freeBV e) (S.singleton x) )

{-@ lem_freeBV_emptyB :: g:BEnv -> e:Expr -> t:BType -> ProofOf(HasBType g e t)
                              -> { pf:_ | Set_emp (freeBV e) } @-}
lem_freeBV_emptyB :: BEnv -> Expr ->  BType -> HasBType -> Proof 
lem_freeBV_emptyB g e t (BTBC _g b)    = ()
lem_freeBV_emptyB g e t (BTIC _g n)    = ()
lem_freeBV_emptyB g e t (BTVar1 _ x _) = ()
lem_freeBV_emptyB g e t (BTVar2 g' x _ p_x_t y s)
    = () ? lem_freeBV_emptyB g' e t p_x_t
lem_freeBV_emptyB g e t (BTPrm _g c)   = ()
lem_freeBV_emptyB g e t (BTAbs _g x t_x e' t' y p_yg_e'_t')
    = () ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (BCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
lem_freeBV_emptyB g e t (BTApp _g e' t_x t' p_e'_txt' e_x p_ex_tx)
    = () ? lem_freeBV_emptyB g e' (BTFunc t_x t') p_e'_txt'
         ? lem_freeBV_emptyB g e_x t_x p_ex_tx
lem_freeBV_emptyB g e t (BTLet _g e_x t_x p_ex_tx x e' t' y p_yg_e'_t')
    = () ? lem_freeBV_emptyB g e_x t_x p_ex_tx
         ? lem_freeBV_unbind_empty x y (e' ? lem_freeBV_emptyB (BCons y t_x g) (unbind x y e')
                                                               t' p_yg_e'_t')
lem_freeBV_emptyB g e t (BTAnn _g e' _t t1 p_e'_t) 
    = () ? lem_freeBV_emptyB g e' t p_e'_t


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -
-- Consequences of the Bare Typing Judgments -
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -


-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. NB this is the base type judgement so there are no variables in the 
--   types to worry about
{-@ lem_change_var_btyp :: g:BEnv -> { x:Vname | not (in_envB x g) } -> t_x:BType
        -> { g':BEnv | not (in_envB x g') && Set_emp (Set_cap (bindsB g) (bindsB g')) }
        -> e:Expr -> t:BType 
        -> { p_e_t:HasBType | propOf p_e_t == HasBType (concatB (BCons x t_x g) g') e t }
        -> { y:Vname | not (in_envB y g) && not (in_envB y g') }
        -> { pf:HasBType | propOf pf == (HasBType (concatB (BCons y t_x g) g') (subFV x (FV y) e) t) 
                           && btypSize pf == btypSize p_e_t } / [btypSize p_e_t] @-}
lem_change_var_btyp :: BEnv -> Vname -> BType -> BEnv -> Expr -> BType 
                -> HasBType ->  Vname -> HasBType
lem_change_var_btyp g x t_x g' e t (BTBC _ b) y
    = BTBC (concatB (BCons y t_x g) g') b
lem_change_var_btyp g x t_x g' e t (BTIC _ n) y
    = BTIC (concatB (BCons y t_x g) g') n 
lem_change_var_btyp g x t_x g' e t p_z_t@(BTVar1 _ z _t) y
    = case g' of 
        (BEmpty)           -> BTVar1 g y t_x 
        (BCons _z _ g'')   -> BTVar1 (concatB (BCons y t_x g) g'') z t
lem_change_var_btyp g x t_x g' e t (BTVar2 _ z _t p_z_t w t_w) y
    = case g' of             -- g''=Emp so x=w and p_z_t :: HasBType(g (FV z) t)
        (BEmpty)           -> case (x == z) of
                                (True)  -> impossible "it is"
                                (False) -> BTVar2 g z t p_z_t y t_x 
        (BCons _w _tw g'') -> case (x == z) of
                    (True)  -> BTVar2 (concatB (BCons y t_x g) g'') 
                                 (y `withProof` lem_in_env_concatB (BCons y t_x g) g'' y)
                                 t (lem_change_var_btyp g x t_x g'' (FV z) t p_z_t y) w t_w
                    (False) -> BTVar2 (concatB (BCons y t_x g) g'')
                                 (z `withProof` lem_in_env_concatB (BCons y t_x g) g'' z
                                    `withProof` lem_in_env_concatB (BCons x t_x g) g'' z)
                                 t (lem_change_var_btyp g x t_x g'' (FV z) t p_z_t y) w t_w
lem_change_var_btyp g x t_x g' e t (BTPrm _ c) y
    = BTPrm (concatB (BCons y t_x g) g') c
lem_change_var_btyp g x t_x g' e t p_e_t@(BTAbs gg z b e' b' z' p_z'_e'_b') y
    = BTAbs (concatB (BCons y t_x g) g') z b (subFV x (FV y) e') b' 
            (z'' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g') e t p_e_t z'')
            (lem_change_var_btyp g x t_x (BCons z'' b g') (unbind z z'' e') b' 
                (p_z''_e'_b' `withProof` lem_subFV_unbind z z' (FV z'')
                        (e' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g')
                                                          e t p_e_t z'))
                y `withProof` lem_commute_subFV_unbind x y z z'' e')
        where
            z''         = fresh_var_excludingB (concatB (BCons x t_x g) g') y
            p_z''_e'_b' = lem_change_var_btyp  (concatB (BCons x t_x g) g') z' b BEmpty 
                                    (unbind z z' e') b' p_z'_e'_b' 
                                    (z'' `withProof` lem_in_env_concatB g g' z''
                                         `withProof` lem_in_env_concatB (BCons x t_x g) g' z'')
lem_change_var_btyp g x t_x g' e t (BTApp _ e1 t1 t2 p_e1_t1t2 e2 p_e2_t1) y
    = BTApp (concatB (BCons y t_x g) g') (subFV x (FV y) e1) t1 t2 
            (lem_change_var_btyp g x t_x g' e1 (BTFunc t1 t2) p_e1_t1t2 y)
            (subFV x (FV y) e2) (lem_change_var_btyp g x t_x g' e2 t1 p_e2_t1 y)
lem_change_var_btyp g x t_x g' e t p_e_t@(BTLet gg e_z t_z p_ez_tz z e' t' z' p_z'_e'_t') y
    = BTLet (concatB (BCons y t_x g) g') (subFV x (FV y) e_z) t_z
            (lem_change_var_btyp g x t_x g' e_z t_z p_ez_tz y) z (subFV x (FV y) e') t' 
            (z'' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g') e t p_e_t z'')
            (lem_change_var_btyp g x t_x (BCons z'' t_z g') (unbind z z'' e') t' 
                (p_z''_e'_t' `withProof` lem_subFV_unbind z z' (FV z'')
                        (e' `withProof` lem_fv_bound_in_benv (concatB (BCons x t_x g) g')
                                                          e t p_e_t z'))
                y `withProof` lem_commute_subFV_unbind x y z z'' e')
        where
            z''         = fresh_var_excludingB (concatB (BCons x t_x g) g') y
            p_z''_e'_t' = lem_change_var_btyp  (concatB (BCons x t_x g) g') z' t_z BEmpty 
                                    (unbind z z' e') t' p_z'_e'_t' 
                                    (z'' `withProof` lem_in_env_concatB g g' z''
                                         `withProof` lem_in_env_concatB (BCons x t_x g) g' z'')
lem_change_var_btyp g x t_x g' e t (BTAnn _ e' _t t' p_e'_t) y
    = BTAnn (concatB (BCons y t_x g) g') (subFV x (FV y) e') t 
            (tsubFV x (FV y) t' `withProof` lem_erase_tsubFV x (FV y) t'
                                `withProof` lem_binds_cons_concatB g g' x t_x)
            (lem_change_var_btyp g x t_x g' e' t p_e'_t y)


{-@ lem_weaken_btyp :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) }
        -> e:Expr -> bt:BType -> { p_e_bt:HasBType | propOf p_e_bt == HasBType (concatB g g') e bt }
        -> { x:Vname | (not (in_envB x g)) && (not (in_envB x g')) }
        -> t_x:BType -> ProofOf(HasBType (concatB (BCons x t_x g) g') e bt) / [btypSize p_e_bt] @-}
lem_weaken_btyp :: BEnv -> BEnv -> Expr -> BType -> HasBType -> Vname -> BType -> HasBType
lem_weaken_btyp g g' e t (BTBC _g b)      x t_x = BTBC  (concatB (BCons x t_x g) g') b
lem_weaken_btyp g g' e t (BTIC _g n)      x t_x = BTIC  (concatB (BCons x t_x g) g') n
lem_weaken_btyp g g' e t p_y_ty@(BTVar1 gg y t_y) x t_x 
    = case g' of 
        (BEmpty)           -> BTVar2 (BCons y t_y gg) y t_y p_y_ty x t_x
        (BCons _y _ty g'') -> BTVar1 (concatB (BCons x t_x g) g'') y t_y 
                                    -- (g; g' == _g, z:t_z) |- y : t_y
lem_weaken_btyp g g' e t p_y_ty@(BTVar2 gg y t_y p_gg'_y_ty z t_z) x t_x
    = case g' of
        (BEmpty)           -> BTVar2 (BCons z t_z gg) y t_y p_y_ty x t_x
        (BCons _z _tz g'') -> BTVar2 (concatB (BCons x t_x g) g'') 
                                  (y `withProof` lem_in_env_concatB g g'' y
                                     `withProof` lem_in_env_concatB (BCons x t_x g) g'' y) t_y
                                     (lem_weaken_btyp g g'' e t p_gg'_y_ty x t_x)
                                     z t_z
lem_weaken_btyp g g' e t (BTPrm _g c)     x t_x = BTPrm (concatB (BCons x t_x g) g') c
lem_weaken_btyp g g' e t p_e_t@(BTAbs gg y t_y e' t' y' p_y'_e'_t') x t_x
    = BTAbs (concatB (BCons x t_x g) g') y t_y e' t' 
               (y'' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'')
               (lem_weaken_btyp g (BCons y'' t_y g') (unbind y y'' e') t' 
                       (p_y''_e'_t' `withProof` lem_subFV_unbind y y' (FV y'') e')
                       x t_x) 
        where
            y''         = fresh_varB (concatB (BCons x t_x g) g')
            p_y''_e'_t' = lem_change_var_btyp (concatB g g') y' t_y BEmpty (unbind y y' e') 
                                   t' p_y'_e'_t' 
                                   (y'' `withProof` lem_in_env_concatB g g' y''
                                        `withProof` lem_in_env_concatB (BCons x t_x g) g' y'')
lem_weaken_btyp g g' e t (BTApp _g e1 s s' p_e1_ss' e2 p_e2_s) x t_x 
    = BTApp (concatB (BCons x t_x g) g') e1 s s' 
               (lem_weaken_btyp g g' e1 (BTFunc s s') p_e1_ss' x t_x)
                e2 (lem_weaken_btyp g g' e2 s p_e2_s x t_x)
lem_weaken_btyp g g' e t p_e_t@(BTLet gg e_y t_y p_ey_ty y e' t' y' p_y'_e'_t') x t_x
    = BTLet (concatB (BCons x t_x g) g') e_y t_y 
               (lem_weaken_btyp g g' e_y t_y p_ey_ty x t_x) y e' t' 
               (y'' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'')
               (lem_weaken_btyp g (BCons y'' t_y g') (unbind y y'' e') t' 
                       (p_y''_e'_t' `withProof` lem_subFV_unbind y y' (FV y'') e')
                       x t_x)
        where
            y''         = fresh_varB (concatB (BCons x t_x g) g')
            p_y''_e'_t' = lem_change_var_btyp (concatB g g') y' t_y BEmpty (unbind y y' e') 
                              t' p_y'_e'_t' (y'' `withProof` lem_in_env_concatB g g' y''
                                        `withProof` lem_in_env_concatB (BCons x t_x g) g' y'')
lem_weaken_btyp g g' e bt (BTAnn _g e' _bt lt p_e'_bt) x t_x
    = BTAnn (concatB (BCons x t_x g) g') e' bt 
            (lt `withProof` lem_binds_cons_concatB g g' x t_x)
            (lem_weaken_btyp g g' e' bt p_e'_bt x t_x)


-- -- -- -- -- -- -- -- ---
-- THE SUBSTITUTION LEMMA -
-- -- -- -- -- -- -- -- ---

{-@ lem_subst_btyp :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) }
        -> { x:Vname | (not (in_envB x g)) && not (in_envB x g') } -> v_x:Value
        -> t_x:BType -> ProofOf(HasBType g v_x t_x) -> e:Expr -> t:BType
        -> ProofOf(HasBType (concatB (BCons x t_x g) g') e t)
        -> ProofOf(HasBType (concatB g g') (subFV x v_x e) t) @-}
lem_subst_btyp :: BEnv -> BEnv -> Vname -> Expr -> BType -> HasBType 
        -> Expr -> BType -> HasBType -> HasBType
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTBC _env b) = BTBC (concatB g g') b
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTIC _env n) = BTIC (concatB g g') n
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTVar1 _env z _t)
  = case g' of
      (BEmpty)         -> p_vx_tx   
      (BCons _z _ g'') -> BTVar1 (concatB g g'') (z ? lem_in_env_concatB (BCons x t_x g) g'' z
                                                    ? lem_in_env_concatB g g'' z) t
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTVar2 _env z _t p_z_t w t_w)
  = case g' of
      (BEmpty)           -> case ( x == z ) of
                    (True)  -> impossible "it is"
                    (False) -> p_z_t -- ? toProof ( e === (FV z) )
      (BCons _w _tw g'') -> case ( x == z ) of
                    (True)  -> lem_weaken_btyp (concatB g g'') BEmpty v_x t p_gg''_vx_tx w t_w 
                                               ? toProof ( e === FV x )
                                 where
                                   p_gg''_vx_tx = lem_subst_btyp g g'' x v_x t_x p_vx_tx e t p_z_t
                    (False) -> BTVar2 (concatB g g'') (z ? lem_in_env_concatB (BCons x t_x g) g'' z
                                                        ? lem_in_env_concatB g g'' z)
                                      t p_z_tvx (w ? lem_fv_bound_in_benv g v_x t_x p_vx_tx w
                                                   ? lem_in_env_concatB (BCons x t_x g) g'' w   
                                                   ? lem_in_env_concatB g g'' w) t_w
                                 where
                                   p_z_tvx = lem_subst_btyp g g'' x v_x t_x p_vx_tx e t p_z_t
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTPrm _env c) = BTPrm (concatB g g') c
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTAbs env_ z t_z e' t' y_ p_yenv_e'_t')
  = BTAbs (concatB g g') z t_z (subFV x v_x e') t' y p_yg'g_e'vx_t'
      where
        y              = y_ ? lem_in_env_concatB g g' y_
                            ? lem_in_env_concatB (BCons x t_x g) g' y_
                            ? lem_fv_bound_in_benv g v_x t_x p_vx_tx y_
        p_yg'g_e'vx_t' = lem_subst_btyp g (BCons y t_z g') x v_x t_x p_vx_tx (unbind z y e')
                                        t' p_yenv_e'_t' ? lem_commute_subFV_subBV1 z (FV y) x v_x e'
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTApp env_ e' t_z t' p_env_e'_tzt' e_z p_env_ez_tz)
  = BTApp (concatB g g') (subFV x v_x e') t_z t' p_g'g_e'vx_tzt' (subFV x v_x e_z) p_g'g_ezvx_tz
      where
        p_g'g_e'vx_tzt' = lem_subst_btyp g g' x v_x t_x p_vx_tx e' (BTFunc t_z t') p_env_e'_tzt'
        p_g'g_ezvx_tz   = lem_subst_btyp g g' x v_x t_x p_vx_tx e_z t_z p_env_ez_tz
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTLet env_ e_z t_z p_env_ez_tz z e' t_ y_ p_yenv_e'_t)
  = BTLet (concatB g g') (subFV x v_x e_z) t_z p_g'g_ezvx_tz z (subFV x v_x e') t y p_yg'g_e'vx_t
      where
        y              = y_ ? lem_in_env_concatB g g' y_
                            ? lem_in_env_concatB (BCons x t_x g) g' y_
                            ? lem_fv_bound_in_benv g v_x t_x p_vx_tx y_
        p_g'g_ezvx_tz  = lem_subst_btyp g g' x v_x t_x p_vx_tx e_z t_z p_env_ez_tz
        p_yg'g_e'vx_t  = lem_subst_btyp g (BCons y t_z g') x v_x t_x p_vx_tx (unbind z y e')
                                        t p_yenv_e'_t ? lem_commute_subFV_subBV1 z (FV y) x v_x e'
lem_subst_btyp g g' x v_x t_x p_vx_tx e t (BTAnn env_ e' t_ liqt p_env_e'_t)
  = BTAnn (concatB g g') (subFV x v_x e') t 
          (tsubFV x (v_x ? lem_fv_subset_bindsB g v_x t_x p_vx_tx 
                         ? toProof ( S.isSubsetOf (bindsB g) (bindsB (concatB g g')) === True )
                         ? toProof ( S.isSubsetOf (fv v_x) (bindsB (concatB g g')) === True ) )
                       (liqt ? lem_erase_tsubFV x v_x liqt
                             ? lem_binds_cons_concatB g g' x t_x
                             ? toProof ( S.isSubsetOf (free (tsubFV x v_x liqt)) (S.union (fv v_x) (S.difference (free liqt) (S.singleton x))) === True )
                             ? toProof ( S.difference (bindsB (concatB (BCons x t_x g) g')) (S.singleton x) === (bindsB (concatB g g')) )
                             ? toProof ( S.isSubsetOf (S.difference (free liqt) (S.singleton x)) (bindsB (concatB g g')) === True ) )
                             ? toProof ( S.isSubsetOf (fv v_x) (bindsB (concatB g g')) === True ) 
                             ? lem_union_subset (fv v_x) (S.difference (free liqt) (S.singleton x)) (bindsB (concatB g g'))
                             ? toProof ( S.isSubsetOf (S.union (fv v_x) (S.difference (free liqt) (S.singleton x))) (bindsB (concatB g g')) === True )
                             ? toProof ( bindsB (concatB g g') === S.union (bindsB g) (bindsB g') )
                             ? toProof ( tfreeBV liqt === S.empty ) 
                             ? toProof ( erase (tsubFV x v_x liqt) === t )
                             ? toProof ( tfreeBV (tsubFV x v_x liqt) === S.empty ) ) p_g'g_e'_t
      where
        p_g'g_e'_t = lem_subst_btyp g g' x v_x t_x p_vx_tx e' t p_env_e'_t
