{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicLemmas where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Semantics
import Typing
import Primitives

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv)

------------------------------------------------------------------------------
----- | METATHEORY Development
------------------------------------------------------------------------------

-- -- -- -- -- -- -- -- ---
-- Basic Facts and Lemmas -
-- -- -- -- -- -- -- -- ---

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

-- We can alpha-rename a variable anywhere in the environment and recursively alter the type
--   derivation tree. NB this is the base type judgement so there are no variables in the 
--   types to worry about
{-@ lem_change_var_btyp :: g:BEnv -> { x:Vname | not (in_envB x g) } -> t_x:BType
        -> { g':BEnv | not (in_envB x g') && Set_emp (Set_cap (bindsB g) (bindsB g')) }
        -> e:Expr -> t:BType -> ProofOf(HasBType (concatB (BCons x t_x g) g') e t)
        -> { y:Vname | not (in_envB y g) && not (in_envB y g') }
        -> ProofOf(HasBType (concatB (BCons y t_x g) g') (subFV x (FV y) e) t) @-}
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
                (p_z''_e'_b' `withProof` lem_unbind_and_subFV z z' z''
--                      ((e' `withProof` lem_fv_subset e' e)
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
                (p_z''_e'_t' `withProof` lem_unbind_and_subFV z z' z'' 
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

{-@ lem_change_var_wf :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> ProofOf(WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) (tsubFV x (FV y) t)) @-}
lem_change_var_wf :: Env -> Vname -> Type -> Env -> Type -> WFType -> Vname -> WFType
lem_change_var_wf g x t_x g' t p_t_wf@(WFRefn gg z b p z' p_z'_p_b) y
    = WFRefn (concatE (Cons y t_x g) (esubFV x (FV y) g')) z b (subFV x (FV y) p) 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_btyp (erase_env g) x (erase t_x) 
                  (BCons z'' (BTBase b) (erase_env g')) (unbind z z'' p) (BTBase TBool) 
                  (p_z''_p_b `withProof` lem_unbind_and_subFV z z' z''
                       (p `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                            t p_t_wf z'))
                  y `withProof` lem_commute_subFV_unbind x y z z'' p
                    `withProof` lem_erase_concat (Cons y t_x g) (esubFV x (FV y) g')
                    `withProof` lem_erase_esubFV x (FV y) g')
        where
            z''       = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_p_b = lem_change_var_btyp (erase_env (concatE (Cons x t_x g) g')) 
                                  z' (BTBase b) BEmpty 
                                  (unbind z z' p) (BTBase TBool) p_z'_p_b  
                                  (z'' `withProof` lem_erase_concat (Cons x t_x g) g'
                                       `withProof` lem_erase_concat g g')
lem_change_var_wf g x t_x g' t p_t_wf@(WFFunc gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = WFFunc (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z)
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') 
                 (p_z''_t'_wf `withProof` lem_unbindT_and_tsubFV z z' z'' 
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                 y `withProof` lem_commute_tsubFV_unbindT x y z z'' t')
--             `withProof` lem_esubFV_tsubFV x (FV y) z'' t_z g'
        where
            z''         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') p_z'_t'_wf --z''
                                    (z'' `withProof` lem_in_env_concat g g' z''
                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')
lem_change_var_wf g x t_x g' t p_t_wf@(WFExis gg z t_z p_tz_wf t' z' p_z'_t'_wf) y
    = WFExis (concatE (Cons y t_x g) (esubFV x (FV y) g')) z (tsubFV x (FV y) t_z)
             (lem_change_var_wf g x t_x g' t_z p_tz_wf y) (tsubFV x (FV y) t') 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             ((lem_change_var_wf g x t_x (Cons z'' t_z g') (unbindT z z'' t') 
                  (p_z''_t'_wf `withProof` lem_unbindT_and_tsubFV z z' z'' 
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                  y `withProof` lem_commute_tsubFV_unbindT x y z z'' t') -- this the key
             )--     `withProof` lem_esubFV_tsubFV x (FV y) z'' t_z g')
        where
            z''         = fresh_var_excluding (concatE (Cons x t_x g) g') y
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') p_z'_t'_wf 
                                    (z'' `withProof` lem_in_env_concat g g' z''
                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')

--                   e' (t' `withProof` lem_bound_concatB g g' y t_y) p_e'_t' x t_x) 
{-@ lem_weaken_btyp :: g:BEnv -> { g':BEnv | Set_emp (Set_cap (bindsB g) (bindsB g')) }
                -> e:Expr -> bt:BType -> ProofOf(HasBType (concatB g g') e bt) 
                -> { x:Vname | (not (in_envB x g)) && (not (in_envB x g')) }
                -> t_x:BType -> ProofOf(HasBType (concatB (BCons x t_x g) g') e bt) @-}
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
                       (p_y''_e'_t' `withProof` lem_unbind_and_subFV y y' y'' e')
--                       (e' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'))
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
                       (p_y''_e'_t' `withProof` lem_unbind_and_subFV y y' y'' e')
--                        (e' `withProof` lem_fv_bound_in_benv (concatB g g') e t p_e_t y'))
                       x t_x)
        where
            y''         = fresh_varB (concatB (BCons x t_x g) g')
            p_y''_e'_t' = lem_change_var_btyp (concatB g g') y' t_y BEmpty (unbind y y' e') 
                              t' p_y'_e'_t' (y'' `withProof` lem_in_env_concatB g g' y''
                                        `withProof` lem_in_env_concatB (BCons x t_x g) g' y'')
--               (y `withProof` lem_binds_bv_distinctB (concatB g g') e t p_e_t)
lem_weaken_btyp g g' e bt (BTAnn _g e' _bt lt p_e'_bt) x t_x
    = BTAnn (concatB (BCons x t_x g) g') e' bt 
            (lt `withProof` lem_binds_cons_concatB g g' x t_x)
            (lem_weaken_btyp g g' e' bt p_e'_bt x t_x)

-- -- -- -- -- -- -- -- -- -- -- -- -- ---
-- Consequences of the Typing Judgments --
-- -- -- -- -- -- -- -- -- -- -- -- -- ---

{-@ lem_weaken_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> t:Type -> ProofOf(WFType (concatE g g') t)
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } 
            -> t_x:Type -> ProofOf(WFType g t_x)
            -> ProofOf(WFType (concatE (Cons x t_x g) g') t) @-}
lem_weaken_wf :: Env -> Env -> Type -> WFType -> Vname -> Type -> WFType -> WFType
lem_weaken_wf g g' t p_t_wf@(WFRefn _g y b p y' pf_p_bl) x t_x p_tx
    = WFRefn (concatE (Cons x t_x g) g') y b p
                           (y'' `withProof` lem_in_env_concat g g' y''
                                `withProof` lem_in_env_concat (Cons x t_x g) g' y''
                                `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'') 
          (lem_weaken_btyp (erase_env g) (BCons y'' (BTBase b) (erase_env g')) 
               (unbind y y'' p) (BTBase TBool) 
               (pf_y''_p_bl `withProof` lem_unbind_and_subFV y y' y'' p) 
                           x (erase t_x))
        where
          y''         = fresh_var (concatE (Cons x t_x g) g')
          pf_y''_p_bl = lem_change_var_btyp (erase_env (concatE g g')) y' (BTBase b) BEmpty
                             (unbind y y' p) (BTBase TBool) pf_p_bl
                             (y'' `withProof` lem_erase_concat (Cons x t_x g) g'
                                  `withProof` lem_erase_concat g g')
lem_weaken_wf g g' t p_t_wf@(WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x p_tx
    = WFFunc (concatE (Cons x t_x g) g') y
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x p_tx)
             t' (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t') 
                         (p_y''_t'_wf `withProof` lem_unbindT_and_tsubFV y y' y'' t')
                         x t_x p_tx)
        where
          y''         = fresh_var(concatE (Cons x t_x g) g')
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty
                             (unbindT y y' t') p_y'_t'_wf
                             (y'' `withProof` lem_in_env_concat g g' y''
                                  `withProof` lem_in_env_concat (Cons x t_x g) g' y'')
lem_weaken_wf g g' t p_t_wf@(WFExis gg y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x p_tx
    = WFExis (concatE (Cons x t_x g) g') y 
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x p_tx)
             t' (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t')
                         (p_y''_t'_wf `withProof` lem_unbindT_and_tsubFV y y' y''  t')
                         x t_x p_tx)
        where
          y''         = fresh_var (concatE (Cons x t_x g) g')
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty 
                             (unbindT y y' t') p_y'_t'_wf 
                             (y'' `withProof` lem_in_env_concat g g' y''
                                  `withProof` lem_in_env_concat (Cons x t_x g) g' y'')


{-@ assume lem_weaken_typ :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
                             -> e:Expr -> t:Type -> ProofOf(HasType (concatE g g') e t)
                             -> { x:Vname | (not (in_env x g)) && (not (in_env x g')) }
                             -> t_x:Type -> ProofOf(HasType (concatE (Cons x t_x g) g') e t) @-}
lem_weaken_typ :: Env -> Env -> Expr -> Type -> HasType -> Vname -> Type -> HasType          
lem_weaken_typ g g' e t p_e_t x t_x = undefined


{-@ lem_typing_wf :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                      -> ProofOf(WFEnv g) -> ProofOf(WFType g t) @-} 
lem_typing_wf :: Env -> Expr -> Type -> HasType -> WFEnv -> WFType
--lem_typing_wf g e t (TBC _g b) p_wf_g  = lem_wf_tybc g b
--lem_typing_wf g e t (TIC _g n) p_wf_g  = lem_wf_tyic g n
lem_typing_wf g e t (TVar1 _g' x _t) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                     -> impossible "surely"
        (WFEBind g' p_g' _x _t p_g'_t) -> lem_weaken_wf g' Empty t p_g'_t x t p_g'_t
lem_typing_wf g e t (TVar2 g' x _t p_g'_x_t y s) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                     -> impossible "Surely"
        (WFEBind g' p_g' _y _s p_g'_s) -> lem_weaken_wf g' Empty t 
                                              (lem_typing_wf g' e t p_g'_x_t p_g')
                                              y s p_g'_s
--TODO: refactor lem_wf_ty: adds five minutes to typechecking
--lem_typing_wf g e t (TPrm _g c) p_wf_g = lem_wf_ty g c
lem_typing_wf g e t (TAbs _g x t_x p_tx_wf e' t' y p_e'_t') p_wf_g
    = WFFunc g x t_x p_tx_wf t' y (lem_typing_wf (Cons y t_x g) (unbind x y e') 
                                               (unbindT x y t') p_e'_t'
                                               (WFEBind g p_wf_g y t_x p_tx_wf))
lem_typing_wf g e t (TApp _g e1 x t_x t' p_e1_txt' e2 p_e2_tx) p_wf_g
    = case (lem_typing_wf g e1 (TFunc x t_x t') p_e1_txt' p_wf_g) of
        (WFFunc _ _ _ p_g_tx _ y p_gx_t') -> WFExis g x t_x 
                                                    (lem_typing_wf g e2 t_x p_e2_tx p_wf_g)
                                                    t' y p_gx_t'
        (_)                               -> impossible "clearly"
lem_typing_wf g e t (TLet _g e_x t_x p_ex_tx x e' _t p_g_t y p_e'_t) p_wf_g = p_g_t 
lem_typing_wf g e t (TAnn _g e' _t p_e'_t) p_wf_g
    = lem_typing_wf g e' t p_e'_t p_wf_g
lem_typing_wf g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_wf_g = p_g_t


-- Lemma. If G |- e : t, then Set_emp (freeBV e)
{-@ lem_freeBV_unbind_empty :: x:Vname -> y:Vname -> { e:Expr | Set_emp (freeBV (unbind x y e)) }
	-> { pf:_ | Set_emp (freeBV e) || freeBV e == Set_sng x } @-}
lem_freeBV_unbind_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBV_unbind_empty x y e = toProof ( S.empty === freeBV (unbind x y e)
                                      === S.difference (freeBV e) (S.singleton x) )

{-@ lem_tfreeBV_unbindT_empty :: x:Vname -> y:Vname -> { t:Type | Set_emp (tfreeBV (unbindT x y t)) }
        -> { pf:_ | Set_emp (tfreeBV t) || tfreeBV t == Set_sng x } @-}
lem_tfreeBV_unbindT_empty :: Vname -> Vname -> Type -> Proof
lem_tfreeBV_unbindT_empty x y t = toProof ( S.empty === tfreeBV (unbindT x y t)
                                        === S.difference (tfreeBV t) (S.singleton x) )

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

-- Lemma. If G |- e : t, then Set_emp (freeBV e)
{-@ lem_freeBV_empty :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t) -> ProofOf(WFEnv g)
                              -> { pf:_ | Set_emp (freeBV e) && Set_emp (tfreeBV t) } @-}
lem_freeBV_empty :: Env -> Expr -> Type -> HasType -> WFEnv -> Proof
lem_freeBV_empty g e t (TBC _g b) p_g_wf   = ()
lem_freeBV_empty g e t (TIC _g n) p_g_wf   = ()
lem_freeBV_empty g e t (TVar1 _ x _) p_g_wf 
    = case (p_g_wf) of
        (WFEEmpty)                        -> impossible ""
        (WFEBind g' p_g'_wf _x _t p_g'_t) -> lem_tfreeBV_empty g' t p_g'_t p_g'_wf
lem_freeBV_empty g e t (TVar2 g' x _ p_x_t y s) p_g_wf
    = case (p_g_wf) of
        (WFEEmpty)                        -> impossible ""
        (WFEBind _g' p_g'_wf _ _s p_g'_s) -> lem_freeBV_empty g' e t p_x_t p_g'_wf
lem_freeBV_empty g e t (TPrm _g c) p_g_wf  = () ? lem_freeBV_prim_empty c
lem_freeBV_empty g e t (TAbs _g x t_x p_g_tx e' t' y p_yg_e'_t') p_g_wf
    = () ? lem_tfreeBV_empty g t_x p_g_tx p_g_wf
         ? lem_freeBV_unbind_empty x y (e' ? pf_unbinds_empty)
         ? lem_tfreeBV_unbindT_empty x y (t' ? pf_unbinds_empty)
        where
          p_yg_wf = WFEBind g p_g_wf y t_x p_g_tx
          {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind x y e')) 
                                        && Set_emp (tfreeBV (unbindT x y t')) } @-}
          pf_unbinds_empty = lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t') 
                                              p_yg_e'_t' p_yg_wf
lem_freeBV_empty g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf
    = () ? lem_freeBV_empty g e' (TFunc x t_x t') p_e'_txt' p_g_wf
         ? lem_freeBV_empty g e_x t_x p_ex_tx p_g_wf
lem_freeBV_empty g e t (TLet _g e_x t_x p_ex_tx x e' _t p_g_t y p_yg_e'_t) p_g_wf
    = () ? lem_freeBV_empty g e_x t_x p_ex_tx p_g_wf
         ? lem_freeBV_unbind_empty x y  (e' ? lem_freeBV_empty (Cons y t_x g) (unbind x y e')
                                                               (unbindT x y t) p_yg_e'_t p_yg_wf)
         ? lem_tfreeBV_empty g t p_g_t p_g_wf
        where
          p_g_tx = lem_typing_wf g e_x t_x p_ex_tx p_g_wf
          p_yg_wf = WFEBind g p_g_wf y t_x p_g_tx
lem_freeBV_empty g e t (TAnn _g e' _ p_e'_t) p_g_wf 
    = () ? lem_freeBV_empty g e' t p_e'_t p_g_wf
lem_freeBV_empty g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_g_wf
    = () ? lem_freeBV_empty g e s p_e_s p_g_wf
         ? lem_tfreeBV_empty g t p_g_t p_g_wf

{-@ lem_tfreeBV_empty :: g:Env -> t:Type -> ProofOf(WFType g t) -> ProofOf(WFEnv g)
                               -> { pf:Proof | Set_emp (tfreeBV t) } @-}
lem_tfreeBV_empty :: Env -> Type -> WFType -> WFEnv -> Proof
lem_tfreeBV_empty g t (WFRefn _g x b p y p_yg_p_bl) p_g_wf
    = () ? lem_freeBV_unbind_empty x y (p ? lem_freeBV_emptyB (BCons y (BTBase b) (erase_env g))
                                                              (unbind x y p) (BTBase TBool) p_yg_p_bl) 
lem_tfreeBV_empty g t (WFFunc _g x t_x p_g_tx t' y p_yg_t') p_g_wf
    = () ? lem_tfreeBV_empty g t_x p_g_tx p_g_wf
         ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t')
                                                                 p_yg_t' p_yg_wf)
        where
          p_yg_wf = WFEBind g p_g_wf y t_x p_g_tx
lem_tfreeBV_empty g t (WFExis _g x t_x p_g_tx t' y p_yg_t') p_g_wf
    = () ? lem_tfreeBV_empty g t_x p_g_tx p_g_wf
         ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t')
                                                                 p_yg_t' p_yg_wf)
        where
          p_yg_wf = WFEBind g p_g_wf y t_x p_g_tx

