{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-} 
{- @ LIQUID "--no-totality" @-} 
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module TechLemmas where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import BasicProps
import Typing
import Primitives
import Primitives3
import STLCLemmas
import STLCSoundness

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, Subtype, WFType, WFEnv)
denotations = (Entails, Denotes, DenotesEnv)

{-@ reflect foo13 @-}
foo13 x = Just x
foo13 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   Weds AM: 676 lines
------------------------------------------------------------------------------

-- Note: The technical lemmas lem_change_var_btyp, lem_weaken_btyp
--   are found in STLCLemmas.hs

{-@ lem_change_var_ent :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type 
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> { p:Pred | Set_sub (fv p) (binds (concatE (Cons x t_x g) g')) }
      -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE (Cons x t_x g) g') p }
      -> { y:Vname | not (in_env y g) && not (in_env y g') && (x==y || not (Set_mem y (fv p))) }
      -> ProofOf(Entails (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) p)) @-}
lem_change_var_ent :: Env -> Vname -> Type -> Env -> WFEnv -> Pred -> Entails -> Vname -> Entails
lem_change_var_ent g x t_x g' p_env_wf p (EntPred _env _p evals_func) y
    = EntPred (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) p) evals_func'
        where  -- env' = concatE (Cons y t_x g) (esubFV x (FV y) g')   env = concatE (Cons x t_x g) g'
          env'      = concatE (Cons y t_x g) (esubFV x (FV y) g')
          p_env'_wf = lem_change_var_wfenv g x t_x g' p_env_wf y
          env       = concatE (Cons x t_x g) g' ? lem_esubFV_inverse g x t_x g' p_env_wf y
          evals_func' :: CSubst -> DenotesEnv -> EvalsTo
          evals_func' th' den_env'_th' = evals_func th den_env_th 
              ? lem_change_var_back th' y x 
              ? lem_binds_env_th (concatE (Cons y t_x g) (esubFV x (FV y) g')) th' den_env'_th'
              ? lem_change_var_in_csubst th x y (p ? lem_binds_env_th env th den_env_th)
              ? lem_chain_subFV x y (FV x) p 
            where
              th         = change_varCS th' y x  
              den_env_th = lem_change_var_denote_env g y t_x (esubFV x (FV y) g') p_env'_wf th' den_env'_th' (x
                             ? lem_binds_env_th (concatE (Cons y t_x g) (esubFV x (FV y) g')) th' den_env'_th')
                             ? lem_esubFV_inverse  g x t_x g' p_env_wf y

{-@ lem_change_var_wfenv :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> ProofOf(WFEnv (concatE (Cons y t_x g) (esubFV x (FV y) g'))) @-}
lem_change_var_wfenv :: Env -> Vname -> Type -> Env -> WFEnv -> Vname -> WFEnv
lem_change_var_wfenv g x t_x Empty           p_env_wf y = case p_env_wf of
  (WFEBind _g p_g_wf _x _tx p_g_tx)         -> WFEBind g p_g_wf y t_x p_g_tx
lem_change_var_wfenv g x t_x (Cons z t_z g') p_env_wf y = case p_env_wf of
  (WFEBind env' p_env'_wf _z _tz p_env'_tz) -> WFEBind env'' p_env''_wf z (tsubFV x (FV y) t_z) p_env''_tz
    where
      env''      = concatE (Cons y t_x g) (esubFV x (FV y) g')
      p_env''_wf = lem_change_var_wfenv g x t_x g' p_env'_wf y
      p_env''_tz = lem_change_var_wf g x t_x g' t_z p_env'_tz y

--                         (tsubFV x (FV y) t)) && (wftypSize pf == wftypSize p_t_wf) } @-}
{-@ lem_change_var_wf :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE (Cons x t_x g) g') t }
      -> { y:Vname | not (in_env y g) && not (in_env y g') }
      -> { pf:WFType | propOf pf == (WFType (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                (tsubFV x (FV y) t)) && (wftypSize pf == wftypSize p_t_wf) } / [wftypSize p_t_wf ] @-}
lem_change_var_wf :: Env -> Vname -> Type -> Env -> Type -> WFType -> Vname -> WFType
lem_change_var_wf g x t_x g' t p_t_wf@(WFRefn gg z b p z' p_z'_p_b) y
    = WFRefn (concatE (Cons y t_x g) (esubFV x (FV y) g')) z b (subFV x (FV y) p) 
             (z'' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') t p_t_wf z'')
             (lem_change_var_btyp (erase_env g) x (erase t_x) 
                  (BCons z'' (BTBase b) (erase_env g')) (unbind z z'' p) (BTBase TBool) 
                  (p_z''_p_b `withProof` lem_subFV_unbind z z' (FV z'')
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
                 (p_z''_t'_wf `withProof` lem_tsubFV_unbindT z z' (FV z'')
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
                  (p_z''_t'_wf `withProof` lem_tsubFV_unbindT z z' (FV z'') 
                      (t' `withProof` lem_free_bound_in_env (concatE (Cons x t_x g) g') 
                                                        t p_t_wf z'))
                  y `withProof` lem_commute_tsubFV_unbindT x y z z'' t') -- this the key
             )--     `withProof` lem_esubFV_tsubFV x (FV y) z'' t_z g')
        where
            z''_        = fresh_var_excluding (concatE (Cons x t_x g) g') y
            z''         = z''_ ? lem_in_env_concat g g' z''_
                               ? lem_in_env_concat (Cons x t_x g) g' z''_
            p_z''_t'_wf = lem_change_var_wf (concatE (Cons x t_x g) g') z' t_z Empty 
                                    (unbindT z z' t') p_z'_t'_wf z''
{-                                    (z'' `withProof` lem_in_env_concat g g' z''
                                         `withProof` lem_in_env_concat (Cons x t_x g) g' z'')-}

{-@ lem_weaken_ent :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> { p:Pred | Set_sub (fv p) (binds (concatE g g')) }
        -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE g g') p } 
        -> { x:Vname | not (in_env x g) && not (in_env x g') && not (Set_mem x (fv p)) } -> t_x:Type
        -> ProofOf(Entails (concatE (Cons x t_x g) g') p) @-}
lem_weaken_ent :: Env -> Env -> WFEnv -> Pred -> Entails -> Vname -> Type -> Entails
lem_weaken_ent g g' p_env_wf p (EntPred env_ _p evals_func) x t_x
    = EntPred (concatE (Cons x t_x g) g') p evals_func'
        where
          env' = (concatE (Cons x t_x g) g')
          evals_func' ::  CSubst -> DenotesEnv -> EvalsTo
          evals_func' th' den_env'_th' = evals_func th den_env_th
                ? lem_remove_csubst th' x ( p ? lem_binds_env_th (concatE g g') th den_env_th)
            where
              th         = remove_fromCS th' x 
              den_env_th = lem_remove_var_denote_env g x t_x g' p_env_wf th' den_env'_th'
                               ? lem_binds_env_th env' th' den_env'_th' 


--            -> t_x:Type -> { p_g_tx:WFType | propOf p_g_tx == WFType g t_x }
{-@ lem_weaken_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> t:Type -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t) &&
                             wftypSize pf == wftypSize p_t_wf } / [wftypSize p_t_wf] @-}
lem_weaken_wf :: Env -> Env -> Type -> WFType -> Vname -> Type -> WFType -- -> WFType
lem_weaken_wf g g' t p_t_wf@(WFRefn _g y b p y' pf_p_bl) x t_x --p_ tx
    = WFRefn (concatE (Cons x t_x g) g') y b p
                           (y'' `withProof` lem_in_env_concat g g' y''
                                `withProof` lem_in_env_concat (Cons x t_x g) g' y''
                                `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'') 
          (lem_weaken_btyp (erase_env g) (BCons y'' (BTBase b) (erase_env g')) 
               (unbind y y'' p) (BTBase TBool) 
               (pf_y''_p_bl `withProof` lem_subFV_unbind y y' (FV y'') p) 
                           x (erase t_x))
        where
          y''         = fresh_var (concatE (Cons x t_x g) g')
          pf_y''_p_bl = lem_change_var_btyp (erase_env (concatE g g')) y' (BTBase b) BEmpty
                             (unbind y y' p) (BTBase TBool) pf_p_bl
                             (y'' `withProof` lem_erase_concat (Cons x t_x g) g'
                                  `withProof` lem_erase_concat g g')
lem_weaken_wf g g' t p_t_wf@(WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x --p_ tx
    = WFFunc (concatE (Cons x t_x g) g') y
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x ) --p_ tx)
             t' (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t') 
                         (p_y''_t'_wf `withProof` lem_tsubFV_unbindT y y' (FV y'') t')
                         x t_x) -- p_ tx)
        where
          y''         = fresh_var(concatE (Cons x t_x g) g')
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty
                             (unbindT y y' t') p_y'_t'_wf
                             (y'' `withProof` lem_in_env_concat g g' y''
                                  `withProof` lem_in_env_concat (Cons x t_x g) g' y'')
lem_weaken_wf g g' t p_t_wf@(WFExis gg y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x --p_ tx
    = WFExis (concatE (Cons x t_x g) g') y 
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x) -- p_ tx)
             t' (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t')
                         (p_y''_t'_wf `withProof` lem_tsubFV_unbindT y y' (FV y'')  t')
                         x t_x) -- p_ tx)
        where
          y''         = fresh_var (concatE (Cons x t_x g) g')
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty 
                             (unbindT y y' t') p_y'_t'_wf 
                             (y'' `withProof` lem_in_env_concat g g' y''
                                  `withProof` lem_in_env_concat (Cons x t_x g) g' y'')


{-@ lem_weaken_many_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> ProofOf(WFType g t) -> ProofOf(WFType (concatE g g') t) @-}
lem_weaken_many_wf :: Env -> Env -> Type -> WFType -> WFType
lem_weaken_many_wf g Empty           t p_g_t = p_g_t 
lem_weaken_many_wf g (Cons x t_x g') t p_g_t 
  = lem_weaken_wf (concatE g g') Empty t p_gg'_t x t_x 
     where
       p_gg'_t = lem_weaken_many_wf g g' t p_g_t 
 
-- -- -- -- -- -- -- -- -- -- -- -- -- ---
-- Consequences of the Typing Judgments --
-- -- -- -- -- -- -- -- -- -- -- -- -- ---

{-@ lem_typing_wf :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                      -> ProofOf(WFEnv g) -> ProofOf(WFType g t) @-} 
lem_typing_wf :: Env -> Expr -> Type -> HasType -> WFEnv -> WFType
lem_typing_wf g e t (TBC _g b) p_wf_g  = lem_wf_tybc g b
lem_typing_wf g e t (TIC _g n) p_wf_g  = lem_wf_tyic g n
lem_typing_wf g e t (TVar1 _g' x _t) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                     -> impossible "surely"
        (WFEBind g' p_g' _x _t p_g'_t) -> lem_weaken_wf g' Empty t p_g'_t x t -- p_g'_t
lem_typing_wf g e t (TVar2 g' x _t p_g'_x_t y s) p_wf_g
    = case p_wf_g of
        (WFEEmpty)                     -> impossible "Surely"
        (WFEBind g' p_g' _y _s p_g'_s) -> lem_weaken_wf g' Empty t 
                                              (lem_typing_wf g' e t p_g'_x_t p_g')
                                              y s -- p_g'_s
lem_typing_wf g e t (TPrm _g c) p_wf_g = lem_weaken_many_wf Empty g (ty c) (lem_wf_ty c)
                                             ? lem_empty_concatE g
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

{-@ lem_subtype_in_env_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> { x:Vname | (not (in_env x g)) && not (in_env x g') }
      -> s_x:Type -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> t:Type
      -> ProofOf(WFType (concatE (Cons x t_x g) g') t)
      -> ProofOf(WFType (concatE (Cons x s_x g) g') t) @-} 
lem_subtype_in_env_wf :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Type -> WFType -> WFType
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t (WFRefn env z b p z'_ p_z'env_p_bl)
    = WFRefn (concatE (Cons x s_x g) g') z b p z' p_z'env'_p_bl
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_z'env'_p_bl = p_z'env_p_bl ? lem_erase_concat (Cons x s_x g) g' -- (Cons z' (BTBase b) g')
                                       ? lem_erase_concat (Cons x t_x g) g' -- (Cons z' (BTBase b) g')
                                       ? lem_erase_subtype g s_x t_x p_sx_tx
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t (WFFunc env z t_z p_env_tz t' z'_ p_z'env_t')
    = WFFunc (concatE (Cons x s_x g) g') z t_z p_env'_tz t' z' p_z'env'_t'
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') p_z'env_t'
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t (WFExis env z t_z p_env_tz t' z'_ p_z'env_t')
    = WFExis (concatE (Cons x s_x g) g') z t_z p_env'_tz t' z' p_z'env'_t'
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') p_z'env_t'

{-@ lem_typing_hasbtype :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
        -> ProofOf(WFEnv g) -> ProofOf(HasBType (erase_env g) e (erase t)) @-}
lem_typing_hasbtype :: Env -> Expr -> Type -> HasType -> WFEnv -> HasBType
lem_typing_hasbtype g e t (TBC _g b) p_g_wf     = BTBC (erase_env g) b
lem_typing_hasbtype g e t (TIC _g n) p_g_wf     = BTIC (erase_env g) n
lem_typing_hasbtype g e t (TVar1 g' x _) p_g_wf = BTVar1 (erase_env g') x (erase t)
lem_typing_hasbtype g e t (TVar2 g' x _ p_x_t y s) p_g_wf
    = BTVar2 (erase_env g') x (erase t) p_x_er_t y (erase s) 
        where
          (WFEBind _ p_g'_wf _ _ _) = p_g_wf
          p_x_er_t = lem_typing_hasbtype g' e t p_x_t p_g'_wf
lem_typing_hasbtype g e t (TPrm _g c) p_g_wf    = BTPrm (erase_env g) c
lem_typing_hasbtype g e t (TAbs _g x t_x p_g_tx e' t' y p_yg_e'_t') p_g_wf
    = BTAbs (erase_env g) x (erase t_x) e' (erase t' ? lem_erase_tsubBV x (FV y) t')
            y p_yg_e'_er_t'
        where
          p_yg_wf       = WFEBind g p_g_wf y t_x p_g_tx
          p_yg_e'_er_t' = lem_typing_hasbtype (Cons y t_x g) (unbind x y e')
                                             (unbindT x y t') p_yg_e'_t' p_yg_wf
lem_typing_hasbtype g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) p_g_wf
    = BTApp (erase_env g) e' (erase t_x) (erase t') p_e'_er_txt' e_x p_ex_er_tx
        where
          p_e'_er_txt' = lem_typing_hasbtype g e' (TFunc x t_x t') p_e'_txt' p_g_wf
          p_ex_er_tx   = lem_typing_hasbtype g e_x t_x p_ex_tx p_g_wf
lem_typing_hasbtype g e t (TLet _g e_x t_x p_ex_tx x e' _t p_g_t y p_yg_e'_t) p_g_wf
    = BTLet (erase_env g) e_x (erase t_x) p_ex_er_tx x e' (erase t ? lem_erase_tsubBV x (FV y) t) 
            y p_yg_e'_er_t
        where
          p_g_tx       = lem_typing_wf g e_x t_x p_ex_tx p_g_wf
          p_yg_wf      = WFEBind g p_g_wf y t_x p_g_tx
          p_yg_e'_er_t = lem_typing_hasbtype (Cons y t_x g) (unbind x y e') 
                              (unbindT x y t)  p_yg_e'_t p_yg_wf
          p_ex_er_tx   = lem_typing_hasbtype g e_x t_x p_ex_tx p_g_wf         
lem_typing_hasbtype g e t (TAnn _g e' _ p_e'_t) p_g_wf
    = BTAnn (erase_env g) e' (erase t) --t 
            (t ? lem_free_subset_binds g t p_t_wf
               ? lem_tfreeBV_empty g t p_t_wf p_g_wf)
            (lem_typing_hasbtype g e' t p_e'_t p_g_wf)
        where
          p_t_wf = lem_typing_wf g e' t p_e'_t p_g_wf
lem_typing_hasbtype g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) p_g_wf
    = lem_typing_hasbtype g e s p_e_s p_g_wf ? lem_erase_subtype g s t p_s_t -- p_g_wf


-- Lemma? If we have G |- e : t and th \in [[G]] then BEmpty |-_B th(e) : erase(t)
{-@ lem_csubst_hasbtype :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t) -> ProofOf(WFEnv g)
        -> th:CSubst -> ProofOf(DenotesEnv g th) -> ProofOf(HasBType BEmpty (csubst th e) (erase t)) @-} 
lem_csubst_hasbtype :: Env -> Expr -> Type -> HasType -> WFEnv -> CSubst -> DenotesEnv -> HasBType
lem_csubst_hasbtype g e t p_e_t p_g_wf th den_g_th = lem_csubst_hasbtype' g e t p_e_er_t th den_g_th
    where
      p_e_er_t = lem_typing_hasbtype g e t p_e_t p_g_wf

{-@ lem_csubst_hasbtype' :: g:Env -> e:Expr -> t:Type -> ProofOf(HasBType (erase_env g) e (erase t))
        -> th:CSubst -> ProofOf(DenotesEnv g th) -> ProofOf(HasBType BEmpty (csubst th e) (erase t)) @-} 
lem_csubst_hasbtype' :: Env -> Expr -> Type -> HasBType -> CSubst -> DenotesEnv -> HasBType
lem_csubst_hasbtype' Empty           e t p_e_t th den_g_th = case den_g_th of 
  (DEmp)                                           -> p_e_t ? lem_binds_env_th Empty th den_g_th
lem_csubst_hasbtype' (Cons x t_x g') e t p_e_t th den_g_th = case den_g_th of
  (DExt g' th' den_g'_th' _x _tx v_x den_th'tx_vx) -> p_the_t
    where
      p_emp_vx_tx = get_btyp_from_den (ctsubst th' t_x) v_x den_th'tx_vx
                                      ? lem_erase_ctsubst th' t_x
      p_g'_vx_tx  = lem_weaken_many_btyp BEmpty (erase_env g') v_x (erase t_x) p_emp_vx_tx
                                         ? lem_empty_concatB (erase_env g')
      p_evx_t     = lem_subst_btyp (erase_env g') BEmpty x v_x (erase t_x) p_g'_vx_tx -- ? lem_empty_concatE g')
                                   e (erase t) p_e_t ? lem_erase_tsubFV x v_x t
      p_the_t     = lem_csubst_hasbtype' g' (subFV x v_x e) (tsubFV x v_x t) p_evx_t th' den_g'_th' 


{-@ lem_tfreeBV_unbindT_empty :: x:Vname -> y:Vname -> { t:Type | Set_emp (tfreeBV (unbindT x y t)) }
        -> { pf:_ | Set_emp (tfreeBV t) || tfreeBV t == Set_sng x } @-}
lem_tfreeBV_unbindT_empty :: Vname -> Vname -> Type -> Proof
lem_tfreeBV_unbindT_empty x y t = toProof ( S.empty === tfreeBV (unbindT x y t)
                                        === S.difference (tfreeBV t) (S.singleton x) )

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
