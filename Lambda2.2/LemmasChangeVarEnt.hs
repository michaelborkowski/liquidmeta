{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasChangeVarEnt where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
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
import BasicPropsCSubst
import BasicPropsDenotes
import LemmasChangeVarWF
import LemmasChangeVarWFEnv

{-@ reflect foo33 @-}
foo33 x = Just x
foo33 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas  
------------------------------------------------------------------------------

-- Note: The technical lemmas lem_change_var_ftyp, lem_weaken_ftyp
--   are found in STLCLemmas.hs

{-@ lem_change_var_ent :: g:Env -> { x:Vname | not (in_env x g) } -> t_x:Type 
      -> { g':Env | not (in_env x g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (Cons x t_x g) g'))
      -> { p:Pred | Set_sub (fv p) (binds (concatE (Cons x t_x g) g')) }
      -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE (Cons x t_x g) g') p }
      -> { y:Vname | not (in_env y g) && not (in_env y g') && (x==y || not (Set_mem y (fv p))) }
      -> ProofOf(Entails (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) p)) @-}
lem_change_var_ent :: Env -> Vname -> Type -> Env -> WFEnv -> Expr -> Entails -> Vname -> Entails
lem_change_var_ent g x t_x g' p_env_wf p (EntPred _env _p evals_func) y
  = EntPred (concatE (Cons y t_x g) (esubFV x (FV y) g')) (subFV x (FV y) p) evals_func'
      where  -- env' = concatE (Cons y t_x g) (esubFV x (FV y) g')   env = concatE (Cons x t_x g) g'
        env'      = concatE (Cons y t_x g) (esubFV x (FV y) g')
        p_env'_wf = lem_change_var_wfenv g x t_x g' p_env_wf y
        env       = concatE (Cons x t_x g) g' ? lem_esubFV_inverse g x t_x g' p_env_wf y
        evals_func' :: CSub -> DenotesEnv -> EvalsTo
        evals_func' th' den_env'_th' = evals_func th den_env_th 
            ? lem_change_var_back th' y x 
            ? lem_binds_env_th (concatE (Cons y t_x g) (esubFV x (FV y) g')) th' den_env'_th'
            ? lem_change_var_in_csubst th x y (p ? lem_binds_env_th env th den_env_th)
            ? lem_chain_subFV x y (FV x) p 
          where
            th         = change_varCS th' (y ? lem_binds_env_th env' th' den_env'_th') x  
            den_env_th = lem_change_var_denote_env g y t_x (esubFV x (FV y) g') p_env'_wf th' den_env'_th'
                             (x ? lem_binds_env_th (concatE (Cons y t_x g) (esubFV x (FV y) g')) 
                                                   th' den_env'_th')
                             ? lem_esubFV_inverse  g x t_x g' p_env_wf y

{-@ lem_change_tvar_ent :: g:Env -> { a:Vname | not (in_env a g) } -> k_a:Kind
      -> { g':Env | not (in_env a g') && Set_emp (Set_cap (binds g) (binds g')) }
      -> ProofOf(WFEnv (concatE (ConsT a k_a g) g'))
      -> { p:Pred | Set_sub (fv p) (binds (concatE (ConsT a k_a g) g')) }
      -> { ent_g_p:Entails | propOf ent_g_p == Entails (concatE (ConsT a k_a g) g') p }
      -> { a':Vname | not (in_env a' g) && not (in_env a' g') && (a==a' || not (Set_mem a' (ftv p))) }
      -> ProofOf(Entails (concatE (ConsT a' k_a g) (echgFTV a a' g')) (chgFTV a a' p)) @-}
lem_change_tvar_ent :: Env -> Vname -> Kind -> Env -> WFEnv -> Expr -> Entails -> Vname -> Entails
lem_change_tvar_ent g a k_a g' p_env_wf p (EntPred _env _p evals_func) a' 
  = EntPred (concatE (ConsT a' k_a g) (echgFTV a a' g')) (chgFTV a a' p) evals_func'
      where
        env'      = concatE (ConsT a' k_a g) (echgFTV a a' g')
        p_env'_wf = lem_change_tvar_wfenv g a k_a g' p_env_wf a'
        env       = concatE (ConsT a k_a g) g' ? lem_echgFTV_inverse g a k_a g' p_env_wf a'
        evals_func' :: CSub -> DenotesEnv -> EvalsTo 
        evals_func' th' den_env'_th' = evals_func th den_env_th
            ? lem_change_tvar_back th' a' a
            ? lem_binds_env_th env' th' den_env'_th'
            ? lem_change_tvar_in_csubst th a a' (p ? lem_binds_env_th env th den_env_th)
            ? lem_chain_chgFTV a a' a p
          where
            th         = change_tvarCS th' (a' ? lem_binds_env_th env' th' den_env'_th') a
            den_env_th = lem_change_tvar_denote_env g a' k_a (echgFTV a a' g') p_env'_wf th' 
                             den_env'_th' (a ? lem_binds_env_th env' th' den_env'_th')
                             ? lem_echgFTV_inverse  g a k_a g' p_env_wf a'
