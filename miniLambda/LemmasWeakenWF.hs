{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWeakenWF where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
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
import Entailments
import LemmasChangeVarWF

{-@ reflect foo38 @-}
foo38 x = Just x
foo38 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_weaken_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } -> t:Type 
            -> { p_t_wf:WFType | propOf p_t_wf == WFType (concatE g g') t }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> { pf:WFType | propOf pf == (WFType (concatE (Cons x t_x g) g') t) } / [wftypSize p_t_wf] @-}
lem_weaken_wf :: Env -> Env -> Type -> WFType -> Vname -> Type -> WFType 
lem_weaken_wf g g' t p_t_wf@(WFRefn env y b p y' pf_p_bl) x t_x 
    = WFRefn (concatE (Cons x t_x g) g') y b p y''
          (lem_weaken_ftyp (erase_env g) (FCons y'' (FTBasic b) (erase_env g'))
               (unbind y y'' p) (FTBasic TBool) 
               (pf_y''_p_bl `withProof` lem_subFV_unbind y y' (FV y'') p 
                    ? lem_erase_concat g (Cons y'' (TRefn b 1 (Bc True)) g'))
                           x (erase t_x) ? lem_erase_concat (Cons x t_x g) g')
        where
          y''_         = fresh_var (concatE (Cons x t_x g) g')
          y''          = y''_ `withProof` lem_in_env_concat g g' y''_
                              `withProof` lem_in_env_concat (Cons x t_x g) g' y''_
                              `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y''_
          pf_y''_p_bl  = lem_change_var_ftyp (erase_env (concatE g g')) y' (FTBasic b) FEmpty
                             (unbind y y' p) (FTBasic TBool) pf_p_bl y''
lem_weaken_wf g g' t p_t_wf@(WFFunc env y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x 
    = WFFunc (concatE (Cons x t_x g) g') y
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x ) 
             t'  (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t') 
                         (p_y''_t'_wf `withProof` lem_tsubFV_unbindT y y' (FV y'') t')
                         x t_x) 
        where
          y''_        = fresh_var(concatE (Cons x t_x g) g')
          y''         = y''_  `withProof` lem_in_env_concat g g' y''_
                              `withProof` lem_in_env_concat (Cons x t_x g) g' y''_
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty 
                             (unbindT y y' t') p_y'_t'_wf y''
lem_weaken_wf g g' t p_t_wf@(WFExis env y t_y p_ty_wf t' y' p_y'_t'_wf) x t_x 
    = WFExis (concatE (Cons x t_x g) g') y 
             t_y (lem_weaken_wf g g' t_y p_ty_wf x t_x) 
             t'  (y'' `withProof` lem_free_bound_in_env (concatE g g') t p_t_wf y'')
             (lem_weaken_wf g (Cons y'' t_y g') (unbindT y y'' t') 
                         (p_y''_t'_wf `withProof` lem_tsubFV_unbindT y y' (FV y'')  t')
                         x t_x) -- p_ tx)
        where
          y''_        = fresh_var(concatE (Cons x t_x g) g')
          y''         = y''_  `withProof` lem_in_env_concat g g' y''_
                              `withProof` lem_in_env_concat (Cons x t_x g) g' y''_
          p_y''_t'_wf = lem_change_var_wf (concatE g g') y' t_y Empty 
                             (unbindT y y' t')  p_y'_t'_wf y''

{-@ lem_weaken_many_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> t:Type -> ProofOf(WFType g t) -> ProofOf(WFType (concatE g g') t) @-}
lem_weaken_many_wf :: Env -> Env -> Type -> WFType -> WFType
lem_weaken_many_wf g Empty            t p_g_t = p_g_t 
lem_weaken_many_wf g (Cons x t_x g')  t p_g_t 
  = lem_weaken_wf    (concatE g g') Empty t p_gg'_t x t_x
     where
       p_gg'_t   = lem_weaken_many_wf g g' t p_g_t ? lem_erase_concat g g'
