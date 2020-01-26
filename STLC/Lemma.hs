{-# LANGUAGE GADTs #-}

-- The following module presents a mechanization of the proofs of type
-- soundness and termination for a Simply Typed Lambda Calculus
-- and is based on Lecture notes "Well-typed Programs Don't Go Wrong"
-- and "Type Soundness and Termination in One Easy Lemma" by Nadia
-- Polikarpova for CSE 130 at UC San Diego.

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}

module Lemma where

import Language.Haskell.Liquid.ProofCombinators 
import Syntax
import Semantics

a = BStep
b = HasType
c = WBValue
d = WBEnv

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- Main Lemma: If G |- e : t and env :: g then exists v
-- --               such that E; e ==> v and v :: T. 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

{-@ main_lemma :: e:Expr -> t:Type -> env:Env -> g:Ctx 
                -> ProofOf(HasType g e t) -> ProofOf(WBEnv env g)
                -> (Value, (BStep, WBValue))<{\v pfs ->
                      (propOf (fst pfs) == BStep env e v) && (propOf (snd pfs) == WBValue v t)}> @-} 
main_lemma :: Expr -> Type -> Env -> Ctx -> HasType -> WBEnv
                -> (Value, (BStep, WBValue))
main_lemma e t env g (TNum _g n)    _       = (VNum n, (ENum env n, WBVNum n))
  -- Case T-Num: e = (N n) and t = Int
main_lemma e t env g (TVar _g x _t) p_env_g = (v, (EVar env x v, p_v_t))
  where
    (v, p_v_t) = lem_lookup_in_wbenv env x t g p_env_g
  -- Case T-Var: e = (V x)
main_lemma e t env g (TAdd _g e1 p_e1_Int e2 p_e2_Int) p_env_g = (VNum n, (bstep_e, WBVNum n))
  where
    (VNum n1, (bstep_e1, p_wb_v1)) = main_lemma e1 TInt env g p_e1_Int p_env_g
    (VNum n2, (bstep_e2, p_wb_v2)) = main_lemma e2 TInt env g p_e2_Int p_env_g
    n                         = n1 + n2
    bstep_e                   = EAdd env e1 n1 bstep_e1 e2 n2 bstep_e2 n
  -- Case T-Add: e = (Add e1 e2)
main_lemma e t env g (TAbs _g x t1 e' t2 p_e2_t2) p_env_g = (VCls env x e', (bstep_e, wb_clos))
  where
    bstep_e = EAbs env x e'
    wb_clos = WBVCls env x e' t1 t2 behaves_on_arg
      where
        behaves_on_arg v1 p_v1_t1 = (v2, (bstep_e', p_v2_t2))
          where
            p_cons_env = WBCons env x v1 t1 g p_v1_t1 p_env_g
            (v2, (bstep_e', p_v2_t2)) = main_lemma e' t2 (Cons x v1 env) (CCons x t1 g) p_e2_t2 p_cons_env
  -- Case T-Abs: e = (Lambda x e') 
main_lemma e t env g (TApp _g e1 t2 _t p_e1_t2t e2 p_e2_t2) p_env_g = (v, (bstep_e1e2, p_v_t)) 
  where 
    (VCls env' x' e', (bstep_e1, WBVCls _env' _x' _e' _ _ behaves_on_arg)) 
      = main_lemma e1 (TFunc t2 t) env g p_e1_t2t p_env_g
    (v2, (bstep_e2, p_v2_t2)) = main_lemma e2 t2 env g p_e2_t2 p_env_g
    (v, (bstep_e', p_v_t)) = behaves_on_arg v2 p_v2_t2
    bstep_e1e2 = EApp env e1 env' x' e' bstep_e1 e2 v2 bstep_e2 v bstep_e'
