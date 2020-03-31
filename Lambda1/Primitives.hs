{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Primitives where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Semantics
import Typing

-- force these into scope
semantics = (Step, EvalsTo)
typing = (HasBType, HasType, WFType, WFEnv, Subtype)
denotations = (Entails, Denotes, DenotesEnv)

{-
-- Constant and Primitive Typing Lemmas
-- Lemma. Well-Formedness of Primitive/Constant Types
{-@ lem_wf_tybc :: g:Env -> b:Bool -> ProofOf(WFType g (tybc b)) @-}
lem_wf_tybc :: Env -> Bool -> WFType
lem_wf_tybc g b = WFRefn g 1 TBool pred y pf_pr_bool
  where
     pred       = (App (App (Prim Eqv) (BV 1)) (Bc b)) 
     y          = (fresh_var g)
     g'         = (BCons y (BTBase TBool) (erase_env g))
     pf_eqv_v   = BTApp g' (Prim Eqv) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool)) 
                           (BTPrm g' Eqv) (FV y) (BTVar1 (erase_env g) y (BTBase TBool))
     -- pf_pr_bool :: ProofOf(HasBType g' pred (BTBase TBool)) @- }
     pf_pr_bool = BTApp g' (App (Prim Eqv) (FV y)) (BTBase TBool) (BTBase TBool) 
                           pf_eqv_v (Bc b) (BTBC g' b)

{-@ lem_wf_tyic :: g:Env -> n:Int -> ProofOf(WFType g (tyic n)) @-}
lem_wf_tyic :: Env -> Int -> WFType
lem_wf_tyic g n = WFRefn g 1 TInt pred y pf_pr_bool
  where
    pred        = (App (App (Prim Eq) (BV 1)) (Ic n))
    y           = fresh_var g
    g'          = (BCons y (BTBase TInt) (erase_env g))
    pf_eq_v     = BTApp g' (Prim Eq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool)) 
                           (BTPrm g' Eq) (FV y) (BTVar1 (erase_env g) y (BTBase TInt))
    pf_pr_bool  = BTApp g' (App (Prim Eq) (FV y)) (BTBase TInt) (BTBase TBool) 
                           pf_eq_v (Ic n) (BTIC g' n)


-- these are various helpers to show ty(c) always well-formed
{-@ pf_base_wf :: g:Env -> b:Base -> x:Vname 
                            -> ProofOf(WFType g (TRefn b x (Bc True))) @-}
pf_base_wf :: Env -> Base -> Vname -> WFType
pf_base_wf g b x = WFRefn g x b (Bc True) y (BTBC g' True) 
  where
    y  = fresh_var g
    g' = BCons y (BTBase b) (erase_env g)

{-@ pf_app_prim_wf :: g:BEnv -> c:Prim 
      -> { b:Base | erase (ty c) == (BTFunc (BTBase b) (BTFunc (BTBase b) (BTBase TBool)))}
      -> { v:Vname | bound_inB v (BTBase b) g }
      -> ProofOf(HasBType g (App (Prim c) (FV v)) (BTFunc (BTBase b) (BTBase TBool))) @-}
pf_app_prim_wf :: BEnv -> Prim -> Base -> Vname -> HasBType
pf_app_prim_wf g c b v = BTApp g (Prim c) (BTBase b) (BTFunc (BTBase b) (BTBase TBool))
                           (BTPrm g c) (FV v) (simpleBTVar g v (BTBase b))

{-@ pf_app_app_prim_wf :: g:BEnv -> c:Prim 
      -> { b:Base | erase (ty c) == BTFunc (BTBase b) (BTFunc (BTBase b) (BTBase TBool)) }
      -> { x:Vname | bound_inB x (BTBase b) g} -> { y:Vname | bound_inB y (BTBase b) g }
      -> ProofOf(HasBType g (App (App (Prim c) (FV x)) (FV y)) (BTBase TBool)) @-}
pf_app_app_prim_wf :: BEnv -> Prim -> Base -> Vname -> Vname -> HasBType
pf_app_app_prim_wf g c b x y = BTApp g (App (Prim c) (FV x)) (BTBase b) (BTBase TBool)
                               (pf_app_prim_wf g c b x) (FV y) (simpleBTVar g y (BTBase b)) 

{-@ lem_wf_ty :: g:Env -> c:Prim -> ProofOf(WFType g (ty c)) @-}
lem_wf_ty :: Env -> Prim -> WFType
lem_wf_ty g' And   = WFFunc g' 1 (TRefn TBool 4 (Bc True)) (pf_base_wf g' TBool 4)
                                      middle_type pf_middle_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 2 (BTBase TBool) 
                                            (BCons 1 (BTBase TBool) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_and_xy    = pf_app_app_prim_wf g And TBool 1 2
    pf_refn_and  = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim And) (FV 1)) (FV 2)) pf_and_xy
    g1           = Cons 2 (TRefn TBool 5 (Bc True))
                                            (Cons 1 (TRefn TBool 4 (Bc True)) g')
    g2           = Cons 1 (TRefn TBool 4 (Bc True)) g'
    inner_type   = TRefn TBool 3 (subFV 3 (BV 3) (refn_pred And))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred And) pf_refn_and
    middle_type  = TFunc 2 (TRefn TBool 5 (Bc True)) (tsubFV 2 (BV 2) inner_type) 
    pf_middle_wf = WFFunc g2 2 (TRefn TBool 5 (Bc True)) (pf_base_wf g2 TBool 5)
                                 inner_type pf_inner_wf 
lem_wf_ty g' Or     = WFFunc g' 1 (TRefn TBool 4 (Bc True)) (pf_base_wf g' TBool 4)
                                      middle_type  pf_middle_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 2 (BTBase TBool) 
                                            (BCons 1 (BTBase TBool) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_or_xy     = pf_app_app_prim_wf g Or TBool 1 2
    pf_refn_or   = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Or) (FV 1)) (FV 2)) pf_or_xy
    g1           = Cons 2 (TRefn TBool 5 (Bc True))
                                            (Cons 1 (TRefn TBool 4 (Bc True)) g')
    g2           = Cons 1 (TRefn TBool 4 (Bc True)) g'
    inner_type   = TRefn TBool 3 (subFV 3 (BV 3) (refn_pred Or))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred Or) pf_refn_or
    middle_type  = TFunc 2 (TRefn TBool 5 (Bc True)) (tsubFV 2 (BV 2) inner_type)
    pf_middle_wf = WFFunc g2 2 (TRefn TBool 5 (Bc True)) (pf_base_wf g2 TBool 5)
                                 inner_type pf_inner_wf 
lem_wf_ty g' Not    = WFFunc g' 1 (TRefn TBool 4 (Bc True)) (pf_base_wf g' TBool 4)
                                      inner_type pf_inner_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 1 (BTBase TBool) (erase_env g'))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_not_x     = BTApp g (Prim Not) (BTBase TBool) (BTBase TBool)
                           (BTPrm g Not) (FV 1) (simpleBTVar g 1 (BTBase TBool))
    pf_refn_not  = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (Prim Not) (FV 1)) pf_not_x
    g1           = Cons 1 (TRefn TBool 4 (Bc True)) g'
    inner_type   = TRefn TBool 3 (tsubFV 3 (BV 3) (refn_pred Not))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred Not) pf_refn_not
lem_wf_ty g' Eqv    = WFFunc g' 1 (TRefn TBool 4 (Bc True)) (pf_base_wf g' TBool 4)
                                      middle_type pf_middle_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 2 (BTBase TBool) 
                                            (BCons 1 (BTBase TBool) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_and_xy    = pf_app_app_prim_wf g And TBool 1 2
    pf_not_x     = BTApp g (Prim Not) (BTBase TBool) (BTBase TBool)
                           (BTPrm g Not) (FV 1) (simpleBTVar g 1 (BTBase TBool))
    pf_not_y     = BTApp g (Prim Not) (BTBase TBool) (BTBase TBool)
                           (BTPrm g Not) (FV 2) (simpleBTVar g 2 (BTBase TBool))
    pf_and_nx    = BTApp g (Prim And) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool))
                               (BTPrm g And) (App (Prim Not) (FV 1)) pf_not_x
    pf_and_nxny  = BTApp g (App (Prim And) (App (Prim Not) (FV 1))) 
                               (BTBase TBool) (BTBase TBool) pf_and_nx
                               (App (Prim Not) (FV 2)) pf_not_y
    pf_iff_xy1   = BTApp g (Prim Or) (BTBase TBool) (BTFunc (BTBase TBool) (BTBase TBool))
                               (BTPrm g Or) (App (App (Prim And) (FV 1)) (FV 2)) pf_and_xy 
    pf_iff_xy2   = BTApp g (App (Prim Or) (App (App (Prim And) (FV 1)) (FV 2)))
                               (BTBase TBool) (BTBase TBool) pf_iff_xy1
                               (App (App (Prim And) (App (Prim Not) (FV 1)))
                                    (App (Prim Not) (FV 2))) pf_and_nxny
    pf_refn_eqv  = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Or) (App (App (Prim And) (FV 1)) (FV 2)))
                                            (App (App (Prim And) (App (Prim Not) (FV 1)))
                                                 (App (Prim Not) (FV 2)))) pf_iff_xy2
    g1           = Cons 2 (TRefn TBool 5 (Bc True))
                                            (Cons 1 (TRefn TBool 4 (Bc True)) g')
    g2           = Cons 1 (TRefn TBool 4 (Bc True)) g'
    inner_type   = TRefn TBool 3 (subFV 3 (BV 3) (refn_pred Eqv))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred Eqv) pf_refn_eqv
    middle_type  = TFunc 2 (TRefn TBool 5 (Bc True)) (tsubFV 2 (BV 2) inner_type)
    pf_middle_wf = WFFunc g2 2 (TRefn TBool 5 (Bc True)) (pf_base_wf g2 TBool 5)
                                 inner_type pf_inner_wf 
lem_wf_ty g' Leq    = WFFunc g' 1 (TRefn TInt 4 (Bc True)) (pf_base_wf g' TInt 4)
                                      middle_type pf_middle_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 2 (BTBase TInt) 
                                            (BCons 1 (BTBase TInt) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_leq_xy    = pf_app_app_prim_wf g Leq TInt 1 2
    pf_refn_leq  = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Leq) (FV 1)) (FV 2)) pf_leq_xy
    g1           = Cons 2 (TRefn TInt 5 (Bc True))
                                            (Cons 1 (TRefn TInt 4 (Bc True)) g')
    g2           = Cons 1 (TRefn TInt 4 (Bc True)) g'
    inner_type   = TRefn TBool 3 (subFV 3 (BV 3) (refn_pred Leq))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred Leq) pf_refn_leq
    middle_type  = TFunc 2 (TRefn TInt 5 (Bc True)) (tsubFV 2 (BV 2) inner_type)
    pf_middle_wf = WFFunc g2 2 (TRefn TInt 5 (Bc True)) (pf_base_wf g2 TInt 5)
                                 inner_type pf_inner_wf 
lem_wf_ty g' (Leqn n) = WFFunc g' 2 (TRefn TInt 5 (Bc True)) (pf_base_wf g' TInt 5)
                                      inner_type pf_inner_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 2 (BTBase TInt) (erase_env g'))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_leqn_n    = BTApp g (Prim Leq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool))
                      (BTPrm g Leq) (Ic n) (BTIC g n)
    pf_leqn_ny   = BTApp g (App (Prim Leq) (Ic n)) (BTBase TInt) (BTBase TBool)
                      pf_leqn_n (FV 2) (simpleBTVar g 2 (BTBase TInt))
    pf_refn_leqn = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Leq) (Ic n)) (FV 2)) pf_leqn_ny
    g1           = Cons 2 (TRefn TInt 5 (Bc True)) g'
    inner_type   = TRefn TBool 3 (subFV 3 (BV 3) (refn_pred (Leqn n)))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred (Leqn n)) pf_refn_leqn
lem_wf_ty g' Eq     = WFFunc g' 1 (TRefn TInt 4 (Bc True)) (pf_base_wf g' TInt 4)
                                      middle_type pf_middle_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 2 (BTBase TInt) 
                                            (BCons 1 (BTBase TInt) (erase_env g')))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_eq_xy     = pf_app_app_prim_wf g Eq TInt 1 2
    pf_refn_eq   = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Eq) (FV 1)) (FV 2)) pf_eq_xy
    g1           = Cons 2 (TRefn TInt 5 (Bc True))
                                            (Cons 1 (TRefn TInt 4 (Bc True)) g')
    g2           = Cons 1 (TRefn TInt 4 (Bc True)) g'
    inner_type   = TRefn TBool 3 (subFV 3 (BV 3) (refn_pred Eq))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred Eq) pf_refn_eq
    middle_type  = TFunc 2 (TRefn TInt 5 (Bc True)) (tsubFV 2 (BV 2) inner_type)
    pf_middle_wf = WFFunc g2 2 (TRefn TInt 5 (Bc True)) (pf_base_wf g2 TInt 5)
                                 inner_type pf_inner_wf 
lem_wf_ty g' (Eqn n) = WFFunc g' 2 (TRefn TInt 5 (Bc True)) (pf_base_wf g' TInt 5)
                                      inner_type pf_inner_wf
  where
    g            = BCons 3 (BTBase TBool) (BCons 2 (BTBase TInt) (erase_env g'))
    pf_eqv_v     = pf_app_prim_wf g Eqv TBool 3
    pf_eqn_n     = BTApp g (Prim Eq) (BTBase TInt) (BTFunc (BTBase TInt) (BTBase TBool))
                      (BTPrm g Eq) (Ic n) (BTIC g n)
    pf_eqn_ny    = BTApp g (App (Prim Eq) (Ic n)) (BTBase TInt) (BTBase TBool)
                      pf_eqn_n (FV 2) (simpleBTVar g 2 (BTBase TInt))
    pf_refn_eqn  = BTApp g (App (Prim Eqv) (FV 3)) (BTBase TBool) (BTBase TBool) pf_eqv_v
                        (App (App (Prim Eq) (Ic n)) (FV 2)) pf_eqn_ny
    g1           = Cons 2 (TRefn TInt 5 (Bc True)) g'
    inner_type   = TRefn TBool 3 (subFV 3 (BV 3) (refn_pred (Eqn n)))
    pf_inner_wf  = WFRefn g1 3 TBool (refn_pred (Eqn n)) pf_refn_eqn
-}


-- Lemma. Denotations of Primitive/Constant Types
{-@ assume lem_den_tybc :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
        -> b:Bool -> ProofOf(Denotes (ctsubst th (tybc b)) (Bc b)) @-}
lem_den_tybc :: Env -> CSubst -> DenotesEnv -> Bool -> Denotes
lem_den_tybc g th den_g_th b = undefined

{-@ assume lem_den_tyic :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
        -> n:Int -> ProofOf(Denotes (ctsubst th (tyic n)) (Ic n)) @-}
lem_den_tyic :: Env -> CSubst -> DenotesEnv -> Int -> Denotes
lem_den_tyic g th den_g_th n = undefined

{-@ assume lem_den_ty :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th)
        -> c:Prim -> ProofOf(Denotes (ctsubst th (ty c)) (Prim c)) @-}
lem_den_ty :: Env -> CSubst -> DenotesEnv -> Prim -> Denotes
lem_den_ty g th den_g_th c = undefined

{-    p        = (App (App (Prim Eqv) (BV 1)) (Bc b))
    step1    = EApp1 (App (Prim Eqv) (Bc b)) (delta Eqv (Bc b)) (EPrim Eqv (Bc b)) (Bc b)
    step2    = 
-- (subBV 1 (Bc b) p) => App (delta Eqv (Bc b)) (Bc b)
    EPrim Eqv (Bc b)  -- Lam 1 BV1 or Lam 1 (Not BV 1)
    ev_del_t = if b then
                    else
    ..
    den_bl_b = DRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc b)) (Bc b) 
                     (BTBC _g b) ev_pbx_tt -}

