{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasInversion where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsEnvironments
import WellFormedness
import BasicPropsWellFormedness
import Typing
import LemmasTyping
import LemmasNarrowingTyp
import LemmasTransitive

-- A collection of Lemmas about inverting typing judgements for abstraction types. In our
--   system this is not trivial because TSub could be used finitely many times to produce
--   the judgment. The key point is to use transitivity of subtyping to collapse a chain
--   of applications of T-Sub to a single use of T-Sub

{-@ measure singleSub @-} -- i.e., exactly one
singleSub :: HasType -> Bool
singleSub (TSub _ _ _ _ p_e_s _ _ _ _) = case p_e_s of
  (TSub {}) -> False
  _         -> True
singleSub _                            = False -- True

{-@ measure tSubDepth @-}
{-@ tSubDepth :: HasType -> { n:Int | n >= 1 } @-}
tSubDepth :: HasType -> Int
tSubDepth (TSub _ _ _ _ p_e_s _ _ _ _) = tSubDepth p_e_s + 1
tSubDepth p_e_s                        = 1

{-@ lem_collapse_sub :: g:Env -> e:Expr -> t:Type -> ProofOf(WFEnv g)
        -> { p_e_t:HasType  | propOf p_e_t  == HasType g e t && isTSub p_e_t }
        -> { p'_e_t:HasType | propOf p'_e_t == HasType g e t && singleSub p'_e_t }
         / [ tSubDepth p_e_t ] @-}
lem_collapse_sub :: Env -> Expr -> Type -> WFEnv -> HasType -> HasType
lem_collapse_sub g e t p_g_wf p_e_t@(TSub n _ _ s p_e_s _ k_t p_g_t p_s_t) = case p_e_s of
  (TSub m _ _ w p_e_w _ k_s p_g_s p_w_s) -> lem_collapse_sub g e t p_g_wf p'_e_t      
    where
      p'_e_t = TSub n' g e w p_e_w t k_t p_g_t p_w_t
      p_g_w  = lem_typing_wf g e w p_e_w p_g_wf
      p_w_t  = lem_sub_trans g p_g_wf w Star p_g_w s t k_t p_g_t p_w_s p_s_t
      n'     = max (typSize p_e_w) (subtypSize p_w_t)
  _                                      -> p_e_t

{-@ lem_lambda_tsub_no_sbind :: g:Env -> e:Expr -> s:Type -> t_x:Type -> t:Type
        -> { p_le_s:HasType | propOf p_le_s == HasType g (Lambda e) s && not (isTSub p_le_s) }
        -> { p_s_t:Subtype  | propOf p_s_t  == Subtype g s (TFunc t_x t) }
        -> { pf:_ | isSFunc p_s_t } @-} -- && not (isSBind p_s_t) } @-}
lem_lambda_tsub_no_sbind :: Env -> Expr -> Type -> Type -> Type -> HasType -> Subtype -> Proof
lem_lambda_tsub_no_sbind g e s t_x t p_le_s p_s_t = case p_s_t of
  (SFunc {}) -> ()
  (SBind {}) -> case p_le_s of
    (TAbs {}) -> impossible "s must be TFunc"

{-@ lem_invert_tabs :: g:Env -> e:Expr -> t_x:Type -> t:Type
       -> ProofOf(HasType g (Lambda e) (TFunc t_x t)) -> ProofOf(WFEnv g)
       -> { p'_e_t:HasType | propOf p'_e_t == HasType g (Lambda e) (TFunc t_x t) &&
                             isTAbs p'_e_t } @-}
lem_invert_tabs :: Env -> Expr -> Type -> Type -> HasType -> WFEnv -> HasType
lem_invert_tabs g e t_x t' p_le_txt' p_g_wf = case p_le_txt' of
  (TAbs {}) -> p_le_txt'
  (TSub {}) 
    -> let (TSub _ _ _ s p_le_s _ k_t p_g_txt' p_s_t)
               = lem_collapse_sub g (Lambda e) (TFunc t_x t') p_g_wf p_le_txt'
         in case p_s_t of
              (SFunc n _ _ _ p_tx_sx _ _  nms mk_p_s'_t') -> case p_le_s of
                (TAbs   n' _ s_x k_sx p_g_sx _ s' nms'  mk_p_e_s') 
                    -> TAbs (n + n' + 2) g t_x k_tx p_g_tx e t' nms''' mk_p_e_t'
                  where
                    {-@ mk_p_e_t' :: { y:Vname | NotElem y nms''' }
                          -> { pf:HasType | propOf pf == 
                                 HasType (Cons y t_x g) (unbind y e) (unbindT y t') &&
                                            sizeOf pf <= n + n' + 2 } @-}
                    mk_p_e_t' y = TSub (n + n' + 1) (Cons y t_x g) (unbind y e) (unbindT y s') 
                                       p_yg_e_s' (unbindT y t') k' (mk_p_yg_t' y) (mk_p_s'_t' y)
                      where
                        {-@ p_yg_e_s' :: { pf':HasType | propOf pf' ==
                                               HasType (Cons y t_x g) (unbind y e) (unbindT y s')
                                                      && sizeOf pf' <= n + n' + 1 } @-}
                        p_yg_e_s' = lem_narrow_typ g Empty y t_x k_tx p_g_tx s_x p_tx_sx p_g_wf
                                                   (unbind y e) (unbindT y s') (mk_p_e_s' y)
                    (WFFunc _ _ k_tx p_g_tx _ k'      nms'' mk_p_yg_t')
                      = lem_wffunc_for_wf_tfunc g t_x t' k_t p_g_txt'
                    nms'''      = unionEnv (union nms (union nms' nms'')) g
              (SBind {}) -> impossible ("by" ? lem_lambda_tsub_no_sbind g e s t_x t' p_le_s p_s_t)


{-@ lem_lambdaT_tsub_no_sbind :: g:Env -> k:Kind -> e:Expr -> s:Type -> k':Kind -> t:Type
        -> { p_le_s:HasType | propOf p_le_s == HasType g (LambdaT k e) s && not (isTSub p_le_s) }
        -> { p_s_t:Subtype  | propOf p_s_t  == Subtype g s (TPoly k' t) }
        -> { pf:_ | isSPoly p_s_t } @-} -- && not (isSBind p_s_t) } @-}
lem_lambdaT_tsub_no_sbind :: Env -> Kind -> Expr -> Type -> Kind -> Type 
                                 -> HasType -> Subtype -> Proof
lem_lambdaT_tsub_no_sbind g k e s k' t' p_le_s p_s_t = case p_s_t of
  (SPoly {}) -> ()
  (SBind {}) -> case p_le_s of
    (TAbsT {}) -> impossible "s must be TPoly"

{-@ lem_invert_tabst :: g:Env -> k:Kind -> e:Expr -> t:Type
       -> ProofOf(HasType g (LambdaT k e) (TPoly k t)) -> ProofOf(WFEnv g)
       -> { p'_e_t:HasType | propOf  p'_e_t == HasType g (LambdaT k e) (TPoly k t) &&
                             isTAbsT p'_e_t } @-}
lem_invert_tabst :: Env -> Kind -> Expr -> Type -> HasType -> WFEnv -> HasType
lem_invert_tabst g k e t' p_le_kt' p_g_wf = case p_le_kt' of
  (TAbsT {}) -> p_le_kt'
  (TSub {}) 
    -> let (TSub _ _ _ s p_le_s _ k_t p_g_kt' p_s_t)
               = lem_collapse_sub g (LambdaT k e) (TPoly k t') p_g_wf p_le_kt'
         in case p_s_t of
              (SPoly n _ _ _ _ nms mk_p_s'_t')
                  -> TAbsT (max n n' + 1) g k e t' nms''' mk_p_e_t'
                where
                  {-@ mk_p_e_t' :: { a:Vname | NotElem a nms''' }
                        -> { pf:HasType | propOf pf ==
                                HasType (ConsT a k g) (unbind_tv a e) (unbind_tvT a t') &&
                                          sizeOf pf <= max n n' + 1 } @-}
                   mk_p_e_t' a = TSub (max n n') (ConsT a k g) (unbind_tv a e) (unbind_tvT a s')
                                      (mk_p_e_s' a) (unbind_tvT a t') k_t' (mk_p_ag_t' a)
                                      (mk_p_s'_t' a)
                   (TAbsT n' _ _ _ s' nms'  mk_p_e_s')  = p_le_s
                   (WFPoly _ _ _ k_t' nms'' mk_p_ag_t') 
                     = lem_wfpoly_for_wf_tpoly' g k t' k_t p_g_kt'
                   nms'''      = unionEnv (union nms (union nms' nms'')) g
              (SBind {}) -> impossible ("by" ? lem_lambdaT_tsub_no_sbind g k e s k t' p_le_s p_s_t)

{-@ lem_lambdaT_tpoly_same_kind :: g:Env -> k:Kind -> e:Expr -> k':Kind -> t':Type 
       -> { p_ke_k't':HasType | propOf p_ke_k't' == HasType g (LambdaT k e) (TPoly k' t') }
       -> ProofOf(WFEnv g) -> { pf:_              | k == k' } / [sizeOf p_ke_k't'] @-}
lem_lambdaT_tpoly_same_kind :: Env -> Kind -> Expr -> Kind -> Type -> HasType -> WFEnv -> Proof
lem_lambdaT_tpoly_same_kind g k e k' t' p_ke_k't' p_g_wf = case p_ke_k't' of
  (TAbsT {}) -> ()
  (TSub {})  -> case lem_collapse_sub g (LambdaT k e) (TPoly k' t') p_g_wf p_ke_k't' of
    (TSub _ _ _ s p_ke_s _ _ _ p_s_t) -> case p_s_t of
      (SPoly {}) -> case p_ke_s of
        (TAbsT {}) -> ()
      (SBind {}) -> impossible ("by" ? lem_lambdaT_tsub_no_sbind g k e s k' t' p_ke_s p_s_t)
