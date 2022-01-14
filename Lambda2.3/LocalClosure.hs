{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LocalClosure where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

--------------------------------------------------------------------------------
----- | Local Closure of Locally Nameless Terms
--------------------------------------------------------------------------------

--isLC_at j k e => isLC_at (j-1) k (open_at j y e)

{-@ lem_islc_at_weaken :: j:Index -> k:Index -> { j':Index | j <= j' } -> { k':Index | k <= k' }
        -> { e:Expr | isLC_at j k e } -> { pf:_ | isLC_at j' k' e } / [esize e] @-}
lem_islc_at_weaken :: Index -> Index -> Index -> Index -> Expr -> Proof
lem_islc_at_weaken j k j' k' (Bc _)         = ()
lem_islc_at_weaken j k j' k' (Ic _)         = ()
lem_islc_at_weaken j k j' k' (Prim _)       = ()
lem_islc_at_weaken j k j' k' (BV i)         = ()
lem_islc_at_weaken j k j' k' (FV x)         = ()
lem_islc_at_weaken j k j' k' (Lambda e)     = () ? lem_islc_at_weaken (j+1) k (j'+1) k' e
lem_islc_at_weaken j k j' k' (App e e')     = () ? lem_islc_at_weaken j     k j'     k' e
                                                 ? lem_islc_at_weaken j     k j'     k' e'
lem_islc_at_weaken j k j' k' (LambdaT k0 e) = () ? lem_islc_at_weaken j (k+1) j' (k'+1) e
lem_islc_at_weaken j k j' k' (AppT e t)     = () ? lem_islc_at_weaken j     k j'     k' e
                                                 ? lem_islct_at_weaken j    k j'     k' t
lem_islc_at_weaken j k j' k' (Let ex e)     = () ? lem_islc_at_weaken j     k j'     k' ex
                                                 ? lem_islc_at_weaken (j+1) k (j'+1) k' e
lem_islc_at_weaken j k j' k' (Annot e t)    = () ? lem_islc_at_weaken j     k j'     k' e
                                                 ? lem_islct_at_weaken j    k j'     k' t

{-@ lem_islcp_at_weaken :: j:Index -> k:Index -> { j':Index | j <= j' } -> { k':Index | k <= k' }
        -> { ps:Preds | isLCP_at j k ps } -> { pf:_ | isLCP_at j' k' ps } / [predsize ps] @-}
lem_islcp_at_weaken :: Index -> Index -> Index -> Index -> Preds -> Proof
lem_islcp_at_weaken j k j' k' PEmpty         = ()
lem_islcp_at_weaken j k j' k' (PCons p ps)   = () ? lem_islc_at_weaken  j k j' k' p
                                                  ? lem_islcp_at_weaken j k j' k' ps

{-@ lem_islct_at_weaken :: j:Index -> k:Index -> { j':Index | j <= j' } -> { k':Index | k <= k' }
        -> { t:Type | isLCT_at j k t } -> { pf:_ | isLCT_at j' k' t } / [tsize t] @-}
lem_islct_at_weaken :: Index -> Index -> Index -> Index -> Type -> Proof
lem_islct_at_weaken j k j' k' (TRefn    b ps) = () ? lem_islcp_at_weaken (j+1) k (j'+1) k' ps
lem_islct_at_weaken j k j' k' (TFunc   t_x t) = () ? lem_islct_at_weaken j     k j'     k' t_x
                                                   ? lem_islct_at_weaken (j+1) k (j'+1) k' t
lem_islct_at_weaken j k j' k' (TExists t_x t) = () ? lem_islct_at_weaken j     k j'     k' t_x
                                                   ? lem_islct_at_weaken (j+1) k (j'+1) k' t
lem_islct_at_weaken j k j' k' (TPoly   k0  t) = () ? lem_islct_at_weaken j (k+1) j' (k'+1) t


{-@ lem_islc_at_subFV :: j:Index -> k:Index -> x:Vname -> { v_x:Value | isLC v_x }
        -> { e:Expr | isLC_at j k e } -> { pf:_ | isLC_at j k (subFV x v_x e) } / [esize e] @-}
lem_islc_at_subFV :: Index -> Index -> Vname -> Expr -> Expr -> Proof
lem_islc_at_subFV j k x v_x (Bc _)         = ()
lem_islc_at_subFV j k x v_x (Ic _)         = ()
lem_islc_at_subFV j k x v_x (Prim _)       = ()
lem_islc_at_subFV j k x v_x (BV _)         = ()
lem_islc_at_subFV j k x v_x (FV y)
    | x == y    = () ? lem_islc_at_weaken 0 0 j k v_x
    | otherwise = ()
lem_islc_at_subFV j k x v_x (Lambda e)     = () ? lem_islc_at_subFV (j+1) k x v_x e
lem_islc_at_subFV j k x v_x (App e e')     = () ? lem_islc_at_subFV j     k x v_x e
                                                ? lem_islc_at_subFV j     k x v_x e'
lem_islc_at_subFV j k x v_x (LambdaT k' e) = () ? lem_islc_at_subFV j (k+1) x v_x e
lem_islc_at_subFV j k x v_x (AppT e rt)    = () ? lem_islc_at_subFV j     k x v_x e
                                                ? lem_islct_at_tsubFV j   k x v_x rt
lem_islc_at_subFV j k x v_x (Let e1 e2)    = () ? lem_islc_at_subFV j     k x v_x e1
                                                ? lem_islc_at_subFV (j+1) k x v_x e2
lem_islc_at_subFV j k x v_x (Annot e t)    = () ? lem_islc_at_subFV j     k x v_x e
                                                ? lem_islct_at_tsubFV j   k x v_x t

{-@ lem_islc_at_subFTV :: j:Index -> k:Index -> a:Vname -> { t_a:UserType | isLCT t_a }
        -> { e:Expr | isLC_at j k e } -> { pf:_ | isLC_at j k (subFTV a t_a e) } / [esize e] @-}
lem_islc_at_subFTV :: Index -> Index -> Vname -> Type -> Expr -> Proof
lem_islc_at_subFTV j k a t_a (Bc _)         = ()
lem_islc_at_subFTV j k a t_a (Ic _)         = ()
lem_islc_at_subFTV j k a t_a (Prim _)       = ()
lem_islc_at_subFTV j k a t_a (BV _)         = ()
lem_islc_at_subFTV j k a t_a (FV y)         = ()
lem_islc_at_subFTV j k a t_a (Lambda e)     = () ? lem_islc_at_subFTV (j+1) k a t_a e
lem_islc_at_subFTV j k a t_a (App e e')     = () ? lem_islc_at_subFTV j     k a t_a e
                                                 ? lem_islc_at_subFTV j     k a t_a e'
lem_islc_at_subFTV j k a t_a (LambdaT k' e) = () ? lem_islc_at_subFTV j (k+1) a t_a e
lem_islc_at_subFTV j k a t_a (AppT e rt)    = () ? lem_islc_at_subFTV j     k a t_a e
                                                 ? lem_islct_at_tsubFTV j   k a t_a rt
lem_islc_at_subFTV j k a t_a (Let e1 e2)    = () ? lem_islc_at_subFTV j     k a t_a e1
                                                 ? lem_islc_at_subFTV (j+1) k a t_a e2
lem_islc_at_subFTV j k a t_a (Annot e t)    = () ? lem_islc_at_subFTV j     k a t_a e
                                                 ? lem_islct_at_tsubFTV j   k a t_a t

{-@ lem_islcp_at_psubFV :: j:Index -> k:Index -> x:Vname -> { v_x:Value | isLC v_x }
        -> { ps:Preds | isLCP_at j k ps } -> { pf:_ | isLCP_at j k (psubFV x v_x ps) } / [predsize ps] @-}
lem_islcp_at_psubFV :: Index -> Index -> Vname -> Expr -> Preds -> Proof
lem_islcp_at_psubFV j k x v_x PEmpty         = ()
lem_islcp_at_psubFV j k x v_x (PCons p ps)   = () ? lem_islc_at_subFV   j k x v_x p
                                                  ? lem_islcp_at_psubFV j k x v_x ps

{-@ lem_islcp_at_psubFTV :: j:Index -> k:Index -> a:Vname -> { t_a:UserType | isLCT t_a }
        -> { ps:Preds | isLCP_at j k ps } -> { pf:_ | isLCP_at j k (psubFTV a t_a ps) } / [predsize ps] @-}
lem_islcp_at_psubFTV :: Index -> Index -> Vname -> Type -> Preds -> Proof
lem_islcp_at_psubFTV j k a t_a PEmpty         = ()
lem_islcp_at_psubFTV j k a t_a (PCons p ps)   = () ? lem_islc_at_subFTV   j k a t_a p
                                                   ? lem_islcp_at_psubFTV j k a t_a ps

{-@ lem_islct_at_tsubFV :: j:Index -> k:Index -> x:Vname -> { v_x:Value | isLC v_x }
        -> { t:Type | isLCT_at j k t } -> { pf:_ | isLCT_at j k (tsubFV x v_x t) } / [tsize t] @-}
lem_islct_at_tsubFV :: Index -> Index -> Vname -> Expr -> Type -> Proof
lem_islct_at_tsubFV j k x v_x (TRefn   b  ps) = () ? lem_islcp_at_psubFV (j+1) k x v_x ps
lem_islct_at_tsubFV j k x v_x (TFunc   t_z t) = () ? lem_islct_at_tsubFV j     k x v_x t_z
                                                   ? lem_islct_at_tsubFV (j+1) k x v_x t
lem_islct_at_tsubFV j k x v_x (TExists t_z t) = () ? lem_islct_at_tsubFV j     k x v_x t_z
                                                   ? lem_islct_at_tsubFV (j+1) k x v_x t
lem_islct_at_tsubFV j k x v_x (TPoly   k'  t) = () ? lem_islct_at_tsubFV j (k+1) x v_x t

{-@ lem_islcp_at_strengthen :: { j:Index | j >=1 } -> k:Index -> { ps:Preds | isLCP_at j k ps }
        -> { ts:Preds | isLCP_at 1 0 ts } -> { pf:_ | isLCP_at j k (strengthen ps ts) } @-}
lem_islcp_at_strengthen :: Index -> Index -> Preds -> Preds -> Proof
lem_islcp_at_strengthen j k (PEmpty)     rs = () ? lem_islcp_at_weaken 1 0 j k    rs
lem_islcp_at_strengthen j k (PCons p ps) rs = () ? lem_islcp_at_strengthen j k ps rs

{-@ lem_islcp_at_push :: { j:Index | j >= 1 } -> k:Index -> { ps:Preds | isLCP_at j k ps } 
        -> { t_a:UserType | isLCT t_a } -> { pf:_ | isLCT_at (j-1) k (push ps t_a) } / [tsize t_a] @-}
lem_islcp_at_push :: Index -> Index -> Preds -> Type -> Proof
lem_islcp_at_push j k ps (TRefn  b ts) = () ? lem_islcp_at_strengthen j k ps ts
lem_islcp_at_push j k ps (TFunc t_x t) = () ? lem_islct_at_weaken 0 0 (j-1) k (TFunc t_x t)
lem_islcp_at_push j k ps (TPoly k' t)  = () ? lem_islct_at_weaken 0 0 (j-1) k (TPoly k' t)

{-@ lem_islct_at_tsubFTV :: j:Index -> k:Index -> a:Vname -> { t_a:UserType | isLCT t_a }
        -> { t:Type | isLCT_at j k t } -> { pf:_ | isLCT_at j k (tsubFTV a t_a t) } / [tsize t] @-}
lem_islct_at_tsubFTV :: Index -> Index -> Vname -> Type -> Type -> Proof
lem_islct_at_tsubFTV j k a t_a (TRefn   b  ps) = case b of
  (FTV a') | a == a' -> () ? lem_islcp_at_push    (j+1) k (psubFTV a t_a ps
                                                            ? lem_islcp_at_psubFTV (j+1) k a t_a ps) t_a
  _                  -> () ? lem_islcp_at_psubFTV (j+1) k a t_a ps
lem_islct_at_tsubFTV j k a t_a (TFunc   t_z t) = () ? lem_islct_at_tsubFTV j     k a t_a t_z
                                                    ? lem_islct_at_tsubFTV (j+1) k a t_a t
lem_islct_at_tsubFTV j k a t_a (TExists t_z t) = () ? lem_islct_at_tsubFTV j     k a t_a t_z
                                                    ? lem_islct_at_tsubFTV (j+1) k a t_a t
lem_islct_at_tsubFTV j k a t_a (TPoly   k'  t) = () ? lem_islct_at_tsubFTV j (k+1) a t_a t

---------------------------------------------------------------------------------
  -- | Behavior of isLC, isLC_at etc under unbind, open_at etc
---------------------------------------------------------------------------------

  -- Local Closure of Expressions

-- In particular, isLC (unbind y e) => isLC_at 1 0 e
{-@ lem_islc_at_after_open_at :: j:Index -> k:Index -> y:Vname
        -> { e:Expr | isLC_at j k (open_at j y e) } -> { pf:_ | isLC_at (j+1) k e } / [esize e] @-}
lem_islc_at_after_open_at :: Index -> Index -> Vname -> Expr -> Proof
lem_islc_at_after_open_at j k y (Bc _)         = ()
lem_islc_at_after_open_at j k y (Ic _)         = ()
lem_islc_at_after_open_at j k y (Prim _)       = ()
lem_islc_at_after_open_at j k y (FV _)         = ()
lem_islc_at_after_open_at j k y (BV i)
  | i == j     = ()
  | otherwise  = ()
lem_islc_at_after_open_at j k y (Lambda e)     = () ? lem_islc_at_after_open_at (j+1) k y e
lem_islc_at_after_open_at j k y (App e e')     = () ? lem_islc_at_after_open_at j k y e
                                                    ? lem_islc_at_after_open_at j k y e'
lem_islc_at_after_open_at j k y (LambdaT k' e) = () ? lem_islc_at_after_open_at j (k+1) y e
lem_islc_at_after_open_at j k y (AppT e t)     = () ? lem_islc_at_after_open_at j k y e
                                                    ? lem_islct_at_after_openT_at j k y t
lem_islc_at_after_open_at j k y (Let ex e)     = () ? lem_islc_at_after_open_at j k y ex
                                                    ? lem_islc_at_after_open_at (j+1) k y e
lem_islc_at_after_open_at j k y (Annot e t)    = () ? lem_islc_at_after_open_at j k y e 
                                                    ? lem_islct_at_after_openT_at j k y t

-- In particular, isLC (unbind_tv a e) => isLC_at 0 1 e
{-@ lem_islc_at_after_open_tv_at :: j:Index -> k:Index -> a:Vname
        -> { e:Expr | isLC_at j k (open_tv_at k a e) } -> { pf:_ | isLC_at j (k+1) e } / [esize e] @-}
lem_islc_at_after_open_tv_at :: Index -> Index -> Vname -> Expr -> Proof
lem_islc_at_after_open_tv_at j k a (Bc _)         = ()
lem_islc_at_after_open_tv_at j k a (Ic _)         = ()
lem_islc_at_after_open_tv_at j k a (Prim _)       = ()
lem_islc_at_after_open_tv_at j k a (FV _)         = ()
lem_islc_at_after_open_tv_at j k a (BV i)         = ()
lem_islc_at_after_open_tv_at j k a (Lambda e)     = () ? lem_islc_at_after_open_tv_at (j+1) k a e
lem_islc_at_after_open_tv_at j k a (App e e')     = () ? lem_islc_at_after_open_tv_at j k a e
                                                       ? lem_islc_at_after_open_tv_at j k a e'
lem_islc_at_after_open_tv_at j k a (LambdaT k' e) = () ? lem_islc_at_after_open_tv_at j (k+1) a e
lem_islc_at_after_open_tv_at j k a (AppT e t)     = () ? lem_islc_at_after_open_tv_at j k a e
                                                       ? lem_islct_at_after_open_tvT_at j k a t
lem_islc_at_after_open_tv_at j k a (Let ex e)     = () ? lem_islc_at_after_open_tv_at j k a ex
                                                       ? lem_islc_at_after_open_tv_at (j+1) k a e
lem_islc_at_after_open_tv_at j k a (Annot e t)    = () ? lem_islc_at_after_open_tv_at j k a e 
                                                       ? lem_islct_at_after_open_tvT_at j k a t

  -- Local Closure of Predicates

{-@ lem_islcp_at_after_openP_at :: j:Index -> k:Index -> y:Vname
        -> { ps:Preds | isLCP_at j k (openP_at j y ps) } -> { pf:_ | isLCP_at (j+1) k ps } 
         / [predsize ps] @-}
lem_islcp_at_after_openP_at :: Index -> Index -> Vname -> Preds -> Proof
lem_islcp_at_after_openP_at j k y PEmpty       = ()
lem_islcp_at_after_openP_at j k y (PCons p ps) = () ? lem_islc_at_after_open_at   j k y p
                                                    ? lem_islcp_at_after_openP_at j k y ps

{-@ lem_islcp_at_open_tvP_at :: j:Index -> k:Index -> a:Vname
        -> { ps:Preds | isLCP_at j k (open_tvP_at k a ps) } -> { pf:_ | isLCP_at j (k+1) ps } 
         / [predsize ps] @-}
lem_islcp_at_open_tvP_at :: Index -> Index -> Vname -> Preds -> Proof
lem_islcp_at_open_tvP_at j k a PEmpty       = ()
lem_islcp_at_open_tvP_at j k a (PCons p ps) = () ? lem_islc_at_after_open_tv_at   j k a p
                                                 ? lem_islcp_at_open_tvP_at j k a ps


{-@ lem_islct_at_after_openT_at :: j:Index -> k:Index -> y:Vname
        -> { t:Type | isLCT_at j k (openT_at j y t) } -> { pf:_ | isLCT_at (j+1) k t } 
         / [tsize t] @-}
lem_islct_at_after_openT_at :: Index -> Index -> Vname -> Type -> Proof
lem_islct_at_after_openT_at j k y (TRefn   b ps)  = case b of
  (BTV i) -> () ? lem_islcp_at_after_openP_at (j+1) k y ps
  _       -> () ? lem_islcp_at_after_openP_at (j+1) k y ps
lem_islct_at_after_openT_at j k y (TFunc   t_x t) = () ? lem_islct_at_after_openT_at j k y t_x
                                                       ? lem_islct_at_after_openT_at (j+1) k y t
lem_islct_at_after_openT_at j k y (TExists t_x t) = () ? lem_islct_at_after_openT_at j k y t_x
                                                       ? lem_islct_at_after_openT_at (j+1) k y t
lem_islct_at_after_openT_at j k y (TPoly   k'  t) = () ? lem_islct_at_after_openT_at j (k+1) y t

{-@ lem_islct_at_after_open_tvT_at :: j:Index -> k:Index -> a:Vname
        -> { t:Type | isLCT_at j k (open_tvT_at k a t) } -> { pf:_ | isLCT_at j (k+1) t } 
         / [tsize t] @-}
lem_islct_at_after_open_tvT_at :: Index -> Index -> Vname -> Type -> Proof
lem_islct_at_after_open_tvT_at j k a (TRefn   b ps)  = case b of
  (BTV i) | i == j    -> () ? lem_islcp_at_open_tvP_at (j+1) k a ps
          | otherwise -> () ? lem_islcp_at_open_tvP_at (j+1) k a ps
  _                   -> () ? lem_islcp_at_open_tvP_at (j+1) k a ps
lem_islct_at_after_open_tvT_at j k a (TFunc   t_x t) = () ? lem_islct_at_after_open_tvT_at j     k a t_x
                                                          ? lem_islct_at_after_open_tvT_at (j+1) k a t
lem_islct_at_after_open_tvT_at j k a (TExists t_x t) = () ? lem_islct_at_after_open_tvT_at j     k a t_x
                                                          ? lem_islct_at_after_open_tvT_at (j+1) k a t
lem_islct_at_after_open_tvT_at j k a (TPoly   k'  t) = () ? lem_islct_at_after_open_tvT_at j (k+1) a t

  -- | System F Version
{-@ lem_islcft_at_after_openFT_at :: j:Index -> a:Vname
        -> { t:FType | isLCFT_at j (openFT_at j a t) } -> { pf:_ | isLCFT_at (j+1) t } / [ftsize t] @-}
lem_islcft_at_after_openFT_at :: Index -> Vname -> FType -> Proof
lem_islcft_at_after_openFT_at j a (FTBasic   b)  = case b of
  (BTV i) | i == j    -> () 
  _                   -> () 
lem_islcft_at_after_openFT_at j a (FTFunc t_x t) = () ? lem_islcft_at_after_openFT_at j     a t_x
                                                      ? lem_islcft_at_after_openFT_at j     a t
lem_islcft_at_after_openFT_at j a (FTPoly k'  t) = () ? lem_islcft_at_after_openFT_at (j+1) a t

{-
{-@ lem_erase_freeBV :: t:Type -> { pf:_ | Set_sub (ffreeBV (erase t)) (tfreeBTV t) } @-}
lem_erase_freeBV :: Type -> Proof
lem_erase_freeBV (TRefn   b   z p) = ()
lem_erase_freeBV (TFunc   z t_z t) = () ? lem_erase_freeBV t_z
                                        ? lem_erase_freeBV t
lem_erase_freeBV (TExists z t_z t) = () ? lem_erase_freeBV t
lem_erase_freeBV (TPoly   a' k' t) = () ? lem_erase_freeBV t
-}
