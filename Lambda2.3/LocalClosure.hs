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
----- | JUDGMENTS : Local Closure of Locally Nameless Terms
--------------------------------------------------------------------------------
{-
data LCExpr where
    LCBC   :: Bool  -> LCExpr
    LCIC   :: Int   -> LCExpr
    LCVar  :: Vname -> LCExpr
    LCPrm  :: Prim  -> LCExpr
    LCAbs  :: Expr  -> Names  -> (Vname -> LCExpr) -> LCExpr
    LCApp  :: Expr  -> LCExpr -> Expr -> LCExpr -> LCExpr
    LCAbsT :: Kind  -> Expr   -> Names -> (Vname -> LCExpr) -> LCExpr
    LCAppT :: Expr  -> LCExpr -> Type -> LCType -> LCExpr
    LCLet  :: Expr  -> LCExpr -> Expr -> Names -> (Vname -> LCExpr) -> LCExpr
    LCAnn  :: Expr  -> LCExpr -> Type -> LCType -> LCExpr

{-@ data LCExpr where 
        LCBC   :: b:Bool  -> ProofOf(LCExpr (Bc b))
        LCIC   :: n:Int   -> ProofOf(LCExpr (Ic n))
        LCVar  :: x:Vname -> ProofOf(LCExpr (FV x))
        LCPrm  :: c:Prim  -> ProofOf(LCExpr (Prim c))
        LCAbs  :: e:Expr  -> nms:Names 
                    -> ( { y:Vname | NotElem y nms } -> ProofOf(LCExpr (unbind y e)) )
                    -> ProofOf(LCExpr (Lambda e))
        LCApp  :: e:Expr  -> ProofOf(LCExpr e) -> e':Expr -> ProofOf(LCExpr e') 
                    -> ProofOf(LCExpr (App e e'))
        LCAbsT :: k:Kind  -> e:Expr -> nms:Names 
                    -> ( { a:Vname | NotElem a nms } -> ProofOf(LCExpr (unbind_tv a e)) )
                    -> ProofOf(LCExpr (LambdaT k e))
        LCAppT :: e:Expr  -> ProofOf(LCExpr e) -> t:UserType -> ProofOf(LCType t)
                    -> ProofOf(LCExpr (AppT e t))
        LCLet  :: e_x:Expr -> ProofOf(LCExpr e_x) -> e:Expr -> nms:Names
                    -> ( { y:Vname | NotElem y nms } -> ProofOf(LCExpr (unbind y e)) )
                    -> ProofOf(LCExpr (Let e_x e))
        LCAnn  :: e:Expr  -> ProofOf(LCExpr e) -> t:Type -> ProofOf(LCType t)
                    -> ProofOf(LCExpr (Annot e t)) @-}

data LCPreds where
    LCPEmp  :: LCPreds
    LCPCons :: Expr -> LCExpr -> Preds -> LCPreds -> LCPreds

{-@ data LCPreds where
        LCPEmp  :: ProofOf(LCPreds PEmpty)
        LCPCons :: p:Expr -> ProofOf(LCExpr p) -> ps:Preds -> ProofOf(LCPreds ps)
                    -> ProofOf(LCPreds (PCons p ps)) @-}

data LCType where 
    LCRefn :: Basic -> Preds -> Names -> (Vname -> LCPreds) -> LCType
    LCFunc :: Type  -> LCType -> Type -> Names -> (Vname -> LCType) -> LCType
    LCExis :: Type  -> LCType -> Type -> Names -> (Vname -> LCType) -> LCType
    LCPoly :: Kind  -> Type  -> Names -> (Vname -> LCType) -> LCType

{-@ data LCType where
        LCRefn :: { b:Basic | not (isBTV b) } -> ps:Preds -> nms:Names
                    -> ( { y:Vname | NotElem y nms } -> ProofOf(LCPreds (unbindP y ps)) )
                    -> ProofOf(LCType (TRefn b ps))
        LCFunc :: t_x:Type -> ProofOf(LCType t_x) -> t:Type -> nms:Names
                    -> ( { y:Vname | NotElem y nms } -> ProofOf(LCType (unbindT y t)) )
                    -> ProofOf(LCType (TFunc t_x t))
        LCExis :: t_x:Type -> ProofOf(LCType t_x) -> t:Type -> nms:Names
                    -> ( { y:Vname | NotElem y nms } -> ProofOf(LCType (unbindT y t)) )
                    -> ProofOf(LCType (TExists t_x t))
        LCPoly :: k:Kind -> t:Type -> nms:Names
                    -> ( { a:Vname | NotElem a nms } -> ProofOf(LCType (unbind_tvT a t)) )
                    -> ProofOf(LCType (TPoly k t)) @-}

data EBody where
    EBOpen :: Expr -> Names -> (Vname -> LCExpr) -> EBody

{-@ data EBody where
        EBOpen :: e:Expr -> nms:Names 
                         -> ({ x:Vname | NotElem x nms } -> ProofOf(LCExpr (unbind x e)) )
                         -> ProofOf(EBody e) @-}

data EBodyTV where
    EBOpenTV :: Expr -> Names -> (Vname -> LCExpr) -> EBodyTV

{-@ data EBodyTV where
        EBOpenTV :: e:Expr -> nms:Names 
                           -> ({ a:Vname | NotElem a nms } -> ProofOf(LCExpr (unbind_tv a e)) ) 
                           -> ProofOf(EBodyTV e) @-}
 
data PBody where
    PBOpen :: Preds -> Names -> (Vname -> LCPreds) -> PBody

{-@ data PBody where
        PBOpen :: ps:Preds -> nms:Names 
                           -> ({ x:Vname | NotElem x nms } -> ProofOf(LCPreds (unbindP x ps)) )
                           -> ProofOf(PBody ps) @-}

data TBody where
    TBOpen :: Type -> Names -> (Vname -> LCType) -> TBody

{-@ data TBody where
        TBOpen :: t:Type -> nms:Names 
                         -> ({ x:Vname | NotElem x nms } -> ProofOf(LCType (unbindT x t)) )
                         -> ProofOf(TBody t) @-}

data TBodyTV where
    TBOpenTV :: Type -> Names -> (Vname -> LCType) -> TBodyTV

{-@ data TBodyTV where
        TBOpenTV :: t:Type -> nms:Names 
                           -> ({ a:Vname | NotElem a nms } -> ProofOf(LCType (unbind_tvT a t)) )
                           -> ProofOf(TBodyTV t) @-}
-}
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
{-@ lem_islc_at_open_at :: j:Index -> k:Index -> y:Vname
        -> { e:Expr | isLC_at j k (open_at j y e) } -> { pf:_ | isLC_at (j+1) k e } / [esize e] @-}
lem_islc_at_open_at :: Index -> Vname -> Vname -> Expr -> Proof
lem_islc_at_open_at j k y (Bc _)         = ()
lem_islc_at_open_at j k y (Ic _)         = ()
lem_islc_at_open_at j k y (Prim _)       = ()
lem_islc_at_open_at j k y (FV _)         = ()
lem_islc_at_open_at j k y (BV i)
  | i == j     = ()
  | otherwise  = ()
lem_islc_at_open_at j k y (Lambda e)     = () ? lem_islc_at_open_at (j+1) k y e
lem_islc_at_open_at j k y (App e e')     = () ? lem_islc_at_open_at j k y e
                                              ? lem_islc_at_open_at j k y e'
lem_islc_at_open_at j k y (LambdaT k' e) = () ? lem_islc_at_open_at j (k+1) y e
lem_islc_at_open_at j k y (AppT e t)     = () ? lem_islc_at_open_at j k y e
                                              ? lem_islct_at_openT_at j k y t
lem_islc_at_open_at j k y (Let ex e)     = () ? lem_islc_at_open_at j k y ex
                                              ? lem_islc_at_open_at (j+1) k y e
lem_islc_at_open_at j k y (Annot e t)    = () ? lem_islc_at_open_at j k y e 
                                              ? lem_islct_at_openT_at j k y t

-- In particular, isLC (unbind_tv a e) => isLC_at 0 1 e
{-@ lem_islc_at_open_tv_at :: j:Index -> k:Index -> a:Vname
        -> { e:Expr | isLC_at j k (open_tv_at k a e) } -> { pf:_ | isLC_at j (k+1) e } / [esize e] @-}
lem_islc_at_open_tv_at :: Index -> Vname -> Vname -> Expr -> Proof
lem_islc_at_open_tv_at j k a (Bc _)         = ()
lem_islc_at_open_tv_at j k a (Ic _)         = ()
lem_islc_at_open_tv_at j k a (Prim _)       = ()
lem_islc_at_open_tv_at j k a (FV _)         = ()
lem_islc_at_open_tv_at j k a (BV i)         = ()
lem_islc_at_open_tv_at j k a (Lambda e)     = () ? lem_islc_at_open_tv_at (j+1) k a e
lem_islc_at_open_tv_at j k a (App e e')     = () ? lem_islc_at_open_tv_at j k a e
                                                 ? lem_islc_at_open_tv_at j k a e'
lem_islc_at_open_tv_at j k a (LambdaT k' e) = () ? lem_islc_at_open_tv_at j (k+1) a e
lem_islc_at_open_tv_at j k a (AppT e t)     = () ? lem_islc_at_open_tv_at j k a e
                                                 ? lem_islct_at_open_tvT_at j k a t
lem_islc_at_open_tv_at j k a (Let ex e)     = () ? lem_islc_at_open_tv_at j k a ex
                                                 ? lem_islc_at_open_tv_at (j+1) k a e
lem_islc_at_open_tv_at j k a (Annot e t)    = () ? lem_islc_at_open_tv_at j k a e 
                                                 ? lem_islct_at_open_tvT_at j k a t

  -- Local Closure of Predicates

{-@ lem_islcp_at_openP_at :: j:Index -> k:Index -> y:Vname
        -> { ps:Preds | isLCP_at j k (openP_at j y ps) } -> { pf:_ | isLCP_at (j+1) k ps } 
         / [predsize ps] @-}
lem_islcp_at_openP_at :: Index -> Vname -> Vname -> Preds -> Proof
lem_islcp_at_openP_at j k y PEmpty       = ()
lem_islcp_at_openP_at j k y (PCons p ps) = () ? lem_islc_at_open_at   j k y p
                                              ? lem_islcp_at_openP_at j k y ps

{-@ lem_islcp_at_open_tvP_at :: j:Index -> k:Index -> a:Vname
        -> { ps:Preds | isLCP_at j k (open_tvP_at k a ps) } -> { pf:_ | isLCP_at j (k+1) ps } 
         / [predsize ps] @-}
lem_islcp_at_open_tvP_at :: Index -> Vname -> Vname -> Preds -> Proof
lem_islcp_at_open_tvP_at j k a PEmpty       = ()
lem_islcp_at_open_tvP_at j k a (PCons p ps) = () ? lem_islc_at_open_tv_at   j k a p
                                                 ? lem_islcp_at_open_tvP_at j k a ps


{-@ lem_islct_at_openT_at :: j:Index -> k:Index -> y:Vname
        -> { t:Type | isLCT_at j k (openT_at j y t) } -> { pf:_ | isLCT_at (j+1) k t } 
         / [tsize t] @-}
lem_islct_at_openT_at :: Index -> Vname -> Vname -> Type -> Proof
lem_islct_at_openT_at j k y (TRefn   b ps)  = case b of
  (BTV i) -> () ? lem_islcp_at_openP_at (j+1) k y ps
  _       -> () ? lem_islcp_at_openP_at (j+1) k y ps
lem_islct_at_openT_at j k y (TFunc   t_x t) = () ? lem_islct_at_openT_at j k y t_x
                                                 ? lem_islct_at_openT_at (j+1) k y t
lem_islct_at_openT_at j k y (TExists t_x t) = () ? lem_islct_at_openT_at j k y t_x
                                                 ? lem_islct_at_openT_at (j+1) k y t
lem_islct_at_openT_at j k y (TPoly   k'  t) = () ? lem_islct_at_openT_at j (k+1) y t

{-@ lem_islct_at_open_tvT_at :: j:Index -> k:Index -> a:Vname
        -> { t:Type | isLCT_at j k (open_tvT_at k a t) } -> { pf:_ | isLCT_at j (k+1) t } 
         / [tsize t] @-}
lem_islct_at_open_tvT_at :: Index -> Vname -> Vname -> Type -> Proof
lem_islct_at_open_tvT_at j k a (TRefn   b ps)  = case b of
  (BTV i) | i == j    -> () ? lem_islcp_at_open_tvP_at (j+1) k a ps
          | otherwise -> () ? lem_islcp_at_open_tvP_at (j+1) k a ps
  _                   -> () ? lem_islcp_at_open_tvP_at (j+1) k a ps
lem_islct_at_open_tvT_at j k a (TFunc   t_x t) = () ? lem_islct_at_open_tvT_at j     k a t_x
                                                    ? lem_islct_at_open_tvT_at (j+1) k a t
lem_islct_at_open_tvT_at j k a (TExists t_x t) = () ? lem_islct_at_open_tvT_at j     k a t_x
                                                    ? lem_islct_at_open_tvT_at (j+1) k a t
lem_islct_at_open_tvT_at j k a (TPoly   k'  t) = () ? lem_islct_at_open_tvT_at j (k+1) a t

{-  Facts about unbindFT and openFT_at:
--                                       ffreeBV t' == Set_dif (ffreeBV t) (Set_sng a) &&

{-@ lem_erase_freeBV :: t:Type -> { pf:_ | Set_sub (ffreeBV (erase t)) (tfreeBTV t) } @-}
lem_erase_freeBV :: Type -> Proof
lem_erase_freeBV (TRefn   b   z p) = ()
lem_erase_freeBV (TFunc   z t_z t) = () ? lem_erase_freeBV t_z
                                        ? lem_erase_freeBV t
lem_erase_freeBV (TExists z t_z t) = () ? lem_erase_freeBV t
lem_erase_freeBV (TPoly   a' k' t) = () ? lem_erase_freeBV t
-}
