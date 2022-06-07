{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Typing where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import LocalClosure
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Typing Relation and the Subtyping Relation
-----------------------------------------------------------------------------

{-@ reflect eqlPred @-}               -- new definition avoids dealing with ps inside eqlPred
{-@ eqlPred :: { t:Type | isTRefn t } -> e:Expr   
        -> { p':Expr | self t e Base == push (PCons p' PEmpty) t &&
                                fv  p' ==                   (fv  e) } @-}
eqlPred :: Type -> Expr -> Expr
eqlPred (TRefn b ps) e = App (App (AppT (Prim Eql) (TRefn b PEmpty)) (BV 0)) e

{-@ lem_eqlPred_islc_at :: { b:Basic | isLCT_at 1 0 (TRefn b PEmpty) } 
        -> ps:Preds -> { e:Expr | isLC e }
        -> { pf:_ | isLC_at 1 0 (eqlPred (TRefn b ps) e) } @-}
lem_eqlPred_islc_at :: Basic -> Preds -> Expr -> Proof
lem_eqlPred_islc_at b ps e = () ? lem_islc_at_weaken 0 0 1 0 e

{-@ reflect self @-} 
{-@ self :: t:Type -> e:Expr -> k:Kind
              -> { t':Type | Set_sub (free t') (Set_cup (free t) (fv e)) &&
                             (isTRefn t => isTRefn t') && (noExists t => noExists t' ) &&
                             tdepth t == tdepth t' &&
                             erase t == erase t' && ( (k == Star) => (t == t') ) } @-}
self :: Type -> Expr -> Kind -> Type
self t@(TRefn b ps)   e Base = TRefn b (PCons  (eqlPred (TRefn b ps) e)  ps)
self (TFunc    t_z t) e Base = TFunc   t_z t
self (TExists  t_z t) e Base = TExists t_z (self t e Base)
self (TPoly    k_a t) e Base = TPoly   k_a t
self t                e Star = t

{-@ lem_self_islct :: { t:Type | isLCT t } -> { e:Expr | isLC e } -> k:Kind
                          -> { pf:_ | isLCT (self t e k) } @-}
lem_self_islct :: Type -> Expr -> Kind -> Proof
lem_self_islct t e k = lem_self_islct_at 0 t e k

{-@ lem_self_islct_at :: j:Index -> { t:Type | isLCT_at j 0 t } -> { e:Expr | isLC e } 
                          -> k:Kind -> { pf:_ | isLCT_at j 0 (self t e k) } @-}
lem_self_islct_at :: Index -> Type -> Expr -> Kind -> Proof
lem_self_islct_at j t@(TRefn b ps)   e Base = case b of
  (BTV i) -> impossible ""
  _       -> () ? lem_eqlPred_islc_at b ps e
                ? lem_islc_at_weaken 0 0 (j+1) 0 e
                ? lem_islc_at_weaken 1 0 (j+1) 0 (eqlPred (TRefn b ps) e)
lem_self_islct_at j (TFunc    t_z t) e Base = ()
lem_self_islct_at j (TExists  t_z t) e Base = lem_self_islct_at (j+1) t e Base
lem_self_islct_at j (TPoly    k_a t) e Base = ()
lem_self_islct_at j t                e Star = ()

{-@ lem_unbindT_self :: y:Vname -> t:Type -> { e:Expr | isLC e } -> k:Kind
        -> { pf:_ | unbindT y (self t e k) == self (unbindT y t) e k } @-}
lem_unbindT_self :: Vname -> Type -> Expr -> Kind -> Proof
lem_unbindT_self y t e k = lem_openT_at_self 0 y t e k

{-@ lem_openT_at_self :: j:Index -> y:Vname -> t:Type -> { e:Expr | isLC e } -> k:Kind
        -> { pf:_ | openT_at j y (self t e k) == self (openT_at j y t) e k } @-}
lem_openT_at_self :: Index -> Vname -> Type -> Expr -> Kind -> Proof
lem_openT_at_self j y (TRefn b ps)    e Base = lem_open_at_lc_at (j+1) y 0 0 e
lem_openT_at_self j y (TFunc t_x t)   e Base = ()
lem_openT_at_self j y (TExists t_x t) e Base = lem_openT_at_self (j+1) y t e Base
lem_openT_at_self j y (TPoly k_a t)   e Base = ()
lem_openT_at_self j y t               e Star = ()

{-@ lem_open_at_eqlPred :: y:Vname -> b:Basic -> ps:Preds 
        -> { e:Expr | isLC e } -> { pf:_ | open_at 0 y (eqlPred (TRefn b ps) e) 
                   == App (App (AppT (Prim Eql) (TRefn b PEmpty)) (FV y)) e } @-}
lem_open_at_eqlPred ::  Vname -> Basic -> Preds -> Expr -> Proof
lem_open_at_eqlPred y b ps e = () ? lem_open_at_lc_at 0 y 0 0 e
                                  ? toProof (unbind y (Prim Eql) === Prim Eql)
                                  ? toProof (unbind y (BV 0) === FV y) 

{-@ lem_tsubFTV_eqlPred :: a:Vname -> t_a:UserType -> { b:Basic | not (b == FTV a) } 
        -> ps:Preds  -> { e:Expr | not (Set_mem a (ftv e)) }
        -> { pf:_ | subFTV a t_a (eqlPred (TRefn b ps) e) == eqlPred (TRefn b ps) e } @-}
lem_tsubFTV_eqlPred :: Vname -> Type -> Basic -> Preds -> Expr -> Proof
lem_tsubFTV_eqlPred a t_a b ps e 
  = () ? lem_psubFTV_notin a t_a PEmpty
       ? lem_subFTV_notin  a t_a e

{-@ lem_tsubFV_self :: z:Vname -> v_z:Expr -> t:Type -> e:Expr -> k:Kind
        -> { pf:_ | tsubFV z v_z (self t e k) == self (tsubFV z v_z t) (subFV z v_z e) k } @-}
lem_tsubFV_self :: Vname -> Expr -> Type -> Expr -> Kind -> Proof
lem_tsubFV_self z v_z (TRefn b ps)     e Base = case b of
  TBool   -> () 
  TInt    -> () 
  (FTV a) -> ()
  (BTV a) -> ()
lem_tsubFV_self z v_z (TFunc    t_y t) e Base = ()
lem_tsubFV_self z v_z (TExists  t_y t) e Base = () ? lem_tsubFV_self z v_z t e Base
lem_tsubFV_self z v_z (TPoly    k_a t) e Base = ()
lem_tsubFV_self z v_z t                e Star = ()

{-@ lem_tsubFV_self2 :: z:Vname -> v:Value -> t:Type -> { x:Vname | x != z } -> k:Kind
        -> { pf:_ | tsubFV z v (self t (FV x) k) == self (tsubFV z v t) (FV x) k } @-}
lem_tsubFV_self2 :: Vname -> Expr -> Type -> Vname -> Kind -> Proof
lem_tsubFV_self2 z v (TRefn b  ps)   x Base = case b of
  TBool   -> ()
  TInt    -> ()
  (FTV a) -> ()
  (BTV a) -> ()
lem_tsubFV_self2 z v (TFunc   t_y t) x Base = ()
lem_tsubFV_self2 z v (TExists t_y t) x Base = () ? lem_tsubFV_self2 z v t x Base
lem_tsubFV_self2 z v (TPoly   k_a t) x Base = ()
lem_tsubFV_self2 z v t               x Star = ()

{-@ lem_tsubBV_self :: v_z:Value -> t:Type  -> { e:Expr | isLC e } -> k:Kind
        -> { pf:_ | tsubBV v_z (self t e k) == self (tsubBV v_z t) e k } @-}
lem_tsubBV_self :: Expr -> Type -> Expr -> Kind -> Proof
lem_tsubBV_self v_z t e k = lem_tsubBV_at_self 0 v_z t e k

{-@ lem_tsubBV_at_self :: j:Index -> v_z:Value -> t:Type -> { e:Expr | isLC e } -> k:Kind
        -> { pf:_ | tsubBV_at j v_z (self t e k) == self (tsubBV_at j v_z t) e k } @-}
lem_tsubBV_at_self :: Index -> Expr -> Type -> Expr -> Kind -> Proof
lem_tsubBV_at_self j v_z (TRefn b ps)     e Base 
              = lem_subBV_at_lc_at (j+1) v_z 0 0 e
lem_tsubBV_at_self j v_z (TFunc t_x t)   e Base = ()
lem_tsubBV_at_self j v_z (TExists t_x t) e Base 
              = lem_tsubBV_at_self (j+1) v_z t e Base
lem_tsubBV_at_self j v_z (TPoly k_a t)   e Base = ()
lem_tsubBV_at_self j v_z t               e Star = ()


  --- | the Typing Judgement  --  Due to cofinite quantification, we need to explicity annotate
  ---                               the judgment size in order to define a termination metric.
 
data HasType where            
    TBC   :: {-Int ->-} Env -> Bool -> HasType
    TIC   :: {-Int ->-} Env -> Int -> HasType
    TVar1 :: {-Int ->-} Env -> Vname -> Type -> Kind -> WFType -> HasType
    TVar2 :: Int -> Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TVar3 :: Int -> Env -> Vname -> Type -> HasType -> Vname -> Kind -> HasType
    TPrm  :: {-Int ->-} Env -> Prim -> HasType
    TAbs  :: Int -> Env -> Type -> Kind -> WFType -> Expr -> Type -> Names
                 -> (Vname -> HasType) -> HasType
    TApp  :: Int -> Env -> Expr -> Type -> Type -> HasType 
                 -> Expr -> HasType -> HasType
    TAbsT :: Int -> Env -> Kind -> Expr -> Type -> Names -> (Vname -> HasType) -> HasType
    TAppT :: Int -> Env -> Expr -> Kind -> Type -> HasType -> Type -> WFType -> HasType
    TLet  :: Int -> Env -> Expr -> Type -> HasType -> Expr -> Type -> Kind -> WFType 
                 -> Names -> (Vname -> HasType) -> HasType
    TAnn  :: Int -> Env -> Expr -> Type -> HasType -> HasType
    TSub  :: Int -> Env -> Expr -> Type -> HasType -> Type -> Kind -> WFType -> Subtype -> HasType

{-@ data HasType where
        TBC   :: g:Env -> b:Bool -> { pf:HasType | propOf pf == HasType g (Bc b) (tybc b) &&
                                                   sizeOf pf == 1 }
        TIC   :: g:Env -> m:Int  -> { pf:HasType | propOf pf == HasType g (Ic m) (tyic m) &&
                                                   sizeOf pf == 1 }
        TVar1 :: g:Env -> { x:Vname | not (in_env x g) } 
                    -> t:Type -> k:Kind -> ProofOf(WFType g t k) 
                    -> { pf:HasType | propOf pf == HasType (Cons x t g) (FV x) (self t (FV x) k) &&
                                      sizeOf pf == tdepth t }
        TVar2 :: n:Nat -> g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOfN n (HasType g (FV x) t)
                    -> { y:Vname | y != x && not (in_env y g) } -> s:Type
                    -> { pf:HasType | propOf pf == HasType (Cons y s g) (FV x) t &&
                                      sizeOf pf == n + 1 }
        TVar3 :: n:Nat -> g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOfN n (HasType g (FV x) t)
                    -> { a:Vname | a != x && not (in_env a g) } -> k:Kind
                    -> { pf:HasType | propOf pf == HasType (ConsT a k g) (FV x) t &&
                                      sizeOf pf == n + 1 }
        TPrm  :: g:Env -> c:Prim -> { pf:HasType | propOf pf == HasType g (Prim c) (ty c) &&
                                                   sizeOf pf == tdepth (ty c) }
        TAbs  :: n:Nat -> g:Env -> t_x:Type -> k_x:Kind -> ProofOf(WFType g t_x k_x)
                  -> e:Expr -> t:Type -> nms:Names
                  -> ( { y:Vname | NotElem y nms } 
                           -> ProofOfN n (HasType (Cons y t_x g) (unbind y e) (unbindT y t)) )
                  -> { pf:HasType | propOf pf == HasType g (Lambda e) (TFunc t_x t) &&
                                    sizeOf pf == max n (tdepth t_x) + 1 }
        TApp  :: n:Nat -> g:Env -> e:Expr -> t_x:Type -> t:Type
                  -> ProofOfN n (HasType g e (TFunc t_x t)) 
                  -> e':Expr -> ProofOfN n (HasType g e' t_x) 
                  -> { pf:HasType | propOf pf == HasType g (App e e') (TExists t_x t) &&
                                    sizeOf pf == n + 1 } 
        TAbsT :: n:Nat -> g:Env -> k:Kind -> e:Expr -> t:Type -> nms:Names
                  -> ({ a':Vname | NotElem a' nms }
                           -> ProofOfN n (HasType (ConsT a' k g) (unbind_tv a' e) (unbind_tvT a' t)) )
                  -> { pf:HasType | propOf pf == HasType g (LambdaT k e) (TPoly k t) &&
                                    sizeOf pf == n + 1 }
        TAppT :: n:Nat -> g:Env -> e:Expr -> k:Kind -> s:Type -> ProofOfN n (HasType g e (TPoly k s))
                  -> t:UserType -> ProofOf(WFType g t k)
                  -> { pf:HasType | propOf pf == HasType g (AppT e t) (tsubBTV t s) &&
                                    sizeOf pf == max n (tdepth (tsubBTV t s)) + 1 }
        TLet  :: n:Nat -> g:Env -> e_x:Expr -> t_x:Type -> ProofOfN n (HasType g e_x t_x)
                  -> e:Expr -> t:Type -> k:Kind -> ProofOf(WFType g t k) -> nms:Names
                  -> ({ y:Vname | NotElem y nms }
                          -> ProofOfN n (HasType (Cons y t_x g) (unbind y e) (unbindT y t)) )
                  -> { pf:HasType | propOf pf == HasType g (Let e_x e) t &&
                                    sizeOf pf == n + 1 }
        TAnn  :: n:Nat -> g:Env -> e:Expr -> t:UserType -> ProofOfN n (HasType g e t)
                  -> { pf:HasType | propOf pf == HasType g (Annot e t) t &&
                                    sizeOf pf == n + 1 }
        TSub  :: n:Nat -> g:Env -> e:Expr -> s:Type -> ProofOfN n (HasType g e s) -> t:Type -> k:Kind
                  -> ProofOf(WFType g t k) -> ProofOfN n (Subtype g s t) 
                  -> { pf:HasType | propOf pf == HasType g e t && sizeOf pf == n + 1 } @-} 

{-@ measure typSize @-}
{-@ typSize :: pf:HasType -> { v:Int | v == sizeOf pf && v >= 1 } @-}
typSize :: HasType -> Int
typSize (TBC _ _)                               = 1
typSize (TIC _ _)                               = 1
typSize (TVar1 _ _ t _ _)                       = tdepth t
typSize (TVar2 n _ _ _ p_x_b _ _)               = n   + 1
typSize (TVar3 n _ _ _ p_x_b _ _)               = n   + 1
typSize (TPrm _ c)                              = tdepth (ty c)
typSize (TAbs n _ t_x _ _ _ _ _ p_e_b')         = max n (tdepth t_x) + 1
typSize (TApp n _ _ _ _ p_e_bb' _ p_e'_b)       = n   + 1
typSize (TAbsT n _ _ _ _ _ p_e_t)               = n   + 1
typSize (TAppT n _ _ _ s p_e_as t _)            = max n (tdepth (tsubBTV t s)) + 1 --n+(tdepth t)+1
typSize (TLet n _ _ p_ex_b _ _ _ _ _ _ p_e_b')  = n   + 1
typSize (TAnn n _ _ _ p_e_b)                    = n   + 1
typSize (TSub n _ _ _ p_e_s _ _ _ p_s_t)        = n   + 1

{-@ lem_typSize_lb :: g:Env -> e:Expr -> t:Type 
        -> { p_e_t:HasType | propOf p_e_t == HasType g e t }
        -> { pf:_ | sizeOf p_e_t >= tdepth t } / [sizeOf p_e_t] @-}
lem_typSize_lb :: Env -> Expr -> Type -> HasType -> Proof
lem_typSize_lb g e t (TBC {})                     = ()
lem_typSize_lb g e t (TIC {})                     = ()
lem_typSize_lb g e t (TVar1 _ x t' k _)            
    = () ? toProof ( tdepth (self t' (FV x) k) === tdepth t' )
lem_typSize_lb g e t (TVar2 n g' _ _ p_x_b _ _)   = lem_typSize_lb g' e t p_x_b
lem_typSize_lb g e t (TVar3 n g' _ _ p_x_b _ _)   = lem_typSize_lb g' e t p_x_b
lem_typSize_lb g e t (TPrm {})                    = ()
lem_typSize_lb g e t (TAbs _ _ t_x _ _ e' t' nms mk_p_e'_txt')
    = lem_typSize_lb (Cons y t_x g) (unbind y e') (unbindT y t') (mk_p_e'_txt' y)
        where
          y = fresh_var nms g
lem_typSize_lb g e t (TApp _ _ e1 t_x t' p_e1_txt' _ _)
    = lem_typSize_lb g e1 (TFunc t_x t') p_e1_txt'
    ? toProof (tdepth (TExists t_x t') === tdepth (TFunc t_x t') )
lem_typSize_lb g e t (TAbsT _ _ k e' t' nms mk_p_e'_t')
    = lem_typSize_lb (ConsT a k g) (unbind_tv a e') (unbind_tvT a t') (mk_p_e'_t' a)
        where
          a = fresh_var nms g
lem_typSize_lb g e t (TAppT _ _ e' k s p_e_ks t' _)
    = lem_typSize_lb g e' (TPoly k s) p_e_ks
lem_typSize_lb g e t (TLet _ _ _ t_x _ e' t' _ _ nms mk_p_e'_t')
    = lem_typSize_lb (Cons y t_x g) (unbind y e') (unbindT y t') (mk_p_e'_t' y)
        where
          y = fresh_var nms g
lem_typSize_lb g e t (TAnn _ _ e' _ p_e'_t)       = lem_typSize_lb g e' t p_e'_t
lem_typSize_lb g e t (TSub _ _ _ s p_e_s _ _ _ p_s_t) 
    = lem_subtypSize_lb g s t p_s_t


{-@ reflect isTBC @-}
isTBC :: HasType -> Bool
isTBC (TBC {}) = True
isTBC _        = False

{-@ reflect isTIC @-}
isTIC :: HasType -> Bool
isTIC (TIC {}) = True
isTIC _        = False

{-@ reflect isTVar @-}
isTVar :: HasType -> Bool
isTVar (TVar1 {}) = True
isTVar (TVar2 {}) = True
isTVar (TVar3 {}) = True
isTVar _          = False

{-@ reflect isTVar1 @-}
isTVar1 :: HasType -> Bool
isTVar1 (TVar1 {}) = True
isTVar1 _          = False

{-@ reflect isTVar2 @-}
isTVar2 :: HasType -> Bool
isTVar2 (TVar2 {}) = True
isTVar2 _          = False

{-@ reflect isTVar3 @-}
isTVar3 :: HasType -> Bool
isTVar3 (TVar3 {}) = True
isTVar3 _          = False

{-@ reflect isTAbs @-}
isTAbs :: HasType -> Bool
isTAbs (TAbs {}) = True
isTAbs _         = False

{-@ reflect isTApp @-}
isTApp :: HasType -> Bool
isTApp (TApp {}) = True
isTApp _         = False

{-@ reflect isTAbsT @-}
isTAbsT :: HasType -> Bool
isTAbsT (TAbsT {}) = True
isTAbsT _          = False

{-@ reflect isTAppT @-}
isTAppT :: HasType -> Bool
isTAppT (TAppT {}) = True
isTAppT _          = False

{-@ reflect isTLet @-}
isTLet :: HasType -> Bool
isTLet (TLet {}) = True
isTLet _         = False

{-@ reflect isTAnn @-}
isTAnn :: HasType -> Bool
isTAnn (TAnn {}) = True
isTAnn _         = False

{-@ reflect isTSub @-}
isTSub :: HasType -> Bool
isTSub (TSub {}) = True
isTSub _         = False

------------------------------------------------------------------------------
----- | SUBTYPING
------------------------------------------------------------------------------

data Subtype where
    SBase :: Env -> Basic -> Preds -> Preds -> Names -> (Vname -> Implies) -> Subtype
    SFunc :: Int -> Env -> Type -> Type -> Subtype -> Type -> Type -> Names 
               -> (Vname -> Subtype) -> Subtype
    SWitn :: Int -> Env -> Expr -> Type -> HasType -> Type -> Type -> Subtype  -> Subtype
    SBind :: Int -> Env -> Type -> Type -> Type -> Names -> (Vname -> Subtype) -> Subtype
    SPoly :: Int -> Env -> Kind -> Type -> Type -> Names -> (Vname -> Subtype) -> Subtype

{-@ data Subtype where
        SBase :: g:Env -> b:Basic -> p1:Preds -> p2:Preds -> nms:Names
                   -> ({ y:Vname | NotElem y nms} 
                           -> ProofOf(Implies (Cons y (TRefn b PEmpty) g) 
                                              (unbindP y p1) (unbindP y p2)) )
                   -> { pf:Subtype | propOf pf == Subtype g (TRefn b p1) (TRefn b p2) &&
                                     sizeOf pf == 1 }
        SFunc :: n:Nat -> g:Env -> s1:Type -> s2:Type -> ProofOfN n (Subtype g s2 s1) 
                   -> t1:Type -> t2:Type -> nms:Names
                   -> ({ y:Vname | NotElem y nms} 
                          -> ProofOfN n (Subtype (Cons y s2 g) (unbindT y t1) (unbindT y t2)) )
                   -> { pf:Subtype | propOf pf == Subtype g (TFunc s1 t1) (TFunc s2 t2) &&
                                     sizeOf pf == n + 1 } 
        SWitn :: n:Nat -> g:Env -> v_x:Value  -> t_x:Type -> ProofOfN n (HasType g v_x t_x)
                   -> t:Type -> t':Type -> ProofOfN n (Subtype g t (tsubBV v_x t'))
                   -> { pf:Subtype | propOf pf == Subtype g t (TExists t_x t') &&
                                     sizeOf pf == n + 1 }
        SBind :: n:Nat -> g:Env -> t_x:Type -> t:Type -> {t':Type | isLCT t'} -> nms:Names
                   -> ({ y:Vname | NotElem y nms }
                           -> ProofOfN n (Subtype (Cons y t_x g) (unbindT y t) t') )
                   -> { pf:Subtype | propOf pf == Subtype g (TExists t_x t) t' &&
                                     sizeOf pf == max n (tdepth t_x) + 1 }
        SPoly :: n:Nat -> g:Env -> k:Kind -> t1:Type -> t2:Type -> nms:Names
                   -> ({ a:Vname | NotElem a nms }
                           -> ProofOfN n (Subtype (ConsT a k g) (unbind_tvT a t1) (unbind_tvT a t2)) )
                   -> { pf:Subtype | propOf pf == Subtype g (TPoly k t1) (TPoly k t2) &&
                                     sizeOf pf == n + 1 } @-}

{-@ measure subtypSize @-}
{-@ subtypSize :: pf:Subtype -> { v:Int | v == sizeOf pf && v >= 1 } @-}
subtypSize :: Subtype -> Int
subtypSize (SBase {})                   = 1
subtypSize (SFunc n _ _ _ _ _ _ _ _)    = n + 1
subtypSize (SWitn n _ _ _ _ _ _ _)      = n + 1
subtypSize (SBind n _ t_x t _ _ _)      = max n (tdepth t_x) + 1
subtypSize (SPoly n _ _ _ _ _ _)        = n + 1

{-@ lem_subtypSize_lb :: g:Env -> s:Type -> t:Type
        -> { p_s_t:Subtype | propOf p_s_t == Subtype g s t }
        -> { pf:_ | sizeOf p_s_t >= tdepth t && sizeOf p_s_t >= tdepth s } / [sizeOf p_s_t] @-}
lem_subtypSize_lb :: Env -> Type -> Type -> Subtype -> Proof
lem_subtypSize_lb g s t (SBase {}) = ()
lem_subtypSize_lb g s t (SFunc _ _ s1 s2 p_s2_s1 t1 t2 nms mk_p_t1_t2)
    = () ? lem_subtypSize_lb g s2 s1 p_s2_s1
         ? lem_subtypSize_lb (Cons y s2 g) (unbindT y t1) (unbindT y t2) (mk_p_t1_t2 y)
             where
               y = fresh_var nms g
lem_subtypSize_lb g s t (SWitn _ _ v_x t_x p_vx_tx _ t' p_s_t'vx)
    = () ? lem_subtypSize_lb g s (tsubBV v_x t') p_s_t'vx
         ? lem_typSize_lb     g v_x t_x p_vx_tx
lem_subtypSize_lb g s t (SBind _ _ s_x s' _ nms mk_p_s'_t)
    = () ? lem_subtypSize_lb (Cons y s_x g) (unbindT y s') t (mk_p_s'_t y)
             where
               y = fresh_var nms g
lem_subtypSize_lb g s t (SPoly _ _ k t1 t2 nms mk_p_t1_t2)
    = () ? lem_subtypSize_lb (ConsT a k g) (unbind_tvT a t1) (unbind_tvT a t2) (mk_p_t1_t2 a)
             where
               a = fresh_var nms g

{-@ reflect isSBase @-}
isSBase :: Subtype -> Bool
isSBase (SBase {}) = True
isSBase _          = False

{-@ reflect isSFunc @-}
isSFunc :: Subtype -> Bool
isSFunc (SFunc {}) = True
isSFunc _          = False

{-@ reflect isSWitn @-}
isSWitn :: Subtype -> Bool
isSWitn (SWitn {}) = True
isSWitn _          = False

{-@ reflect isSBind @-}
isSBind :: Subtype -> Bool
isSBind (SBind {}) = True
isSBind _          = False

{-@ reflect isSPoly @-}
isSPoly :: Subtype -> Bool
isSPoly (SPoly {}) = True
isSPoly _          = False

{-
-------------------------------------------------------------------------
----- | DENOTATIONAL SEMANTICS OF TYPES
-------------------------------------------------------------------------

data Entails where
    EntPred :: Env -> Expr -> (CSub -> DenotesEnv -> PEvalsTrue) -> Entails

{-@ data Entails where
        EntPred :: g:Env -> p:Pred 
                   -> (th:CSub -> ProofOf(DenotesEnv g th) 
                               -> ProofOf(PEvalsTrue (csubst th p)) )
                   -> ProofOf(Entails g p) @-} 

-- We say the proposition ValueDenoted e t holds if there exists a value v such that
--     * e \many v, and
--     * v \in [[ t ]].
{-@ data ValueDenoted where 
        ValDen :: e:Expr -> t:Type -> v:Value -> ProofOf(EvalsTo e v)
                                   -> ProofOf(Denotes t v) -> ProofOf(ValueDenoted e t) @-}
data ValueDenoted where     
    ValDen :: Expr -> Type -> Expr -> EvalsTo -> Denotes -> ValueDenoted

-- placeholder
pEvalsTrue :: Preds -> Bool
pEvalsTrue p = undefined

denotes :: Type -> Value -> DProp   -- also include 
denotes (TRefn b   p)  v = PBase (pEvalsTrue (psubBV v p))
denotes (TFunc   tx t) v = PAll  (\vx -> denotes tx vx => denotes (t[x -> vx]) (app v vx))
denotes (TExists tx t) v =
denotes (TPoly    k t) v =

{-@ data DProp where
        PBase :: ProofOf(PEvalsTrue )

@-}

data DProp = PBase Bool Proposition
           | 
-}

-------------------------------------------------------------------------
----- | UNINTERPRETED IMPLICATION 
-------------------------------------------------------------------------

data Implies where
    IRefl   :: Env -> Preds -> Implies 
    ITrans  :: Env -> Preds -> Preds -> Preds -> Implies -> Implies -> Implies
    IConj   :: Env -> Preds -> Preds -> Preds -> Implies -> Implies -> Implies
    ICons1  :: Env -> Expr  -> Preds -> Implies
    ICons2  :: Env -> Expr  -> Preds -> Implies
    IRepeat :: Env -> Expr  -> Preds -> Implies
    INarrow :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Preds -> Preds -> Implies -> Implies
    IWeak   :: Env -> Env -> Preds -> Preds -> Implies -> Vname -> Type -> Implies 
    IWeakTV :: Env -> Env -> Preds -> Preds -> Implies -> Vname -> Kind -> Implies 
    ISub    :: Env -> Env -> Vname -> Expr -> Type -> HasType -> Preds -> Preds -> Implies -> Implies 
    ISubTV  :: Env -> Env -> Vname -> Type -> Kind -> WFType  -> Preds -> Preds -> Implies -> Implies 
    IEqlSub :: Env -> Basic -> Vname -> Expr -> Preds -> Implies
    IStren  :: Vname -> Basic -> Preds -> Env -> Preds -> Preds -> Implies -> Implies

{-@ data Implies where 
        IRefl   :: g:Env -> ps:Preds -> ProofOf(Implies g ps ps)  
        ITrans  :: g:Env -> ps:Preds -> qs:Preds -> rs:Preds
            -> ProofOf(Implies g ps qs) -> ProofOf(Implies g qs rs) -> ProofOf(Implies g ps rs)
        IConj   :: g:Env -> ps:Preds -> qs:Preds -> rs:Preds 
            -> ProofOf(Implies g ps qs) -> ProofOf(Implies g ps rs)
            -> ProofOf(Implies g ps (strengthen qs rs))
        ICons1  :: g:Env -> p:Expr   -> ps:Preds -> ProofOf(Implies g (PCons p ps) (PCons p PEmpty))
        ICons2  :: g:Env -> p:Expr   -> ps:Preds -> ProofOf(Implies g (PCons p ps) ps)
        IRepeat :: g:Env -> p:Expr   -> ps:Preds -> ProofOf(Implies g (PCons p ps) (PCons p (PCons p ps)))
        INarrow :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> s_x:Type -> t_x:Type
            -> ProofOf(Subtype g s_x t_x) -> ps:Preds -> qs:Preds
            -> ProofOf(Implies (concatE (Cons x t_x g) g') ps qs) 
            -> ProofOf(Implies (concatE (Cons x s_x g) g') ps qs) 
        IWeak   :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> ps:Preds -> qs:Preds  -> ProofOf(Implies (concatE g g') ps qs)
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> t_x:Type 
            -> ProofOf(Implies (concatE (Cons x t_x g) g') ps qs) 
        IWeakTV :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> ps:Preds -> qs:Preds -> ProofOf(Implies (concatE g g') ps qs)
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> k_a:Kind 
            -> ProofOf(Implies (concatE (ConsT a k_a g) g') ps qs)
        ISub    :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> { x:Vname | (not (in_env x g)) && not (in_env x g') } -> v_x:Value
            -> t_x:Type -> ProofOf(HasType g v_x t_x)  -> ps:Preds -> qs:Preds
            -> ProofOf(Implies (concatE (Cons x t_x g) g') ps qs)
            -> ProofOf(Implies (concatE g (esubFV x v_x g')) (psubFV x v_x ps) (psubFV x v_x qs)) 
        ISubTV  :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
            -> { a:Vname | (not (in_env a g)) && not (in_env a g') } -> t_a:Type
            -> k_a:Kind -> ProofOf(WFType g t_a k_a)   -> ps:Preds -> qs:Preds
            -> ProofOf(Implies (concatE (ConsT a k_a g) g') ps qs)
            -> ProofOf(Implies (concatE g (esubFTV a t_a g')) (psubFTV a t_a ps) (psubFTV a t_a qs)) 
        IEqlSub :: g:Env -> b:Basic -> y:Vname -> e:Expr -> ps:Preds
            -> ProofOf(Implies g
                 (PCons (App (App (AppT (Prim Eql) (TRefn b PEmpty)) (FV y)) e) PEmpty)
                 (PCons (App (App (AppT (Prim Eql) (TRefn b ps    )) (FV y)) e) PEmpty) )
        IStren  :: y:Vname -> b':Basic -> qs:Preds -> { g:Env | not (in_env y g) }
            -> p1s:Preds -> p2s:Preds 
            -> ProofOf(Implies (Cons y (TRefn b' qs)     g) p1s p2s)
            -> ProofOf(Implies (Cons y (TRefn b' PEmpty) g) 
                               (strengthen p1s (unbindP y qs)) (strengthen p2s (unbindP y qs))) @-} 
