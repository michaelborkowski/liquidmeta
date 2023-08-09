{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Typing where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
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
    TBC   :: Env -> Bool -> HasType
    TIC   :: Env -> Int -> HasType
    TVar1 :: Env -> Vname -> Type -> Kind -> WFType -> HasType
    TVar2 :: Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TVar3 :: Env -> Vname -> Type -> HasType -> Vname -> Kind -> HasType
    TPrm  :: Env -> Prim -> HasType
    TAbs  :: Env -> Type -> Kind -> WFType -> Expr -> Type -> Names
                 -> (Vname -> HasType) -> HasType
    TApp  :: Env -> Expr -> Type -> Type -> HasType 
                 -> Expr -> HasType -> HasType
    TAbsT :: Env -> Kind -> Expr -> Type -> Names -> (Vname -> HasType) -> HasType
    TAppT :: Env -> Expr -> Kind -> Type -> HasType -> Type -> WFType -> HasType
    TLet  :: Env -> Expr -> Type -> HasType -> Expr -> Type -> Kind -> WFType 
                 -> Names -> (Vname -> HasType) -> HasType
    TAnn  :: Env -> Expr -> Type -> HasType -> HasType
    TSub  :: Env -> Expr -> Type -> HasType -> Type -> Kind -> WFType -> Subtype -> HasType

{-@ measure sizeOf :: a -> Nat @-}
{-@ data size (HasType, Subtype) sizeOf @-}

{-@ data HasType where
        TBC   :: g:Env -> b:Bool -> { pf:HasType | propOf pf == HasType g (Bc b) (tybc b) &&
                                                   sizeOf pf == 1  }
        TIC   :: g:Env -> m:Int  -> { pf:HasType | propOf pf == HasType g (Ic m) (tyic m) &&
                                                   sizeOf pf == 1 }
        TVar1 :: g:Env -> { x:Vname | not (in_env x g) } 
                    -> t:Type -> k:Kind -> ProofOf(WFType g t k) 
                    -> { pf:HasType | propOf pf == HasType (Cons x t g) (FV x) (self t (FV x) k) &&
                                      sizeOf pf == tdepth t }
        TVar2 :: g:Env -> { x:Vname | in_env x g } -> t:Type 
                    -> { pf0:HasType | propOf  pf0 == (HasType g (FV x) t) }
                    -> { y:Vname | y != x && not (in_env y g) } -> s:Type
                    -> { pf:HasType | propOf  pf == (HasType (Cons y s g) (FV x) t) }
        TVar3 :: g:Env -> { x:Vname | in_env x g } -> t:Type 
                    -> { pf0:HasType | propOf  pf0 == (HasType g (FV x) t) }
                    -> { a:Vname | a != x && not (in_env a g) } -> k:Kind
                    -> { pf:HasType | propOf  pf == (HasType (ConsT a k g) (FV x) t) }
        TPrm  :: g:Env -> c:Prim -> { pf:HasType | propOf pf == HasType g (Prim c) (ty c) &&
                                                   sizeOf pf == tdepth (ty c) }
        TAbs  :: g:Env -> t_x:Type -> k_x:Kind -> ProofOf(WFType g t_x k_x)
                  -> e:Expr -> t:Type -> nms:Names
                  -> ( { y:Vname | NotElem y nms } 
                           -> { pf0:HasType | propOf  pf0 == (HasType (Cons y t_x g) (unbind y e) (unbindT y t)) } ) 
                  -> { pf:HasType | propOf  pf == (HasType g (Lambda e) (TFunc t_x t)) }
        TApp  :: g:Env -> e:Expr -> t_x:Type -> t:Type 
                  -> { pf0:HasType | propOf  pf0 == (HasType g e (TFunc t_x t)) }
                  -> e':Expr -> { pf1:HasType | propOf  pf1 == (HasType g e' t_x) }
                  -> { pf:HasType | propOf  pf == (HasType g (App e e') (TExists t_x t)) }
        TAbsT :: g:Env -> k:Kind -> e:Expr -> t:Type -> nms:Names
                  -> ({ a':Vname | NotElem a' nms }
                           -> { pf0:HasType | propOf  pf0 == (HasType (ConsT a' k g) (unbind_tv a' e) (unbind_tvT a' t)) } )
                  -> { pf:HasType | propOf  pf == (HasType g (LambdaT k e) (TPoly k t)) }
        TAppT :: g:Env -> e:Expr -> k:Kind -> s:Type 
                  -> { pf0:HasType | propOf  pf0 == (HasType g e (TPoly k s)) }
                  -> t:UserType -> ProofOf(WFType g t k)
                  -> { pf:HasType | propOf  pf == (HasType g (AppT e t) (tsubBTV t s)) }
        TLet  :: g:Env -> e_x:Expr -> t_x:Type 
                  -> { pf0:HasType | propOf  pf0 == (HasType g e_x t_x) }
                  -> e:Expr -> t:Type -> k:Kind -> ProofOf(WFType g t k) -> nms:Names
                  -> ({ y:Vname | NotElem y nms }
                          -> { pf1:HasType | propOf  pf1 == (HasType (Cons y t_x g) (unbind y e) (unbindT y t)) } )
                  -> { pf:HasType | propOf  pf == (HasType g (Let e_x e) t) }
        TAnn  :: g:Env -> e:Expr -> t:UserType 
                  -> { pf0:HasType | propOf  pf0 == (HasType g e t) }
                  -> { pf:HasType | propOf  pf == (HasType g (Annot e t) t) }
        TSub  :: g:Env -> e:Expr -> s:Type 
                  -> { pf0:HasType | propOf  pf0 == (HasType g e s) }
                  -> t:Type -> k:Kind -> ProofOf(WFType g t k) 
                  -> { pf1:Subtype | propOf  pf1 == (Subtype g s t) }
                  -> { pf:HasType | propOf  pf == (HasType g e t) } @-} 

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
    SFunc :: Env -> Type -> Type -> Subtype -> Type -> Type -> Names 
               -> (Vname -> Subtype) -> Subtype
    SWitn :: Env -> Expr -> Type -> HasType -> Type -> Type -> Subtype  -> Subtype
    SBind :: Env -> Type -> Type -> Type -> Names -> (Vname -> Subtype) -> Subtype
    SPoly :: Env -> Kind -> Type -> Type -> Names -> (Vname -> Subtype) -> Subtype

{-@ data Subtype where
        SBase :: g:Env -> b:Basic -> p1:Preds -> p2:Preds -> nms:Names
                   -> ({ y:Vname | NotElem y nms} 
                           -> ProofOf(Implies (Cons y (TRefn b PEmpty) g) 
                                              (unbindP y p1) (unbindP y p2)) )
                   -> { pf:Subtype | propOf pf == Subtype g (TRefn b p1) (TRefn b p2) &&
                                     sizeOf pf == 1 }
        SFunc :: g:Env -> s1:Type -> s2:Type 
                   -> { pf0:Subtype | propOf pf0 == (Subtype g s2 s1) }
                   -> t1:Type -> t2:Type -> nms:Names
                   -> ({ y:Vname | NotElem y nms} 
                          -> { pf1:Subtype | propOf pf1 == (Subtype (Cons y s2 g) (unbindT y t1) (unbindT y t2)) } )
                   -> { pf:Subtype | propOf pf == (Subtype g (TFunc s1 t1) (TFunc s2 t2)) }
        SWitn :: g:Env -> v_x:Value  -> t_x:Type 
                   -> { pf0:HasType | propOf pf0 == (HasType g v_x t_x) }
                   -> t:Type -> t':Type 
                   -> { pf1:Subtype | propOf pf1 == (Subtype g t (tsubBV v_x t')) }
                   -> { pf:Subtype | propOf pf == (Subtype g t (TExists t_x t')) }
        SBind :: g:Env -> t_x:Type -> t:Type -> {t':Type | isLCT t'} -> nms:Names
                   -> ({ y:Vname | NotElem y nms }
                           -> { pf0:Subtype | propOf pf0 == (Subtype (Cons y t_x g) (unbindT y t) t') } )
                   -> { pf:Subtype | propOf pf == (Subtype g (TExists t_x t) t') }
        SPoly :: g:Env -> k:Kind -> t1:Type -> t2:Type -> nms:Names
                   -> ({ a:Vname | NotElem a nms }
                           -> { pf0:Subtype | propOf pf0 == (Subtype (ConsT a k g) (unbind_tvT a t1) (unbind_tvT a t2)) } )
                   -> { pf:Subtype | propOf pf == (Subtype g (TPoly k t1) (TPoly k t2)) } @-}

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
