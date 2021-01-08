{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Typing where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
--import SystemFLemmasFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness

{-@ reflect foo26 @-}   
foo26 x = Just x 
foo26 :: a -> Maybe a 

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Typing Relation and the Subtyping Relation
-----------------------------------------------------------------------------

-- new version of selfification requires a kind submitted for t
-- old vers:  selfify p TBool   z e = App (App (Prim And) p) (App (App (Prim Eqv) (BV z)) e)
{-@ reflect eqlPred @-} 
{-@ eqlPred :: { t:Type | isTRefn t } -> e:Expr
        -> { p':Pred | self t e Base == push p' t } @-}
eqlPred :: Type -> Expr -> Pred
eqlPred (TRefn b z p) e = App (App (AppT (Prim Eql) (TRefn b z p)) (BV 0)) e
{-
{-@ reflect eqlPred @-} 
{-@ eqlPred :: b:Basic -> z:RVname -> p:Pred -> e:Expr
        -> { p':Pred | self (TRefn b z p) e Base == push p' (TRefn b z p) } @-}
eqlPred :: Basic -> Vname -> Pred -> Expr -> Pred
eqlPred b z p e = App (App (AppT (Prim Eql) (TRefn b z p)) (BV z)) e
-}

{-@ reflect selfify @-} 
{-@ selfify :: p:Pred -> b:Basic -> z:RVname -> e:Expr
        -> { p':Pred | fv p' == Set_cup (fv p) (fv e) && 
                       TRefn b z p' == self (TRefn b z p) e Base } @-}
selfify :: Pred -> Basic -> RVname -> Expr -> Pred
selfify p b z e = strengthen  (App (App (AppT (Prim Eql) (TRefn b z p)) (BV 0)) e)  p

{-@ reflect self @-}
{-@ self :: t:Type -> e:Expr -> k:Kind
              -> { t':Type | Set_sub (free t') (Set_cup (free t) (fv e)) &&
                             Set_sub (tfreeBV t') (Set_cup (tfreeBV t) (freeBV e)) && 
                             erase t == erase t' } @-}
self :: Type -> Expr -> Kind -> Type
self t@(TRefn b z p)   e Base = TRefn b z (strengthen  (App (App (AppT (Prim Eql) t) (BV 0)) e)  p)
self (TFunc   z t_z t) e Base = TFunc   z t_z t
self (TExists z t_z t) e Base = TExists z t_z (self t e Base)
self (TPoly   a k_a t) e Base = TPoly   a k_a t
self t                 e Star = t

{-@ lem_tsubFTV_eqlPred :: a:Vname -> { t_a:UserType | isTRefn t_a } -> { t:Type | isTRefn t } -> e:Expr
        -> { pf:_ | subFTV a t_a (eqlPred t e) == 
                     eqlPred (tsubFTV a t_a t) (subFTV a t_a e) } @-}
{-                       App (App (AppT (Prim Eql) (tsubFTV a t_a t)) (BV 0)) (subFTV a t_a e) } @-}
lem_tsubFTV_eqlPred :: Vname -> Type -> Type -> Expr -> Proof
lem_tsubFTV_eqlPred a t_a@(TRefn b' y' q') (TRefn b z p) e = case b of 
  (FTV a') | a' == a  -> () ? lem_subFTV_notin a t_a (BV 0)
                            ? lem_subFTV_notin a t_a (Prim Eql)
                            ? lem_tsubFTV_trefn a t_a (TRefn b z p)
                            ? toProof ( y' === z )
  _                   -> ()


{-@ lem_tsubFTV_self :: a:Vname -> t_a:UserType -> t:Type -> e:Expr -> k:Kind
        -> { pf:_ | tsubFTV a t_a (self t e k) == self (tsubFTV a t_a t) (subFTV a t_a e) k } @-}
lem_tsubFTV_self :: Vname -> Type -> Type -> Expr -> Kind -> Proof
lem_tsubFTV_self a t_a t@(TRefn b z p)     e Base = case b of
  (FTV a') | a' == a  -> case t_a of 
      (TRefn b_a y_a q_a) ->  () {- ? toProof (
         tsubFTV a t_a (self t e Base) === tsubFTV a t_a (push (eqlPred t e) t) -}
       ? lem_subFTV_push a t_a (eqlPred t e) t 
       ? lem_tsubFTV_trefn a t_a t
--     === push (subFTV a t_a (eqlPred t e)) (tsubFTV a t_a t)
       ? lem_tsubFTV_eqlPred a t_a t e
{-     === push (App (App (AppT (Prim Eql) (tsubFTV a t_a t)) (BV z)) (subFTV a t_a e)) (tsubFTV a t_a t)
     === push (eqlPred (tsubFTV a t_a t) (subFTV a t_a e)) (tsubFTV a t_a t)
     === self (tsubFTV a t_a t) (subFTV a t_a e) Base )-}
      (TFunc y t_y t') -> ()
      (TPoly a1 k1 t') -> ()
  _                   -> ()
lem_tsubFTV_self a t_a (TFunc x t_x t)   e Base = ()
lem_tsubFTV_self a t_a (TExists x t_x t) e Base = () ? lem_tsubFTV_self a t_a t e Base
lem_tsubFTV_self a t_a (TPoly a' k_a' t) e Base = ()  
lem_tsubFTV_self a t_a t                 e Star = ()

{-@ lem_tsubBV_self :: z:Vname -> v_z:Value -> t:Type 
        -> { e:Expr | not (Set_mem z (freeBV e)) } -> k:Kind
        -> { pf:_ | tsubBV z v_z (self t e k) == self (tsubBV z v_z t) e k } @-}
lem_tsubBV_self :: Vname -> Expr -> Type -> Expr -> Kind -> Proof
lem_tsubBV_self z v_z (TRefn b x p)     e Base 
  | z == 0    = ()
  | otherwise = () ? lem_subBV_notin z v_z e
lem_tsubBV_self z v_z (TFunc x t_x t)   e Base = ()
lem_tsubBV_self z v_z (TExists x t_x t) e Base 
  | z == x    = ()
  | otherwise = () ? lem_tsubBV_self z v_z t e Base
lem_tsubBV_self z v_z (TPoly a k_a t)   e Base = ()
lem_tsubBV_self z v_z t                 e Star = ()

{-@ lem_tsubFV_self :: z:Vname -> v_z:Expr -> t:Type -> e:Expr -> k:Kind
        -> { pf:_ | tsubFV z v_z (self t e k) == self (tsubFV z v_z t) (subFV z v_z e) k } @-}
lem_tsubFV_self :: Vname -> Expr -> Type -> Expr -> Kind -> Proof
lem_tsubFV_self z v_z (TRefn b w p)     e Base = case b of
  TBool   -> () 
  TInt    -> () 
  (FTV a) -> ()
  (BTV a) -> ()
lem_tsubFV_self z v_z (TFunc   y t_y t) e Base = ()
lem_tsubFV_self z v_z (TExists y t_y t) e Base = () ? lem_tsubFV_self z v_z t e Base
lem_tsubFV_self z v_z (TPoly   a k_a t) e Base = ()
lem_tsubFV_self z v_z t                 e Star = ()

{-@ lem_tsubFV_self0 :: z:Vname -> v_z:Expr -> t:Type -> { x:Vname | x == z } -> k:Kind
        -> { pf:_ | tsubFV z v_z (self t (FV x) k) == self (tsubFV z v_z t) v_z k } @-}
lem_tsubFV_self0 :: Vname -> Expr -> Type -> Vname -> Kind -> Proof
lem_tsubFV_self0 z v_z (TRefn b w p)     x Base = case b of
  TBool   -> () 
  TInt    -> () 
  (FTV a) -> ()
  (BTV a) -> ()
lem_tsubFV_self0 z v_z (TFunc   y t_y t) x Base = ()
lem_tsubFV_self0 z v_z (TExists y t_y t) x Base = () ? lem_tsubFV_self0 z v_z t x Base
lem_tsubFV_self0 z v_z (TPoly   a k_a t) x Base = ()
lem_tsubFV_self0 z v_z t                 x Star = ()

{-@ lem_tsubFV_self1 :: z:Vname -> z':Vname -> t:Type -> { x:Vname | x == z } -> k:Kind
      -> { pf:_ | tsubFV z (FV z') (self t (FV x) k) == self (tsubFV z (FV z') t) (FV z') k } @-}
lem_tsubFV_self1 :: Vname -> Vname -> Type -> Vname -> Kind -> Proof
lem_tsubFV_self1 z z' (TRefn b w p)     x Base = case b of
  TBool   -> () 
  TInt    -> () 
  (FTV a) -> ()
  (BTV a) -> ()
lem_tsubFV_self1 z z' (TFunc   y t_y t) x Base = ()
lem_tsubFV_self1 z z' (TExists y t_y t) x Base = () ? lem_tsubFV_self1 z z' t x Base
lem_tsubFV_self1 z z' (TPoly   a k_a t) x Base = ()
lem_tsubFV_self1 z z' t                 x Star = ()

{-@ lem_tsubFV_self2 :: z:Vname -> v:Value -> t:Type -> { x:Vname | x != z } -> k:Kind
        -> { pf:_ | tsubFV z v (self t (FV x) k) == self (tsubFV z v t) (FV x) k } @-}
lem_tsubFV_self2 :: Vname -> Expr -> Type -> Vname -> Kind -> Proof
lem_tsubFV_self2 z v (TRefn b w p) x Base = case b of
  TBool   -> ()
  TInt    -> ()
  (FTV a) -> ()
  (BTV a) -> ()
lem_tsubFV_self2 z v (TFunc   y t_y t) x Base = ()
lem_tsubFV_self2 z v (TExists y t_y t) x Base = () ? lem_tsubFV_self2 z v t x Base
lem_tsubFV_self2 z v (TPoly   a k_a t) x Base = ()
lem_tsubFV_self2 z v t             x Star = ()

{-
{- @ equals :: b:Basic -> { c:Prim | Set_emp (fv (Prim c)) && Set_emp (freeBV (Prim c)) &&
                  erase_ty c == FTFunc (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool)) } @-}
{-@ reflect equals @-}
{-@ equals :: b:Basic -> { e:Expr | Set_emp (fv e) && Set_emp (freeBV e) } @-}
equals :: Basic -> Expr
equals b = AppT (Prim Eql) (TRefn b 0 (Bc True)) {- equals TBool "=" Prim Eqv
                                                    equals TInt  "=" Prim Eq -}
-}

  --- the Typing Judgement

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where 
    TBC   :: Env -> Bool -> HasType
    TIC   :: Env -> Int -> HasType
    TVar1 :: Env -> Vname -> Type -> Kind -> WFType -> HasType
    TVar2 :: Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TVar3 :: Env -> Vname -> Type -> HasType -> Vname -> Kind -> HasType
    TPrm  :: Env -> Prim -> HasType
    TAbs  :: Env -> Vname -> Type -> Kind -> WFType -> Expr -> Type 
              -> Vname -> HasType -> HasType
    TApp  :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TAbsT :: Env -> Vname -> Kind -> Expr -> Type -> Kind -> Vname
              -> HasType -> WFType -> HasType
    TAppT :: Env -> Expr -> Vname -> Kind -> Type -> HasType -> Type -> WFType -> HasType
    TLet  :: Env -> Expr -> Type -> HasType -> Vname -> Expr
              -> Type -> Kind -> WFType -> Vname -> HasType -> HasType
    TAnn  :: Env -> Expr -> Type -> HasType -> HasType
    TSub  :: Env -> Expr -> Type -> HasType -> Type -> Kind -> WFType -> Subtype -> HasType

{-@ data HasType where
        TBC   :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (tybc b))
        TIC   :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (tyic n))
        TVar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t:Type -> k:Kind -> ProofOf(WFType g t k)
                    -> ProofOf(HasType (Cons x t g) (FV x) (self t (FV x) k))
        TVar2 :: g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOf(HasType g (FV x) t)
                    -> { y:Vname | y != x && not (in_env y g) && not (Set_mem y (free t)) } -> s:Type
                    -> ProofOf(HasType (Cons y s g) (FV x) t)
        TVar3 :: g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOf(HasType g (FV x) t)
                    -> { a:Vname | a != x && not (in_env a g) && not (Set_mem a (freeTV t)) } -> k:Kind
                    -> ProofOf(HasType (ConsT a k g) (FV x) t)
        TPrm  :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty c))
        TAbs  :: g:Env -> x:Vname -> t_x:Type -> k_x:Kind -> ProofOf(WFType g t_x k_x)
                  -> e:Expr -> t:Type 
                  -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) && not (Set_mem y (ftv e)) &&
                                                 not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) } 
                  -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                  -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
        TApp  :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                  -> ProofOf(HasType g e (TFunc x t_x t)) 
                  -> e':Expr -> ProofOf(HasType g e' t_x) 
                  -> ProofOf(HasType g (App e e') (TExists x t_x t))
        TAbsT :: g:Env -> a:Vname -> k:Kind -> e:Expr -> t:Type -> k_t:Kind
                  -> { a':Vname | not (in_env a' g) && not (Set_mem a' (fv e)) && not (Set_mem a' (ftv e)) &&
                                                  not (Set_mem a' (free t)) && not (Set_mem a' (freeTV t)) }
                  -> ProofOf(HasType (ConsT a' k g) (unbind_tv a a' e) (unbind_tvT a a' t))
                  -> ProofOf(WFType  (ConsT a' k g) (unbind_tvT a a' t) k_t)
                  -> ProofOf(HasType g (LambdaT a k e) (TPoly a k t))
        TAppT :: g:Env -> e:Expr -> a:Vname -> k:Kind -> s:Type -> ProofOf(HasType g e (TPoly a k s))
                  -> t:UserType -> ProofOf(WFType g t k)
                  -> ProofOf(HasType g (AppT e t) (tsubBTV a t s))
        TLet  :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                  -> x:Vname -> e:Expr -> t:Type -> k:Kind -> ProofOf(WFType g t k)
                  -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) && not (Set_mem y (ftv e)) &&
                                                   not (Set_mem y (free t)) && not (Set_mem y (freeTV t)) }
                  -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                  -> ProofOf(HasType g (Let x e_x e) t)
        TAnn  :: g:Env -> e:Expr -> t:UserType -> ProofOf(HasType g e t)
                  -> ProofOf(HasType g (Annot e t) t)
        TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type -> k:Kind
                  -> ProofOf(WFType g t k) -> ProofOf(Subtype g s t) 
                  -> ProofOf(HasType g e t) @-} 

{-@ lazy typSize @-}
{-@ measure typSize @-}
{-@ typSize :: HasType -> { v:Int | v >= 0 } @-}
typSize :: HasType -> Int
typSize (TBC {})                               = 1
typSize (TIC {})                               = 1
typSize (TVar1 {})                             = 1
typSize (TVar2 _ _ _ p_x_b _ _)                = (typSize p_x_b)   + 1
typSize (TVar3 _ _ _ p_x_b _ _)                = (typSize p_x_b)   + 1
typSize (TPrm {})                              = 1
typSize (TAbs _ _ _ _ _ _ _ _ p_e_b')          = (typSize p_e_b')  + 1
typSize (TApp _ _ _ _ _ p_e_bb' _ p_e'_b)      = (typSize p_e_bb') + (typSize p_e'_b)   + 1
typSize (TAbsT _ _ _ _ _ _ _ p_e_t _)          = (typSize p_e_t)   + 1
typSize (TAppT _ _ _ _ _ p_e_as _ _)           = (typSize p_e_as)  + 1
typSize (TLet _ _ _ p_ex_b _ _ _ _ _ _ p_e_b') = (typSize p_ex_b)  + (typSize p_e_b')   + 1
typSize (TAnn _ _ _ p_e_b)                     = (typSize p_e_b)   + 1
typSize (TSub _ _ _ p_e_s _ _ _ p_s_t)         = (typSize p_e_s)   + (subtypSize p_s_t) + 1

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

data SubtypeP where
    Subtype :: Env -> Type -> Type -> SubtypeP

data Subtype where
    SBase :: Env -> RVname -> Basic -> Pred -> RVname -> Pred -> Vname -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Vname -> Subtype -> Subtype
    SWitn :: Env -> Expr -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> Type -> Type -> Vname -> Subtype -> Subtype
    SPoly :: Env -> Vname -> Kind -> Type -> Vname -> Type -> Vname -> Subtype -> Subtype

-- edited SFunc 5/5/20: was -> { x2:Vname | not (in_Env x2 g) }. x2 is a BV so there's no
--     possibility for collision with the FV's in the environment g.
{-@ data Subtype where
        SBase :: g:Env -> v1:RVname -> b:Basic -> p1:Pred -> v2:RVname -> p2:Pred 
                 -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
                 -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind 0 y p2))
                 -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
        SFunc :: g:Env -> x1:Vname -> s1:Type -> x2:Vname -> s2:Type
                 -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
                 -> { y:Vname | not (in_env y g) && not (Set_mem y (free t1))
                                                 && not (Set_mem y (free t2))
                                && not (Set_mem y (freeTV t1)) && not (Set_mem y (freeTV t2)) }
                 -> ProofOf(Subtype (Cons y s2 g) (unbindT x1 y t1) (unbindT x2 y t2))
                 -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
        SWitn :: g:Env -> e:Value  -> t_x:Type -> ProofOf(HasType g e t_x)
                 -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubBV x e t'))
                 -> ProofOf(Subtype g t (TExists x t_x t'))
        SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (tfreeBV t')}
                 -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                                 && not (Set_mem y (free t')) }
                 -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
                 -> ProofOf(Subtype g (TExists x t_x t) t')
        SPoly :: g:Env -> a1:Vname -> k:Kind -> t1:Type -> a2:Vname -> t2:Type
                 -> { a:Vname | not (in_env a g) 
                                && not (Set_mem a (free t1)) && not (Set_mem a (freeTV t1))
                                && not (Set_mem a (free t2)) && not (Set_mem a (freeTV t2)) }
                 -> ProofOf(Subtype (ConsT a k g) (unbind_tvT a1 a t1) (unbind_tvT a2 a t2))
                 -> ProofOf(Subtype g (TPoly a1 k t1) (TPoly a2 k t2))  @-}

{-@ lazy subtypSize @-}
{-@ measure subtypSize @-}
{-@ subtypSize :: Subtype -> { v:Int | v >= 0 } @-}
subtypSize :: Subtype -> Int
subtypSize (SBase {})                              = 1
subtypSize (SFunc _ _ _ _ _ p_s2_s1 _ _ _ p_t1_t2) = (subtypSize p_s2_s1) + (subtypSize p_t1_t2) + 1
subtypSize (SWitn _ _ _ p_e_tx _ _ _ p_t_t')       = (subtypSize p_t_t')  + (typSize p_e_tx)     + 1
subtypSize (SBind _ _ _ _ _ _ p_t_t')              = (subtypSize p_t_t')  + 1
subtypSize (SPoly _ _ _ _ _ _ _ p_t1_t2)           = (subtypSize p_t1_t2) + 1 

{-@ measure subtypSize' @-}
{-@ subtypSize' :: Subtype -> { v:Int | v >= 0 } @-}
subtypSize' :: Subtype -> Int
subtypSize' (SBase {})                              = 1
subtypSize' (SFunc _ _ _ _ _ p_s2_s1 _ _ _ p_t1_t2) = (subtypSize' p_s2_s1) + (subtypSize' p_t1_t2) + 1
subtypSize' (SWitn _ _ _ p_e_tx _ _ _ p_t_t')       = (subtypSize' p_t_t')  + 1
subtypSize' (SBind _ _ _ _ _ _ p_t_t')              = (subtypSize' p_t_t')  + 1
subtypSize' (SPoly _ _ _ _ _ _ _ p_t1_t2)           = (subtypSize' p_t1_t2) + 1 

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
----- | ALPHA EQUIVALENCE for SYSTEM F
-------------------------------------------------------------------------

-- | Alpha equivalence in System F. These partition the set of FTypes into equivlance 
-- |     classes. We need a separate formalization of this because our System F has
-- |     no notion of subtypes. Cf Pierce, TAPL, Chapter 23 (Figure 23-1)

data AlphaEqvP where
    AlphaEqv :: FEnv -> FType -> FType -> AlphaEqvP

data AlphaEqv where
    AEBasic :: FEnv -> Basic -> AlphaEqv
    AEFunc  :: FEnv -> FType -> FType -> AlphaEqv -> FType -> FType -> AlphaEqv -> AlphaEqv
    AEPoly  :: FEnv -> Vname -> Kind -> FType -> Vname -> FType -> Vname -> AlphaEqv -> AlphaEqv

{-@ data AlphaEqv where
        AEBasic :: g:FEnv -> { b:Basic | Set_sub (ffreeTV (FTBasic b)) (tvbindsF g) }
                     -> ProofOf(AlphaEqv g (FTBasic b) (FTBasic b))
        AEFunc  :: g:FEnv -> s1:FType -> s2:FType -> ProofOf(AlphaEqv g s1 s2)
                     -> t1:FType -> t2:FType -> ProofOf(AlphaEqv g t1 t2)
                     -> ProofOf(AlphaEqv g (FTFunc s1 t1) (FTFunc s2 t2))
        AEPoly  :: g:FEnv -> a1:Vname -> k:Kind -> { t1:FType | Set_sub (ffreeTV t1) (tvbindsF g) }
                     -> a2:Vname -> { t2:FType | Set_sub (ffreeTV t2) (tvbindsF g) }
                     -> { a:Vname | not (Set_mem a (bindsF g)) }
                     -> ProofOf(AlphaEqv (FConsT a k g) (unbindFT a1 a t1) (unbindFT a2 a t2))
                     -> ProofOf(AlphaEqv g (FTPoly a1 k t1) (FTPoly a2 k t2)) @-} -- @-}

{-@ measure alphaSize @-}
{-@ alphaSize :: AlphaEqv -> { v:Int | v >= 0 } @-}
alphaSize :: AlphaEqv -> Int
alphaSize (AEBasic _ _)                        = 1
alphaSize (AEFunc _ _ _ ae_s1_s2 _ _ ae_t1_t2) = alphaSize ae_s1_s2 + alphaSize ae_t1_t2 + 1
alphaSize (AEPoly _ _ _ _ _ _ _ ae_t1_t2)      = alphaSize ae_t1_t2 + 1

-------------------------------------------------------------------------
----- | CLOSING SUBSTITUTIONS 
-------------------------------------------------------------------------

-- closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
--   the typing env downwards/leftwards. In order for a closing substitution to be
--   "well formed" it must be an element of the denotation the corresponding enivornment

data CSub = CEmpty
          | CCons  Vname Expr CSub
          | CConsT Vname Type CSub
  deriving (Show)
{-@ data CSub  where
        CEmpty :: CSub
        CCons  :: x:Vname -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) &&
                                         Set_emp (freeBV v) && Set_emp (freeBTV v) } 
                          -> { th:CSub | not (in_csubst x th ) } 
                          -> { th':CSub | bindsC th'   == Set_cup (Set_sng x)  (bindsC th) && 
                                          vbindsC th'  == Set_cup (Set_sng x) (vbindsC th) &&
                                          tvbindsC th' == tvbindsC th &&
                                          Set_cup (vbindsC th') (tvbindsC th') == bindsC th' &&
                                          Set_emp (Set_cap (vbindsC th') (tvbindsC th')) } 
        CConsT :: a:Vname -> { t:UserType | Set_emp (free t) && Set_emp (freeTV t) &&
                                            Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) }
                          -> { th:CSub | not (in_csubst a th) }
                          -> { th':CSub | bindsC th'   == Set_cup (Set_sng a)   (bindsC th) && 
                                          vbindsC th'  == vbindsC th &&
                                          tvbindsC th' == Set_cup (Set_sng a) (tvbindsC th) &&
                                          Set_cup (vbindsC th') (tvbindsC th') == bindsC th' &&
                                          Set_emp (Set_cap (vbindsC th') (tvbindsC th')) } @-}

{-@ measure csubstSize @-}
csubstSize :: CSub -> Int
csubstSize CEmpty           = 1
csubstSize (CCons y v_y th) = (csubstSize th) + 1
csubstSize (CConsT a k  th) = (csubstSize th) + 1

{-@ reflect bindsC @-}
bindsC :: CSub -> S.Set Vname
bindsC CEmpty          = S.empty
bindsC (CCons  x v th) = S.union (S.singleton x) (bindsC th)
bindsC (CConsT a t th) = S.union (S.singleton a) (bindsC th)

{-@ reflect in_csubst @-}
in_csubst :: Vname -> CSub -> Bool
in_csubst x th = S.member x (bindsC th)

{-@ reflect vbindsC @-}
vbindsC :: CSub -> S.Set Vname
vbindsC CEmpty          = S.empty
vbindsC (CCons  x v th) = S.union (S.singleton x) (vbindsC th)
vbindsC (CConsT a t th) = vbindsC th

{-@ reflect v_in_csubst @-}
v_in_csubst :: Vname -> CSub -> Bool
v_in_csubst x th = S.member x (vbindsC th)

{-@ reflect tvbindsC @-}
tvbindsC :: CSub -> S.Set Vname
tvbindsC CEmpty          = S.empty
tvbindsC (CCons  x v th) = tvbindsC th
tvbindsC (CConsT a t th) = S.union (S.singleton a) (tvbindsC th)

{-@ reflect tv_in_csubst @-}
tv_in_csubst :: Vname -> CSub -> Bool
tv_in_csubst a th = S.member a (tvbindsC th)

{-@ reflect bound_inC @-}
bound_inC :: Vname -> Expr -> CSub -> Bool
bound_inC x v CEmpty                              = False
bound_inC x v (CCons y v' th) | (x == y)          = (v == v')
                              | otherwise         = bound_inC x v th
bound_inC x v (CConsT a t th) | (x == a)          = False
                              | otherwise         = bound_inC x v th

{-@ reflect tv_bound_inC @-}
tv_bound_inC :: Vname -> Type -> CSub -> Bool
tv_bound_inC a t CEmpty                                = False
tv_bound_inC a t (CCons  y  v' th) | (a == y)          = False
                                   | otherwise         = tv_bound_inC a t th
tv_bound_inC a t (CConsT a' t' th) | (a == a')         = (t == t')
                                   | otherwise         = tv_bound_inC a t th

{-@ reflect csubst @-}
{-@ csubst :: th:CSub -> e:Expr -> { e':Expr | isTerm e => isTerm e' } @-}
csubst :: CSub -> Expr -> Expr
csubst CEmpty          e = e
csubst (CCons  x v th) e = csubst th (subFV x v e)
csubst (CConsT a t th) e = csubst th (subFTV a t e)

-- Idea: ctsubst th t = foldr (\(x,e) t' -> tsubFV x e t') t th 
{-@ reflect ctsubst @-}
{-@ ctsubst :: th:CSub -> t:Type -> Type @-}
ctsubst :: CSub -> Type -> Type
ctsubst CEmpty           t = t
ctsubst (CCons  x v  th) t = ctsubst th (tsubFV x v t)
ctsubst (CConsT a t' th) t = ctsubst th (tsubFTV a t' t)

{-@ reflect csubst_tv @-}
{-@ csubst_tv :: th:CSub -> { a:Vname | tv_in_csubst a th } -> Type @-}
csubst_tv :: CSub -> Vname -> Type
csubst_tv (CCons  x  v  th) a             = csubst_tv th a
csubst_tv (CConsT a' t' th) a | a' == a   = t'
                              | otherwise = csubst_tv th a

{-@ reflect concatCS @-}
{-@ concatCS :: th:CSub -> { th':CSub | Set_emp (Set_cap (bindsC th) (bindsC th')) }
                          -> { thC:CSub | bindsC thC == Set_cup (bindsC th) (bindsC th') } @-}
concatCS :: CSub -> CSub -> CSub
concatCS th CEmpty           = th
concatCS th (CCons  x v th') = CCons x v (concatCS th th')
concatCS th (CConsT a t th') = CConsT a t (concatCS th th')


{-@ reflect change_varCS @-}
{-@ change_varCS :: th:CSub ->  { x:Vname | v_in_csubst x th } 
        -> { y:Vname | y == x || not (in_csubst y th) } 
        -> { th':CSub | bindsC th'  == Set_cup (Set_sng y) (Set_dif  (bindsC th) (Set_sng x)) &&
                        vbindsC th' == Set_cup (Set_sng y) (Set_dif (vbindsC th) (Set_sng x)) &&
                        tvbindsC th' == tvbindsC th } @-} 
change_varCS :: CSub -> Vname -> Vname -> CSub
change_varCS CEmpty            x y              = CEmpty
change_varCS (CCons  z v_z th) x y | ( x == z ) = CCons  y v_z th
                                   | otherwise  = CCons  z v_z (change_varCS th x y)
change_varCS (CConsT a t_a th) x y              = CConsT a t_a (change_varCS th x y)

{-@ reflect change_tvarCS @-}
{-@ change_tvarCS :: th:CSub ->  { a:Vname | tv_in_csubst a th } 
        -> { a':Vname | a' == a || not (in_csubst a' th) } 
        -> { th':CSub | bindsC th'   == Set_cup (Set_sng a') (Set_dif   (bindsC th) (Set_sng a)) &&
                        vbindsC th'  == vbindsC th &&
                        tvbindsC th' == Set_cup (Set_sng a') (Set_dif (tvbindsC th) (Set_sng a)) } @-} 
change_tvarCS :: CSub -> Vname -> Vname -> CSub
change_tvarCS CEmpty             a a'               = CEmpty
change_tvarCS (CCons  z  v_z th) a a'               = CCons  z  v_z (change_tvarCS th a a')
change_tvarCS (CConsT a1 t_a th) a a' | ( a == a1 ) = CConsT a' t_a th
                                      | otherwise   = CConsT a1 t_a (change_tvarCS th a a')

{-@ reflect remove_fromCS @-}
{-@ remove_fromCS :: th:CSub -> { x:Vname | in_csubst x th}
        -> { th':CSub | bindsC th' == Set_dif (bindsC th) (Set_sng x) } @-}
remove_fromCS :: CSub -> Vname -> CSub
remove_fromCS (CCons  z v_z th) x | ( x == z ) = th
                                  | otherwise  = CCons  z v_z (remove_fromCS th x)
remove_fromCS (CConsT a t_a th) x | ( x == a ) = th
                                  | otherwise  = CConsT a t_a (remove_fromCS th x)

-------------------------------------------------------------------------
----- | ENTAILMENTS and DENOTATIONAL SEMANTICS 
-------------------------------------------------------------------------

data EntailsP where
    Entails :: Env -> Pred -> EntailsP

data Entails where
    EntPred :: Env -> Pred -> (CSub -> DenotesEnv -> EvalsTo) -> Entails

{-@ data Entails where
        EntPred :: g:Env -> p:Pred 
                   -> (th:CSub -> ProofOf(DenotesEnv g th) 
                               -> ProofOf(EvalsTo (csubst th p) (Bc True)) )
                   -> ProofOf(Entails g p) @-} 

-- We say the proposition ValueDenoted e t holds if there exists a value v such that
--     * e \many v, and
--     * v \in [[ t ]].
data ValueDenotedP where
    ValueDenoted :: Expr -> Type -> ValueDenotedP

{-@ data ValueDenoted where 
        ValDen :: e:Expr -> t:Type -> v:Value -> ProofOf(EvalsTo e v)
                                   -> ProofOf(Denotes t v) -> ProofOf(ValueDenoted e t) @-}
data ValueDenoted where     
    ValDen :: Expr -> Type -> Expr -> EvalsTo -> Denotes -> ValueDenoted


data DenotesP where 
    Denotes :: Type -> Expr -> DenotesP    -- e \in [[t]]

data Denotes where
    DRefn :: Basic -> RVname -> Pred -> Expr -> HasFType -> EvalsTo -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> FType -> FType -> AlphaEqv -> HasFType
              -> (Expr -> Denotes -> ValueDenoted) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> FType -> AlphaEqv -> HasFType
              -> Expr -> Denotes -> Denotes -> Denotes
    DPoly :: Vname -> Kind -> Type -> Expr -> Vname -> FType -> AlphaEqv -> HasFType
              -> (Type -> WFType -> ValueDenoted) -> Denotes
{-@ data Denotes where
        DRefn :: b:Basic -> x:RVname -> p:Pred -> v:Value  
                  -> ProofOf(HasFType FEmpty v (FTBasic b))
                  -> ProofOf(EvalsTo (subBV 0 v p) (Bc True)) 
                  -> ProofOf(Denotes (TRefn b x p) v)
        DFunc :: x:Vname -> t_x:Type -> t:Type -> v:Value
                  -> s_x:FType -> s:FType 
                  -> ProofOf(AlphaEqv FEmpty (FTFunc s_x s) (erase (TFunc x t_x t)))
                  -> ProofOf(HasFType FEmpty v (FTFunc s_x s))
                  -> ( v_x:Value -> ProofOf(Denotes t_x v_x)
                                 -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x t)) ) 
                  -> ProofOf(Denotes (TFunc x t_x t) v)
        DExis :: x:Vname -> t_x:Type -> t:Type -> v:Value -> s:FType
                  -> ProofOf(AlphaEqv FEmpty s (erase t)) -> ProofOf(HasFType FEmpty v s) 
                  -> v_x:Value -> ProofOf(Denotes t_x v_x)
                  -> ProofOf(Denotes (tsubBV x v_x t) v)
                  -> ProofOf(Denotes (TExists x t_x t) v)  
        DPoly :: a:Vname -> k:Kind -> t:Type -> v:Value -> a0:Vname -> s:FType
                  -> ProofOf(AlphaEqv FEmpty (FTPoly a0 k s) (FTPoly a k (erase t)))
                  -> ProofOf(HasFType FEmpty v (FTPoly a0 k s))
                  -> ( t_a:UserType -> ProofOf(WFType Empty t_a k) 
                                    -> ProofOf(ValueDenoted (AppT v t_a) (tsubBTV a t_a t)) )
                  -> ProofOf(Denotes (TPoly a k t) v) @-} -- @-}


{-@ get_ftyp_from_den :: t:Type -> v:Value -> ProofOf(Denotes t v)
              -> (FType,HasFType)<{\s pf -> propOf pf == HasFType FEmpty v s }> @-}
get_ftyp_from_den :: Type -> Expr -> Denotes -> (FType,HasFType)
get_ftyp_from_den t v (DRefn b _ _ _ pf_v_b _)         = (FTBasic b,     pf_v_b)
get_ftyp_from_den t v (DFunc _ _ _ _ s_x s _ pf_v_b _) = (FTFunc s_x s,  pf_v_b)
get_ftyp_from_den t v (DExis _ _ _ _ s _ pf_v_b _ _ _) = (s,             pf_v_b)
get_ftyp_from_den t v (DPoly _ k _ _ a0 s _ pf_v_b _)  = (FTPoly a0 k s, pf_v_b)

{-@ lem_den_nofv :: v:Value -> t:Type -> ProofOf(Denotes t v) 
        -> { pf:_ | Set_emp (fv v) && Set_emp (ftv v) } @-}
lem_den_nofv :: Expr -> Type -> Denotes -> Proof
lem_den_nofv v t den_t_v = lem_fv_subset_bindsF FEmpty v bt pf_v_bt
  where
    (bt, pf_v_bt) = get_ftyp_from_den t v den_t_v

{-@ lem_den_nobv :: v:Value -> t:Type -> ProofOf(Denotes t v) 
        -> { pf:_ | Set_emp (freeBV v) && Set_emp (freeBTV v) } @-}
lem_den_nobv :: Expr -> Type -> Denotes -> Proof
lem_den_nobv v t den_t_v = lem_freeBV_emptyB FEmpty v bt pf_v_bt
  where
   (bt, pf_v_bt) = get_ftyp_from_den t v den_t_v

{-@ get_obj_from_dfunc :: x:Vname -> s:Type -> t:Type -> v:Value 
        -> ProofOf(Denotes (TFunc x s t) v) -> v':Value 
        -> ProofOf(Denotes s v') -> ProofOf(ValueDenoted (App v v') (tsubBV x v' t)) @-}  
get_obj_from_dfunc :: Vname -> Type -> Type -> Expr -> Denotes 
                                    -> Expr -> Denotes -> ValueDenoted
get_obj_from_dfunc x s t v (DFunc _ _ _ _ _ _ _ _ prover) v' den_s_v' = prover v' den_s_v' 

{-@ get_obj_from_dpoly :: a:Vname -> k:Kind -> t:Type -> v:Value -> ProofOf(Denotes (TPoly a k t) v) 
        -> t_a:UserType -> ProofOf(WFType Empty t_a k)
        -> ProofOf(ValueDenoted (AppT v t_a) (tsubBTV a t_a t)) @-}
get_obj_from_dpoly :: Vname -> Kind -> Type -> Expr -> Denotes 
                                    -> Type -> WFType -> ValueDenoted
get_obj_from_dpoly a k t v (DPoly _ _ _ _ _ _ _ _ prover) t_a p_emp_ta = prover t_a p_emp_ta

-- Denotations of Environments, [[g]]. There are two cases:
--   1. [[ Empty ]] = { CEmpty }.
--   2. [[ Cons x t g ]] = { CCons x v_x th | Denotes th(t) v_x && th \in [[ g ]] }
data DenotesEnvP where 
    DenotesEnv :: Env -> CSub -> DenotesEnvP 

data DenotesEnv where
    DEmp :: DenotesEnv
    DExt :: Env -> CSub -> DenotesEnv -> Vname -> Type -> Expr -> Denotes -> DenotesEnv
    DExtT :: Env -> CSub -> DenotesEnv -> Vname -> Kind -> Type -> WFType -> DenotesEnv
{-@ data DenotesEnv where 
        DEmp  :: ProofOf(DenotesEnv Empty CEmpty)
        DExt  :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
                 -> { x:Vname | not (in_env x g) } -> t:Type 
                 -> { v:Value | Set_emp (fv v) && Set_emp (ftv v) && Set_emp (freeBV v) && Set_emp (freeBTV v) }
                 -> ProofOf(Denotes (ctsubst th t) v)
                 -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th))
        DExtT :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th)
                   -> { a:Vname | not (in_env a g) } -> k:Kind
                   -> { t:UserType  | Set_emp (free t) && Set_emp (freeTV t) &&
                                      Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) }
                   -> ProofOf(WFType Empty t k)
                   -> ProofOf(DenotesEnv (ConsT a k g) (CConsT a t th)) @-}

{-@ lem_binds_env_th :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> { pf:_ | binds g == bindsC th && vbinds g == vbindsC th && tvbinds g == tvbindsC th } @-}
lem_binds_env_th :: Env -> CSub -> DenotesEnv -> Proof
lem_binds_env_th g th DEmp                                       = ()
lem_binds_env_th g th (DExt  g' th' den_g'_th' x t v den_th't_v) = () ? lem_binds_env_th g' th' den_g'_th'
lem_binds_env_th g th (DExtT g' th' den_g'_th' a k t p_emp_tha)  = () ? lem_binds_env_th g' th' den_g'_th'
