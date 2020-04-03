{-# LANGUAGE GADTs #-}

--{-@ LIQUID "--higherorder" @-}
{- @ LIQUID "--diff"        @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Typing where

--import Control.Exception (assert)
import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Semantics

-- force these into scope
semantics = (Step, EvalsTo)

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation and the Typing Relation
-----------------------------------------------------------------------------

data HasBTypeP where
    HasBType :: BEnv -> Expr -> BType -> HasBTypeP 

data HasBType where
    BTBC   :: BEnv -> Bool -> HasBType
    BTIC   :: BEnv -> Int -> HasBType
    BTVar1 :: BEnv -> Vname -> BType -> HasBType 
    BTVar2 :: BEnv -> Vname -> BType -> HasBType -> Vname -> BType -> HasBType
    BTPrm  :: BEnv -> Prim -> HasBType
    BTAbs  :: BEnv -> Vname -> BType -> Expr -> BType -> Vname -> HasBType -> HasBType
    BTApp  :: BEnv -> Expr -> BType -> BType -> HasBType 
              -> Expr -> HasBType -> HasBType
    BTLet  :: BEnv -> Expr -> BType -> HasBType -> Vname -> Expr
              -> BType -> Vname -> HasBType -> HasBType
    BTAnn  :: BEnv -> Expr -> BType -> Type -> HasBType -> HasBType

{-@ data HasBType where
    BTBC   :: g:BEnv -> b:Bool -> ProofOf(HasBType g (Bc b) (BTBase TBool))
 |  BTIC   :: g:BEnv -> n:Int -> ProofOf(HasBType g (Ic n) (BTBase TInt))
 |  BTVar1 :: g:BEnv -> { x:Vname | not (in_envB x g) } -> b:BType 
                -> ProofOf(HasBType (BCons x b g) (FV x) b)
 |  BTVar2 :: g:BEnv -> { x:Vname | in_envB x g } -> b:BType -> ProofOf(HasBType g (FV x) b)
                -> { y:Vname | y != x && not (in_envB y g) } -> b':BType 
                -> ProofOf(HasBType (BCons y b' g) (FV x) b)
 |  BTPrm  :: g:BEnv -> c:Prim  -> ProofOf(HasBType g (Prim c) (erase (ty c)))
 |  BTAbs  :: g:BEnv -> x:Vname -> b:BType -> e:Expr -> b':BType
                -> { y:Vname | not (in_envB y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasBType (BCons y b g) (unbind x y e) b')
                -> ProofOf(HasBType g (Lambda x e) (BTFunc b b'))
 |  BTApp  :: g:BEnv -> e:Expr -> b:BType -> b':BType
                -> ProofOf(HasBType g e (BTFunc b b')) 
                -> e':Expr -> ProofOf(HasBType g e' b) 
                -> ProofOf(HasBType g (App e e') b')
 |  BTLet  :: g:BEnv -> e_x:Expr -> b:BType -> ProofOf(HasBType g e_x b)
                -> x:Vname -> e:Expr -> b':BType 
                -> { y:Vname | not (in_envB y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasBType (BCons y b g) (unbind x y e) b')
                -> ProofOf(HasBType g (Let x e_x e) b')
 |  BTAnn  :: g:BEnv -> e:Expr -> b:BType 
                -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsB g) }
                -> ProofOf(HasBType g e b) -> ProofOf(HasBType g (Annot e t1) b)  @-} 

-- TODO: refactor without impossible
{-@ simpleBTVar :: g:BEnv -> { x:Vname | in_envB x g} -> { t:BType | bound_inB x t g } 
                -> ProofOf(HasBType g (FV x) t) @-}
simpleBTVar :: BEnv -> Vname -> BType -> HasBType
simpleBTVar BEmpty        x t = impossible "certainly"
simpleBTVar (BCons y s g) x t 
    = case (x == y, t == s) of
        (True, True) -> BTVar1 g x t
        (True, _)    -> impossible "again"
        (False, _)   -> BTVar2 g x t (simpleBTVar g x t) y s

-- Lemma. The underlying bare type system is sound. Omitting, for now, the textbook
--          soundness proof for the STLC.
{-@ assume lemma_soundness :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> b:BType
                   -> ProofOf(HasBType BEmpty e b) -> ProofOf(HasBType BEmpty e' b) @-}
lemma_soundness :: Expr -> Expr -> EvalsTo -> BType -> HasBType -> HasBType
lemma_soundness e e' p_ee' b p_eb = undefined

-- Lemma. All free variables in a (bare) typed expression are bound in the (bare) environment
{-@ lem_fv_bound_in_benv :: g:BEnv -> e:Expr -> t:BType -> ProofOf(HasBType g e t)
                -> { x:Vname | not (in_envB x g) }
                -> { pf:_ | not (Set_mem x (fv e)) } @-}
lem_fv_bound_in_benv :: BEnv -> Expr -> BType -> HasBType -> Vname -> Proof
lem_fv_bound_in_benv g e t (BTBC _g b) x      = ()
lem_fv_bound_in_benv g e t (BTIC _g n) x      = ()
lem_fv_bound_in_benv g e t (BTVar1 _ y _t) x  = ()
lem_fv_bound_in_benv g e t (BTVar2 _ y _t p_y_t z t') x = ()
lem_fv_bound_in_benv g e t (BTPrm _g c) x     = ()
lem_fv_bound_in_benv g e t (BTAbs _g y t_y e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_benv (BCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_benv g e t (BTApp _g e1 t_y t' p_e1_tyt' e2 p_e2_ty) x 
    = () ? lem_fv_bound_in_benv g e1 (BTFunc t_y t') p_e1_tyt' x
         ? lem_fv_bound_in_benv g e2 t_y p_e2_ty x
lem_fv_bound_in_benv g e t (BTLet _g e_y t_y p_ey_ty y e' t' y' p_e'_t') x 
    = case ( x == y' ) of
        (True)  -> () ? lem_fv_bound_in_benv g e_y t_y p_ey_ty x
        (False) -> () ? lem_fv_bound_in_benv g e_y t_y p_ey_ty x
                      ? lem_fv_bound_in_benv (BCons y' t_y g) (unbind y y' e') t' p_e'_t' x
lem_fv_bound_in_benv g e t (BTAnn _g e' _t ann_t p_e'_t) x 
    = () ? lem_fv_bound_in_benv g e' t p_e'_t x


  --- Well-Formedness of Types

data WFTypeP where
    WFType :: Env -> Type -> WFTypeP

data WFType where 
    WFRefn :: Env -> Vname -> Base -> Pred -> Vname -> HasBType -> WFType
    WFFunc :: Env -> Vname -> Type -> WFType -> Type -> Vname -> WFType -> WFType
    WFExis :: Env -> Vname -> Type -> WFType -> Type -> Vname -> WFType -> WFType

{-@ data WFType where
    WFRefn :: g:Env -> x:Vname -> b:Base -> p:Pred 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) }
        -> ProofOf(HasBType (BCons y (BTBase b) (erase_env g)) (unbind x y p) (BTBase TBool)) 
        -> ProofOf(WFType g (TRefn b x p))
 |  WFFunc :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> t:Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TFunc x t_x t))
 |  WFExis :: g:Env -> x:Vname -> t_x:Type 
        -> ProofOf(WFType g t_x) -> t:Type 
        -> { y:Vname | not (in_env y g) && not (Set_mem y (free t)) }
        -> ProofOf(WFType (Cons y t_x g) (unbindT x y t)) -> ProofOf(WFType g (TExists x t_x t)) @-} 


{-@ lem_free_bound_in_env :: g:Env -> t:Type -> ProofOf(WFType g t)
                -> { x:Vname | not (in_env x g) }
                -> { pf:_ | not (Set_mem x (free t)) } @-}
lem_free_bound_in_env :: Env -> Type -> WFType -> Vname -> Proof
lem_free_bound_in_env g t (WFRefn _g z b p z' p_z'_p_bl) x
    = case ( x == z' ) of
        (True)  -> ()
        (False) -> () ? lem_fv_bound_in_benv (BCons z' (BTBase b) (erase_env g)) 
                                             (unbind z z' p) (BTBase TBool) p_z'_p_bl x
lem_free_bound_in_env g t (WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf) x
    = case ( x == y' ) of
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x
lem_free_bound_in_env g t (WFExis _g y t_y p_ty_wf t' y' p_y'_t'_wf) x
    = case ( x == y' ) of 
        (True)  -> () ? lem_free_bound_in_env g t_y p_ty_wf x
        (False) -> () ? lem_free_bound_in_env g t_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf x
 

  --- Well-formedness of Environments
data WFEnvP where
    WFEnv :: Env -> WFEnvP

data WFEnv where
    WFEEmpty :: WFEnv
    WFEBind  :: Env -> WFEnv -> Vname -> Type -> WFType -> WFEnv

{-@ data WFEnv where
    WFEEmpty :: ProofOf(WFEnv Empty)
 |  WFEBind  :: g:Env -> ProofOf(WFEnv g) -> { x:Vname | not (in_env x g) } -> t:Type 
                      -> ProofOf(WFType g t) -> ProofOf(WFEnv (Cons x t g)) @-}


{-@ lookup_wftype_in_env :: g:Env -> ProofOf(WFEnv g) -> x:Vname -> { t:Type | bound_in x t g }
        -> (Env,WFType)<{\g' pf -> not (in_env x g') && propOf pf == WFType g' t}> @-}
lookup_wftype_in_env :: Env -> WFEnv -> Vname -> Type -> (Env, WFType)
lookup_wftype_in_env g (WFEBind g' p_wf_g' y t_y p_wf_ty) x t
  = case (x == y) of
      (True)  -> (g', p_wf_ty)
      (False) -> lookup_wftype_in_env g' p_wf_g' x t

  --- the Typing Judgement

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where -- TODO: Indicate in notes/latex where well-formedness used
    TBC   :: Env -> Bool -> HasType
    TIC   :: Env -> Int -> HasType
    TVar1 :: Env -> Vname -> Type -> HasType
    TVar2 :: Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TPrm  :: Env -> Prim -> HasType
    TAbs  :: Env -> Vname -> Type -> WFType -> Expr -> Type 
              -> Vname -> HasType -> HasType
    TApp  :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TLet  :: Env -> Expr -> Type -> HasType -> Vname -> Expr
              -> Type -> WFType -> Vname -> HasType -> HasType
    TAnn  :: Env -> Expr -> Type -> HasType -> HasType
    TSub  :: Env -> Expr -> Type -> HasType -> Type -> WFType -> Subtype -> HasType

{-@ data HasType where
    TBC   :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (tybc b))
 |  TIC   :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (tyic n))
 |  TVar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t:Type 
                -> ProofOf(HasType (Cons x t g) (FV x) t)
 |  TVar2 :: g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOf(HasType g (FV x) t)
                -> { y:Vname | y != x && not (in_env y g) && not (Set_mem y (free t)) } -> s:Type 
                -> ProofOf(HasType (Cons y s g) (FV x) t)
 |  TPrm  :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty c))
 |  TAbs  :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) 
                -> e:Expr -> t:Type 
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) } 
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
 |  TApp  :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                -> ProofOf(HasType g e (TFunc x t_x t)) 
                -> e':Expr -> ProofOf(HasType g e' t_x) 
                -> ProofOf(HasType g (App e e') (TExists x t_x t))
 |  TLet  :: g:Env -> e_x:Expr -> t_x:Type -> ProofOf(HasType g e_x t_x)
                -> x:Vname -> e:Expr -> t:Type -> ProofOf(WFType g t)
                -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) &&
                                                   not (Set_mem y (free t)) }
                -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                -> ProofOf(HasType g (Let x e_x e) t)
 |  TAnn  :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                -> ProofOf(HasType g (Annot e t) t)
 |  TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type 
                -> ProofOf(WFType g t) -> ProofOf(Subtype g s t) 
                -> ProofOf(HasType g e t) @-} -- @-}

{-@ lem_freeBV_unbind_empty :: x:Vname -> y:Vname -> { e:Expr | Set_emp (freeBV (unbind x y e)) }
	-> { pf:_ | Set_emp (freeBV e) || freeBV e == Set_sng x } @-}
lem_freeBV_unbind_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBV_unbind_empty x y e = toProof ( S.empty === freeBV (unbind x y e)
                                      === S.difference (freeBV e) (S.singleton x) )

-- Lemma. If G |- e : t, then Set_emp (freeBV e)
{-@ lem_freeBV_empty :: g:Env -> e:Expr -> t:Type -> ProofOf(HasType g e t)
                              -> { pf:_ | Set_emp (freeBV e) } @-}
lem_freeBV_empty :: Env -> Expr -> Type -> HasType -> Proof
lem_freeBV_empty g e t (TBC _g b)    = ()
lem_freeBV_empty g e t (TIC _g n)    = ()
lem_freeBV_empty g e t (TVar1 _ x _) = ()
lem_freeBV_empty g e t (TVar2 g' x _ p_x_t y s) 
    = () ? lem_freeBV_empty g' e t p_x_t 
lem_freeBV_empty g e t (TPrm _g c)   = ()
lem_freeBV_empty g e t (TAbs _g x t_x p_g_tx e' t' y p_yg_e'_t') 
    | freeBV e' ==  (S.empty)       =  () ? lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t')
    | freeBV e' ==  (S.singleton x) =  () ? lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t')
    | otherwise                     =  impossible ( "lol" ? lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t')
                                              ? lem_freeBV_unbind_empty x y e')
lem_freeBV_empty g e t (TApp _g e' x t_x t' p_e'_txt' e_x p_ex_tx) 
    = () ? lem_freeBV_empty g e' (TFunc x t_x t') p_e'_txt'
         ? lem_freeBV_empty g e_x t_x p_ex_tx
lem_freeBV_empty g e t (TLet _g e_x t_x p_ex_tx x e' t' p_g_t' y p_yg_e'_t') 
    = () ? lem_freeBV_empty (Cons y t_x g) (unbind x y e') (unbindT x y t')
         ? lem_freeBV_empty g e_x t_x p_ex_tx
         ? lem_freeBV_unbind_empty x y e'
lem_freeBV_empty g e t (TAnn _g e' _ p_e'_t) 
    = () ? lem_freeBV_empty g e' t p_e'_t
lem_freeBV_empty g e t (TSub _g _e s p_e_s _t p_g_t p_s_t) 
    = () ? lem_freeBV_empty g e s p_e_s


{-- TODO: refactor without impossible
{-@ simpleTVar :: g:Env -> { x:Vname | in_env x g } -> { t:Type | bound_in x t g } 
                -> ProofOf(HasType g (FV x) t) @-}
simpleTVar :: Env -> Vname -> Type -> HasType
simpleTVar Empty        x t = impossible "Clearly"
simpleTVar (Cons y s g) x t 
    = case (x == y, t == s) of
        (True, True) -> TVar1 g x t
        (True, _)    -> impossible "again"
        (False, _)   -> TVar2 g x t (simpleTVar g x t) y s
-}

-------------------------------------------------------------------------
----- |
-------------------------------------------------------------------------

{-@ reflect tybc @-} -- Refined Constant Typing
tybc :: Bool -> Type
tybc True  = TRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc True))
tybc False = TRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc False))

{-@ reflect tyic @-}
tyic :: Int -> Type
tyic n = TRefn TInt 1 (App (App (Prim Eq) (BV 1)) (Ic n))

{-@ reflect refn_pred @-} -- 
refn_pred :: Prim -> Pred
refn_pred And      = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim And) (FV 1)) (FV 2)) 
refn_pred Or       = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim Or) (FV 1)) (FV 2)) 
refn_pred Not      = App (App (Prim Eqv) (FV 3)) 
                           (App (Prim Not) (FV 1)) 
refn_pred Eqv      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (FV 1)) (FV 2)))
                                    (App (App (Prim And) (App (Prim Not) (FV 1)))
                                         (App (Prim Not) (FV 2))))
refn_pred Leq      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Leq) (FV 1)) (FV 2)) 
refn_pred (Leqn n) = App (App (Prim Eqv) (FV 3))
                           (App (App (Prim Leq) (Ic n)) (FV 2)) 
refn_pred Eq       = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Eq) (FV 1)) (FV 2))
refn_pred (Eqn n)  = App (App (Prim Eqv) (FV 3))
                           (App (App (Prim Eq) (Ic n)) (FV 2))

{-@ reflect ty @-} -- Primitive Typing
ty :: Prim -> Type
ty And      = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TFunc 2 (TRefn TBool 5 (Bc True)) 
                      (TRefn TBool 3 
                          (App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim And) (BV 1)) (BV 2)) )))
ty Or       = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TFunc 2 (TRefn TBool 5 (Bc True)) 
                      (TRefn TBool 3 
                          (App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim Or) (BV 1)) (BV 2)) )))
ty Not      = TFunc 1 (TRefn TBool 4 (Bc True)) 
                  (TRefn TBool 3
                      (App (App (Prim Eqv) (BV 3)) 
                           (App (Prim Not) (BV 1)) ))
ty Eqv      = TFunc 1 (TRefn TBool 4 (Bc True))
                  (TFunc 2 (TRefn TBool 5 (Bc True))  
                      (TRefn TBool 3
                          (App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (BV 1)) (BV 2)))
                                    (App (App (Prim And) (App (Prim Not) (BV 1)))
                                         (App (Prim Not) (BV 2)))))))
ty Leq      = TFunc 1 (TRefn TInt 4 (Bc True)) 
                  (TFunc 2 (TRefn TInt 5 (Bc True)) 
                      (TRefn TBool 3
                          (App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (BV 1)) (BV 2)) )))
ty (Leqn n) = TFunc 2 (TRefn TInt 5 (Bc True)) 
                  (TRefn TBool 3
                      (App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Leq) (Ic n)) (BV 2)) )) 
ty Eq       = TFunc 1 (TRefn TInt 4 (Bc True)) 
                  (TFunc 2 (TRefn TInt 5 (Bc True)) 
                      (TRefn TBool 3
                          (App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (BV 1)) (BV 2)) )))
ty (Eqn n)  = TFunc 2 (TRefn TInt 5 (Bc True)) 
                  (TRefn TBool 3
                      (App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Eq) (Ic n)) (BV 2)) ))

------------------------------------------------------------------------------
----- | SUBTYPING
------------------------------------------------------------------------------

data SubtypeP where
    Subtype :: Env -> Type -> Type -> SubtypeP

data Subtype where
    SBase :: Env -> Vname -> Base -> Pred -> Vname -> Pred -> Vname -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Vname -> Subtype -> Subtype
    SWitn :: Env -> Expr -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> Type -> Type -> Vname -> Subtype -> Subtype

{-@ data Subtype where
    SBase :: g:Env -> v1:Vname -> b:Base -> p1:Pred -> v2:Vname -> p2:Pred 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
               -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind v2 y p2))
               -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
 |  SFunc :: g:Env -> x1:Vname -> s1:Type -> { x2:Vname | not (in_env x2 g) } -> s2:Type
               -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t1)) 
                                               && not (Set_mem y (free t2)) }
               -> ProofOf(Subtype (Cons y s2 g) (unbindT x1 y t1) (unbindT x2 y t2))
               -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
 |  SWitn :: g:Env -> e:Value  -> t_x:Type -> ProofOf(HasType g e t_x) 
               -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubBV x e t'))
               -> ProofOf(Subtype g t (TExists x t_x t'))
 |  SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (free t')} 
               -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                               && not (Set_mem y (free t')) }
               -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
               -> ProofOf(Subtype g (TExists x t_x t) t')
@-} -- TODO remove the req that x \not\in free(t')

{-@ assume lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> { pf:_ | erase t1 == erase t2 } @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> Proof
lem_erase_subtype g t1 t2 p_t1_t2 = undefined
{-lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = ()
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
    = () ? lem_erase_subtype g s2 s1 p_s2_s1
         ? lem_erase_subtype (Cons y s2 g) t1' t2' p_t1'_t2'
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
    = toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t')
            === erase t' === erase t2 )
--    = () ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
    = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
-}


-------------------------------------------------------------------------
----- | CLOSING SUBSTITUTIONS and DENOTATIONAL SEMANTICS 
-------------------------------------------------------------------------

-- closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
--   the typing env downwards/leftwards

data CSubst = CEmpty
            | CCons Vname Expr CSubst
{-@ data CSubst  where
    CEmpty :: CSubst
  | CCons  :: x:Vname -> v:Value -> th:CSubst -> CSubst @-}

{-@ reflect bindsC @-}
bindsC :: CSubst -> S.Set Vname
bindsC CEmpty         = S.empty
bindsC (CCons x v th) = S.union (S.singleton x) (bindsC th)

{-@ measure uniqueC @-}
uniqueC :: CSubst -> Bool
uniqueC CEmpty         = True
uniqueC (CCons x v th) = (uniqueC th) && not (S.member x (bindsC th))

{-@ reflect csubst @-}
csubst :: CSubst -> Expr -> Expr
csubst CEmpty         e = e
csubst (CCons x v th) e = csubst th (subFV x v e)

-- Idea: ctsubst th t = foldr (\(x,e) t' -> tsubFV x e t') t th 
{-@ reflect ctsubst @-}
ctsubst :: CSubst -> Type -> Type
ctsubst CEmpty         t = t
ctsubst (CCons x v th) t = ctsubst th (tsubFV x v t)

  --- various distributive properties of csubst and ctsubst

{-@ assume lem_csubst_bc :: th:CSubst -> b:Bool -> { pf:_ | csubst th (Bc b) == Bc b } @-}
lem_csubst_bc :: CSubst -> Bool -> Proof
lem_csubst_bc th b = undefined

{-@ assume lem_csubst_ic :: th:CSubst -> n:Int -> { pf:_ | csubst th (Ic n) == Ic n } @-}
lem_csubst_ic :: CSubst -> Int -> Proof
lem_csubst_ic th n = undefined

{-@ assume lem_csubst_prim :: th:CSubst -> c:Prim -> { pf:_ | csubst th (Prim c) == Prim c } @-}
lem_csubst_prim :: CSubst -> Prim -> Proof
lem_csubst_prim th c = undefined

{-@ assume lem_csubst_nofv :: th:CSubst -> { e:Expr | Set_emp (fv e) }
        -> { pf:_ | csubst th e == e } @-}
lem_csubst_nofv :: CSubst -> Expr -> Proof
lem_csubst_nofv th e = undefined
--lem_csubst_nofv (CEmpty)       e = ()
--lem_csubst_nofv (CCons x v th) e = () ? lem_csubst_nofv th e

{-@ assume lem_ctsubst_nofree :: th:CSubst -> { t:Type | Set_emp (free t) }
        -> { pf:_ | ctsubst th t == t } @-}
lem_ctsubst_nofree :: CSubst -> Type -> Proof
lem_ctsubst_nofree th t = undefined
--lem_ctsubst_nofree (CEmpty)       t = ()
--lem_ctsubst_nofree (CCons x v th) t = () ? lem_ctsubst_nofree th t

{-@ lem_csubst_value :: th:CSubst -> v:Value  
        -> { pf:_ | isValue (csubst th v) && Set_emp (freeBV (csubst th v)) } @-}
lem_csubst_value :: CSubst -> Expr -> Proof
lem_csubst_value (CEmpty)         v = ()
lem_csubst_value (CCons y v_y th) v = () ? lem_csubst_value th (subFV y v_y v)

{-@ lem_ctsubst_head_not_free :: x:Vname -> v_x:Value -> th:CSubst 
        -> { t:Type | not (Set_mem x (free t)) } 
        -> { pf:_ | ctsubst (CCons x v_x th) t == ctsubst th t } @-}
lem_ctsubst_head_not_free :: Vname -> Expr -> CSubst -> Type -> Proof
lem_ctsubst_head_not_free x v_x th t = toProof ( ctsubst (CCons x v_x th) t
                                             === ctsubst th (tsubFV x v_x t)
                                             === ctsubst th t )

{-@ assume lem_csubst_app :: th:CSubst -> e:Expr -> e':Expr 
               -> { pf:_ | csubst th (App e e') == App (csubst th e) (csubst th e') } @-}
lem_csubst_app :: CSubst -> Expr -> Expr -> Proof
lem_csubst_app th e e' = undefined

{-@ lem_ctsubst_refn :: th:CSubst -> b:Base -> x:Vname -> p:Expr
               -> { pf:_ | ctsubst th (TRefn b x p) == TRefn b x (csubst th p) } @-}
lem_ctsubst_refn :: CSubst -> Base -> Vname -> Expr -> Proof
lem_ctsubst_refn (CEmpty)       b x p = ()
lem_ctsubst_refn (CCons y v th) b x p = toProof ( ctsubst (CCons y v th) (TRefn b x p)
                                              === ctsubst th (tsubFV y v (TRefn b x p))
                                              === ctsubst th (TRefn b x (subFV y v p))
                                                ? lem_ctsubst_refn th b x (subFV y v p)
                                              === TRefn b x (csubst th (subFV y v p)) 
                                              === TRefn b x (csubst (CCons y v th) p) )

{-@ lem_ctsubst_func :: th:CSubst -> x:Vname -> t_x:Type -> t:Type
        -> { pf:_ | ctsubst th (TFunc x t_x t) == TFunc x (ctsubst th t_x) (ctsubst th t) } @-}  
lem_ctsubst_func :: CSubst -> Vname -> Type -> Type -> Proof
lem_ctsubst_func (CEmpty)       x t_x t = ()
lem_ctsubst_func (CCons y v th) x t_x t 
    = () ? lem_ctsubst_func th x (tsubFV y v t_x) (tsubFV y v t) 

{-@ lem_ctsubst_exis :: th:CSubst -> x:Vname -> t_x:Type -> t:Type
        -> {pf:_ | ctsubst th (TExists x t_x t) == TExists x (ctsubst th t_x) (ctsubst th t)} @-}  
lem_ctsubst_exis :: CSubst -> Vname -> Type -> Type -> Proof
lem_ctsubst_exis (CEmpty)       x t_x t = ()
lem_ctsubst_exis (CCons y v th) x t_x t 
    = () ? lem_ctsubst_exis th x (tsubFV y v t_x) (tsubFV y v t) 

{-@ lem_csubst_subBV :: x:Vname -> v:Value -> b:Base 
           -> ProofOf(HasBType BEmpty v (BTBase b)) -> th:CSubst -> p:Expr
           -> { pf:_ | csubst th (subBV x v p) == subBV x v (csubst th p) } @-}
lem_csubst_subBV :: Vname -> Expr -> Base -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_subBV x v b pf_v_b (CEmpty)         p = ()
lem_csubst_subBV x v b pf_v_b (CCons y v_y th) p 
    = () ? lem_commute_subFV_subBV1 x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v (BTBase b) pf_v_b y) v_y p
         ? lem_csubst_subBV x v b pf_v_b th (subFV y v_y p)

{-@ lem_ctsubst_tsubBV1 :: x:Vname -> v:Value -> bt:BType
           -> ProofOf(HasBType BEmpty v bt) -> th:CSubst -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_tsubBV1 :: Vname -> Expr -> BType -> HasBType -> CSubst -> Type -> Proof
lem_ctsubst_tsubBV1 x v bt pf_v_b (CEmpty)         t = ()
lem_ctsubst_tsubBV1 x v bt pf_v_b (CCons y v_y th) t 
    = () ? lem_commute_tsubFV_tsubBV1 x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v bt pf_v_b y) v_y t
         ? lem_ctsubst_tsubBV1 x v bt pf_v_b th (tsubFV y v_y t)

{-@ lem_csubst_and_unbind :: x:Vname -> y:Vname 
           -> v:Value -> b:Base -> ProofOf(HasBType BEmpty v (BTBase b))
           -> th:CSubst -> { p:Expr | not (Set_mem y (fv p)) }
           -> { pf:_ | csubst (CCons y v th) (unbind x y p) == subBV x v (csubst th p) } @-}
lem_csubst_and_unbind :: Vname -> Vname -> Expr -> Base -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_and_unbind x y v b pf_v_b th p = toProof ( csubst (CCons y v th) (unbind x y p)
                                                  === csubst th (subFV y v (unbind x y p))
                                                    ? lem_subFV_unbind x y v p
                                                  === csubst th (subBV x v p)
                                                    ? lem_csubst_subBV x v b pf_v_b th p
                                                  === subBV x v (csubst th p) )

{-@ lem_ctsubst_and_unbindT :: x:Vname -> y:Vname
           -> v:Value -> bt:BType -> ProofOf(HasBType BEmpty v bt)
           -> th:CSubst -> { t:Type | not (Set_mem y (free t)) }
           -> { pf:_ | ctsubst (CCons y v th) (unbindT x y t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_and_unbindT :: Vname -> Vname -> Expr -> BType -> HasBType 
           -> CSubst -> Type -> Proof
lem_ctsubst_and_unbindT x y v bt pf_v_b th t = toProof ( ctsubst (CCons y v th) (unbindT x y t)
                                                   === ctsubst th (tsubFV y v (unbindT x y t))
                                                     ? lem_tsubFV_unbindT x y v t
                                                   === ctsubst th (tsubBV x v t)
                                                     ? lem_ctsubst_tsubBV1 x v bt pf_v_b th t
                                                   === tsubBV x v (ctsubst th t) )

{-@ lem_commute_ctsubst_tsubBV :: th:CSubst -> x:Vname -> v:Value -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x (csubst th v) (ctsubst th t) } @-} 
lem_commute_ctsubst_tsubBV :: CSubst -> Vname -> Expr -> Type -> Proof
lem_commute_ctsubst_tsubBV (CEmpty)         x v t = () 
lem_commute_ctsubst_tsubBV (CCons y v_y th) x v t 
    = () ? lem_commute_tsubFV_tsubBV x v y v_y t
         ? lem_commute_ctsubst_tsubBV th x (subFV y v_y v) (tsubFV y v_y t)

{-@ lem_erase_ctsubst :: th:CSubst -> t:Type 
               -> { pf:_ | erase (ctsubst th t) == erase t } @-}
lem_erase_ctsubst :: CSubst -> Type -> Proof
lem_erase_ctsubst (CEmpty)       t = ()
lem_erase_ctsubst (CCons y v th) t = toProof ( erase (ctsubst (CCons y v th) t)
                                           === erase (ctsubst th (tsubFV y v t))
                                             ? lem_erase_ctsubst th (tsubFV y v t)
                                           === erase (tsubFV y v t)
                                             ? lem_erase_tsubFV y v t
                                           === erase t )

{-@ lem_erase_th_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> th:CSubst -> { pf:_ | erase (ctsubst th t1) == erase (ctsubst th t2) } @-}
lem_erase_th_sub :: Env -> Type -> Type -> Subtype -> CSubst -> Proof
lem_erase_th_sub g t1 t2 p_t1_t2 th = toProof ( erase (ctsubst th t1) 
                                              ? lem_erase_ctsubst th t1
                                            === erase t1 ? lem_erase_subtype g t1 t2 p_t1_t2
                                            === erase t2 ? lem_erase_ctsubst th t2
                                            === erase (ctsubst th t2) )
                      
data EntailsP where
    Entails :: Env -> Pred -> EntailsP

data Entails where
    EntPred :: Env -> Pred -> (CSubst -> DenotesEnv -> EvalsTo) -> Entails

{-@ data Entails where
    EntPred :: g:Env -> p:Pred 
               -> (th:CSubst -> ProofOf(DenotesEnv g th) 
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

{- @ data Hex a b c d e f <p :: a -> b -> c -> d -> e -> f -> Bool>
       = Hex { in_cs :: a, in_exp :: b, in_typ :: c,
                 val :: d, evals :: e, den :: f<p in_cs in_exp in_typ val evals> } @-}
--data Hex a b c d e f = Hex { in_cs :: a,  in_exp :: b, in_typ :: c,
--                               val :: d, evals :: e, den :: f }

{- @ type ValueDenoted = Hex <{\th e t v pf_evl pf_den -> isValue v && Set_emp (freeBV v)
                                      && (propOf pf_evl == EvalsTo (csubst th e) v)
                                     && (propOf pf_den == Denotes (ctsubst th t) v) }>
                            CSubst Expr Type Expr EvalsTo Denotes @-}
--type ValueDenoted     = Hex CSubst Expr Type Expr EvalsTo Denotes
{-              -> ( v_x:Value -> ProofOf(Denotes t_x v_x)
                    -> (Value, (EvalsTo, Denotes))
                       <{\v' pfs -> (propOf (fst pfs) == EvalsTo (App v v_x) v')
                                 && (propOf (snd pfs) == Denotes (tsubBV x v_x t) v')}>) -}

data DenotesP where 
    Denotes :: Type -> Expr -> DenotesP    -- e \in [[t]]

data Denotes where
    DRefn :: Base -> Vname -> Pred -> Expr -> HasBType -> EvalsTo -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasBType
              -> (Expr -> Denotes -> ValueDenoted) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasBType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
    DRefn :: b:Base -> x:Vname -> p:Pred -> v:Value  
              -> ProofOf(HasBType BEmpty v (BTBase b))
              -> ProofOf(EvalsTo (subBV x v p) (Bc True)) 
              -> ProofOf(Denotes (TRefn b x p) v)
  | DFunc :: x:Vname -> t_x:Type -> t:Type -> v:Value  
              -> ProofOf(HasBType BEmpty v (erase (TFunc x t_x t)))
              -> ( v_x:Value -> ProofOf(Denotes t_x v_x)
                             -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x t)) ) 
              -> ProofOf(Denotes (TFunc x t_x t) v)
  | DExis :: x:Vname -> t_x:Type -> t:Type -> v:Value 
              -> ProofOf(HasBType BEmpty v (erase t)) 
              -> v_x:Value -> ProofOf(Denotes t_x v_x)
              -> ProofOf(Denotes (tsubBV x v_x t) v)
              -> ProofOf(Denotes (TExists x t_x t) v)  @-} -- @-}

{-@ lem_den_nofv1 :: v:Value -> t:Type -> ProofOf(Denotes t v) ->  x:Vname 
        -> { pf:_ | not (Set_mem x (fv v)) }  @-}
lem_den_nofv1 :: Expr -> Type -> Denotes -> Vname -> Proof
lem_den_nofv1 v t den_t_v x = lem_fv_bound_in_benv BEmpty v (erase t) pf_v_bt x
  where
    pf_v_bt = get_btyp_from_den t v den_t_v

{-@ assume lem_den_nofv :: v:Value -> t:Type -> ProofOf(Denotes t v) 
        -> { pf:_ | Set_emp (fv v) } @-}
lem_den_nofv :: Expr -> Type -> Denotes -> Proof
lem_den_nofv v t den_t_v = undefined  

  --- helper functions to avoid deeply nested pattern matching

{-@ get_btyp_from_den :: t:Type -> v:Value -> ProofOf(Denotes t v)
              -> ProofOf(HasBType BEmpty v (erase t)) @-}
get_btyp_from_den :: Type -> Expr -> Denotes -> HasBType    
get_btyp_from_den t v (DRefn _ _ _ _ pf_v_b _)     = pf_v_b
get_btyp_from_den t v (DFunc _ _ _ _ pf_v_b _)     = pf_v_b
get_btyp_from_den t v (DExis _ _ _ _ pf_v_b _ _ _) = pf_v_b

{-@ get_obj_from_dfunc :: x:Vname -> s:Type -> t:Type -> v:Value 
        -> ProofOf(Denotes (TFunc x s t) v) -> v':Value 
        -> ProofOf(Denotes s v') -> ProofOf(ValueDenoted (App v v') (tsubBV x v' t)) @-}  
get_obj_from_dfunc :: Vname -> Type -> Type -> Expr -> Denotes 
                                    -> Expr -> Denotes -> ValueDenoted
get_obj_from_dfunc x s t v (DFunc _ _ _ _ _ prover) v' den_s_v' = prover v' den_s_v' 


{-      -> (Value, (EvalsTo, Denotes))<{\v'' pfs -> (propOf (fst pfs) == EvalsTo (App v v') v'')
                                            && (propOf (snd pfs) == Denotes (tsubBV x v' t) v'') }> @-}

-- Denotations of Environments, [[g]]. There are two cases:
--   1. [[ Empty ]] = { CEmpty }.
--   2. [[ Cons x t g ]] = { CCons x v_x th | Denotes th(t) v_x && th \in [[ g ]] }
data DenotesEnvP where 
    DenotesEnv :: Env -> CSubst -> DenotesEnvP 

data DenotesEnv where
    DEmp :: DenotesEnv
    DExt :: Env -> CSubst -> DenotesEnv -> Vname -> Type -> Expr 
               -> Denotes -> DenotesEnv
{-@ data DenotesEnv where 
    DEmp :: ProofOf(DenotesEnv Empty CEmpty)
 |  DExt :: g:Env -> th:CSubst -> ProofOf(DenotesEnv g th) 
               -> { x:Vname | not (in_env x g) } -> t:Type 
               -> v:Value -> ProofOf(Denotes (ctsubst th t) v)
               -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}

