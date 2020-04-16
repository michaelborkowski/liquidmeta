{-# LANGUAGE GADTs #-}

{-  @ LIQUID "--no-termination" @-}
{-  @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module WellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Syntax
import Environments
import Semantics
import BareTyping

-- we must force these into scope for LH
semantics = (Step, EvalsTo)
typing = (HasBType)

-----------------------------------------------------------------------------
----- | JUDGEMENTS : WELL-FORMEDNESS of TYPES and ENVIRONMENTS
-----------------------------------------------------------------------------

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
{-
{-@ reflect isWellFormed @-}
isWellFormed :: Env -> Type -> Bool
isWellFormed g (TRefn b x p)     = isBTyped (BCons y (BTBase b) (erase_env g)) (unbind x y p) (BTBase TBool)
  where
    y = fresh_var g
isWellFormed g (TFunc x t_x t)   = isWellFormed g t_x && isWellFormed (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g
isWellFormed g (TExists x t_x t) = isWellFormed g t_x && isWellFormed (Cons y t_x g) (unbindT x y t)
  where
    y = fresh_var g

{-@ makeWFType :: g:Env -> { t:Type | isWellFormed g t } -> ProofOf(WFType g t) @-}
makeWFType :: Env -> Type -> WFType
makeWFType g (TRefn b x p)     = WFRefn g x b p y (makeHasBType (BCons y (BTBase b) (erase_env g)) 
                                        (unbind x y p) (BTBase TBool))
  where
    y = fresh_var g
makeWFType g (TFunc x t_x t)   = WFFunc g x t_x (makeWFType g t_x) t y 
                                        (makeWFType (Cons y t_x g) (unbindT x y t))
  where
    y = fresh_var g
makeWFType g (TExists x t_x t) = WFExis g x t_x (makeWFType g t_x) t y 
                                        (makeWFType (Cons y t_x g) (unbindT x y t))
  where
    y = fresh_var g
-}
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

{-@ lem_free_subset_binds :: g:Env -> t:Type -> ProofOf(WFType g t)  
                  -> { pf:_ | Set_sub (free t) (binds g) } @-}
lem_free_subset_binds :: Env -> Type -> WFType -> Proof 
lem_free_subset_binds g t (WFRefn _g z b p z' p_z'_p_bl)
    = () ? lem_fv_subset_bindsB (BCons z' (BTBase b) (erase_env g)) (unbind z z' p) 
                                (BTBase TBool) p_z'_p_bl
lem_free_subset_binds g t (WFFunc _g y t_y p_ty_wf t' y' p_y'_t'_wf)
    = () ? lem_free_subset_binds g t_y p_ty_wf
         ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf
lem_free_subset_binds g t (WFExis _g y t_y p_ty_wf t' y' p_y'_t'_wf)
    = () ? lem_free_subset_binds g t_y p_ty_wf
         ? lem_free_subset_binds (Cons y' t_y g) (unbindT y y' t') p_y'_t'_wf

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

{-@ lem_truncate_wfenv :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> ProofOf(WFEnv g) @-}
lem_truncate_wfenv :: Env -> Env -> WFEnv -> WFEnv
lem_truncate_wfenv g Empty         p_g_wf    = p_g_wf          
lem_truncate_wfenv g (Cons x v g') p_xg'g_wf = lem_truncate_wfenv g g' p_g'g_wf
  where
    (WFEBind _ p_g'g_wf _ _ _) = p_xg'g_wf 

-------------------------------------------------------------------------
----- | CLOSING SUBSTITUTIONS 
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

{-@ reflect concatCS @-}
concatCS :: CSubst -> CSubst -> CSubst
concatCS th CEmpty          = th
concatCS th (CCons x v th') = CCons x v (concatCS th th')

  --- various distributive properties of csubst and ctsubst

{-@ lem_csubst_bc :: th:CSubst -> b:Bool -> { pf:_ | csubst th (Bc b) == Bc b } @-}
lem_csubst_bc :: CSubst -> Bool -> Proof
lem_csubst_bc (CEmpty)       b = ()
lem_csubst_bc (CCons x v th) b = () ? lem_csubst_bc th b

{-@ lem_csubst_ic :: th:CSubst -> n:Int -> { pf:_ | csubst th (Ic n) == Ic n } @-}
lem_csubst_ic :: CSubst -> Int -> Proof
lem_csubst_ic (CEmpty)       n = ()
lem_csubst_ic (CCons x v th) n = () ? lem_csubst_ic th n

{-@ lem_csubst_prim :: th:CSubst -> c:Prim -> { pf:_ | csubst th (Prim c) == Prim c } @-}
lem_csubst_prim :: CSubst -> Prim -> Proof
lem_csubst_prim (CEmpty)       c = ()
lem_csubst_prim (CCons x v th) c = () ? lem_csubst_prim th c

{-@ lem_csubst_lambda :: th:CSubst -> x:Vname 
        -> e:Expr -> { pf:_ | csubst th (Lambda x e) == Lambda x (csubst th e) } @-}
lem_csubst_lambda :: CSubst -> Vname -> Expr -> Proof
lem_csubst_lambda (CEmpty)       x e = ()
lem_csubst_lambda (CCons y v th) x e = () ? lem_csubst_lambda th x (subFV y v e)

{-@ lem_csubst_app :: th:CSubst -> e:Expr -> e':Expr 
               -> { pf:_ | csubst th (App e e') == App (csubst th e) (csubst th e') } @-}
lem_csubst_app :: CSubst -> Expr -> Expr -> Proof
lem_csubst_app (CEmpty)       e e' = ()
lem_csubst_app (CCons y v th) e e' = () ? lem_csubst_app th (subFV y v e) (subFV y v e')

{-@ lem_csubst_let :: th:CSubst -> x:Vname -> e_x:Expr -> e:Expr 
        -> { pf:_ | csubst th (Let x e_x e) == Let x (csubst th e_x) (csubst th e) } @-}
lem_csubst_let :: CSubst -> Vname -> Expr -> Expr -> Proof
lem_csubst_let (CEmpty)       x e_x e = ()
lem_csubst_let (CCons y v th) x e_x e = () ? lem_csubst_let th x (subFV y v e_x) (subFV y v e)

{-@ lem_csubst_annot :: th:CSubst -> e:Expr
        -> t:Type -> { pf:_ | csubst th (Annot e t) == Annot (csubst th e) (ctsubst th t) } @-}
lem_csubst_annot :: CSubst -> Expr -> Type -> Proof
lem_csubst_annot (CEmpty)       e t = ()
lem_csubst_annot (CCons y v th) e t = () ? lem_csubst_annot th (subFV y v e) (tsubFV y v t)

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


  --- Various properties of csubst/ctsubst and free/bound variables

{-@ lem_csubst_nofv :: th:CSubst -> { e:Expr | Set_emp (fv e) }
        -> { pf:_ | csubst th e == e } @-}
lem_csubst_nofv :: CSubst -> Expr -> Proof
lem_csubst_nofv (CEmpty)       e = ()
lem_csubst_nofv (CCons x v th) e = () ? lem_csubst_nofv th e
                                      ? toProof ( subFV x v e === e )

{-@ lem_ctsubst_nofree :: th:CSubst -> { t:Type | Set_emp (free t) }
        -> { pf:_ | ctsubst th t == t } @-}
lem_ctsubst_nofree :: CSubst -> Type -> Proof
lem_ctsubst_nofree (CEmpty)       t = ()
lem_ctsubst_nofree (CCons x v th) t = () ? lem_ctsubst_nofree th t
                                         ? toProof ( tsubFV x v t === t )

{-@ lem_csubst_freeBV :: th:CSubst -> e:Expr
        -> { pf:_ | freeBV (csubst th e) == freeBV e } @-}
lem_csubst_freeBV :: CSubst -> Expr -> Proof
lem_csubst_freeBV (CEmpty)       e = ()
lem_csubst_freeBV (CCons x v th) e = () ? lem_csubst_freeBV th (subFV x v e)
                         ? toProof ( freeBV (subFV x v e) === freeBV e )

{-@ lem_ctsubst_tfreeBV :: th:CSubst -> t:Type
        -> { pf:_ | tfreeBV (ctsubst th t) == tfreeBV t } @-}
lem_ctsubst_tfreeBV :: CSubst -> Type -> Proof
lem_ctsubst_tfreeBV (CEmpty)       t = ()
lem_ctsubst_tfreeBV (CCons x v th) t = () ? lem_ctsubst_tfreeBV th (tsubFV x v t)
                         ? toProof ( tfreeBV (tsubFV x v t) === tfreeBV t )

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

  --- Commutative laws relating csubst/ctsubst and subBV/tsubBV 

{-@ lem_csubst_subBV :: x:Vname -> v:Value -> bt:BType 
           -> ProofOf(HasBType BEmpty v bt) -> th:CSubst -> p:Expr
           -> { pf:_ | csubst th (subBV x v p) == subBV x v (csubst th p) } @-}
lem_csubst_subBV :: Vname -> Expr -> BType -> HasBType -> CSubst -> Expr -> Proof
lem_csubst_subBV x v bt pf_v_b (CEmpty)         p = ()
lem_csubst_subBV x v bt pf_v_b (CCons y v_y th) p 
    = () ? lem_commute_subFV_subBV1 x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v bt pf_v_b y) v_y p
         ? lem_csubst_subBV x v bt pf_v_b th (subFV y v_y p)

{-@ lem_ctsubst_tsubBV :: x:Vname -> v:Value -> bt:BType
           -> ProofOf(HasBType BEmpty v bt) -> th:CSubst -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_tsubBV :: Vname -> Expr -> BType -> HasBType -> CSubst -> Type -> Proof
lem_ctsubst_tsubBV x v bt pf_v_b (CEmpty)         t = ()
lem_ctsubst_tsubBV x v bt pf_v_b (CCons y v_y th) t 
    = () ? lem_commute_tsubFV_tsubBV1 x v 
                   (y `withProof` lem_fv_bound_in_benv BEmpty v bt pf_v_b y) v_y t
         ? lem_ctsubst_tsubBV x v bt pf_v_b th (tsubFV y v_y t)

{-@ lem_csubst_and_unbind :: x:Vname -> y:Vname 
           -> v:Value -> bt:BType -> ProofOf(HasBType BEmpty v bt)
           -> th:CSubst -> { p:Expr | not (Set_mem y (fv p)) }
           -> { pf:_ | csubst (CCons y v th) (unbind x y p) == subBV x v (csubst th p) } @-}
lem_csubst_and_unbind :: Vname -> Vname -> Expr -> BType -> HasBType -> CSubst -> Expr -> Proof
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
                                                     ? lem_ctsubst_tsubBV x v bt pf_v_b th t
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

