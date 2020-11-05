{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module LemmasWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing
import BasicPropsCSubst
import BasicPropsDenotes
import Entailments
import LemmasChangeVarWF
import LemmasWeakenWF

{-@ reflect foo34 @-}
foo34 x = Just x
foo34 :: a -> Maybe a

------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------

{-@ lem_selfify_wf :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k ) 
        -> { x:Vname | not (in_env x g) } -> ProofOf(WFType (Cons x t g) (self t (FV x) k) k) @-}
lem_selfify_wf :: Env -> Type -> Kind -> WFType -> Vname -> WFType
lem_selfify_wf g t@(TRefn b z p) k p_g_t x = case p_g_t of
  (WFBase _g b)                       -> case b of
    TBool -> undefined
    TInt  -> undefined 
  (WFRefn _g _z _b p_g_b _p  y pf_p_bl) -> case b of
    TBool -> undefined {- WFRefn g' z b p' w pf_p'_bl 
      where
        g'          = Cons x t g
        w           = fresh_var g' ? lem_free_subset_binds g t p_g_t
        g''         = BCons w (BTBase b) (erase_env g')
        pf_pw_bl    = lem_change_var_btyp (erase_env g) y (BTBase b) BEmpty (unbind z y p) (BTBase TBool) 
                                          pf_p_bl w ? lem_subFV_unbind z y (FV w) p
        pf_pwx_bl   = lem_weaken_btyp (erase_env g) (BCons w (BTBase b) BEmpty) (unbind z w p) (BTBase TBool)
                                          pf_pw_bl x (BTBase TBool) -- erase t
        p'          = App (App (Prim And) p) (App (App (Prim Eqv) (BV z)) (FV x))
        blbl        = BTFunc (BTBase TBool) (BTBase TBool)
        app_eqv1    = BTApp g'' (Prim Eqv) (BTBase TBool) blbl (BTPrm g'' Eqv) 
                            (FV w) (BTVar1 (erase_env g') w (BTBase b))
        app_eqv2    = BTApp g'' (App (Prim Eqv) (FV w)) (BTBase TBool) (BTBase TBool) app_eqv1
                            (FV x) (BTVar2 (erase_env g') x (BTBase TBool) 
                                           (BTVar1 (erase_env g) x (BTBase TBool)) w (BTBase b))
        app_and1    = BTApp g'' (Prim And) (BTBase TBool) blbl (BTPrm g'' And)
                            (unbind z w p) pf_pwx_bl
        {-@ pf_p'_bl :: ProofOf(HasBType g'' (unbind z w p') (BTBase TBool)) @-}
        pf_p'_bl    = BTApp g'' (App (Prim And) (unbind z w p)) (BTBase TBool) (BTBase TBool) app_and1
                            (App (App (Prim Eqv) (FV w)) (FV x)) app_eqv2
--                            ? lem_fv_subset_bindsB g'' (unbind z w  -}
    TInt  -> undefined {-WFRefn g' z b p' w pf_p'_bl
      where
        g'          = Cons x t g
        w           = fresh_var g' ? lem_free_subset_binds g t p_g_t
        g''         = BCons w (BTBase b) (erase_env g')
        pf_pw_bl    = lem_change_var_btyp (erase_env g) y (BTBase b) BEmpty (unbind z y p) (BTBase TBool) 
                                          pf_p_bl w ? lem_subFV_unbind z y (FV w) p
        pf_pwx_bl   = lem_weaken_btyp (erase_env g) (BCons w (BTBase b) BEmpty) (unbind z w p) (BTBase TBool)
                                          pf_pw_bl x (BTBase TInt) -- erase t
        p'          = App (App (Prim And) p) (App (App (Prim Eq) (BV z)) (FV x))
        blbl        = BTFunc (BTBase TBool) (BTBase TBool)
        intbl       = BTFunc (BTBase TInt) (BTBase TBool)
        app_eqv1    = BTApp g'' (Prim Eq) (BTBase TInt) intbl (BTPrm g'' Eq) 
                            (FV w) (BTVar1 (erase_env g') w (BTBase b))
        app_eqv2    = BTApp g'' (App (Prim Eq) (FV w)) (BTBase TInt) (BTBase TBool) app_eqv1
                            (FV x) (BTVar2 (erase_env g') x (BTBase TInt) 
                                           (BTVar1 (erase_env g) x (BTBase TInt)) w (BTBase b))
        app_and1    = BTApp g'' (Prim And) (BTBase TBool) blbl (BTPrm g'' And)
                            (unbind z w p) pf_pwx_bl
        {-@ pf_p'_bl :: ProofOf(HasBType g'' (unbind z w p') (BTBase TBool)) @-}
        pf_p'_bl    = BTApp g'' (App (Prim And) (unbind z w p)) (BTBase TBool) (BTBase TBool) app_and1
                            (App (App (Prim Eq) (FV w)) (FV x)) app_eqv2-}
    (FTV a) -> undefined
    (BTV a) -> undefined
  (WFVar1 {}) -> undefined
  (WFVar2 {}) -> undefined
  (WFVar3 {}) -> undefined
  (WFKind {}) -> undefined
lem_selfify_wf g t@(TExists z t_z t') k p_g_t x = undefined
lem_selfify_wf g t                    k p_g_t x = undefined -- lem_weaken_wf g Empty t k p_g_t x t 

{-
{-@ lem_push_wf :: g:Env -> g':Env -> t_a:Type -> k_a:Kind -> ProofOf(WFType g t_a k_a) -> x:Vname -> p:Pred
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> ProofOf(HasFType (FCons y (erase t_a) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(WFType g (push p t_a) k) @-}
-}

{-@ lem_push_wf :: g:Env -> t_a:Type -> k:Kind -> ProofOf(WFType g t_a k) 
        -> x:Vname -> { p:Pred | same_bindersE t_a p }
        -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p)) && not (Set_mem y (ftv p)) }
        -> ProofOf(HasFType (FCons y (erase t_a) (erase_env g)) (unbind x y p) (FTBasic TBool))
        -> ProofOf(WFType g (push p t_a) k) @-}
lem_push_wf :: Env -> Type -> Kind -> WFType -> Vname -> Expr -> Vname -> HasFType -> WFType
lem_push_wf g (TRefn   b z   r) k p_g_ta x p y p_yg_p_bl = undefined
lem_push_wf g (TFunc   z t_z t) k p_g_ta x p y p_yg_p_bl = undefined
lem_push_wf g (TExists z t_z t) k p_g_ta x p y p_yg_p_bl = undefined
lem_push_wf g (TPoly   a' k' t) k p_g_ta x p y p_yg_p_bl = undefined


{-@ lem_subtype_in_env_wf :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) }
      -> { x:Vname | (not (in_env x g)) && not (in_env x g') }
      -> s_x:Type -> t_x:Type -> ProofOf(Subtype g s_x t_x) -> t:Type -> k:Kind
      -> ProofOf(WFType (concatE (Cons x t_x g) g') t k)
      -> ProofOf(WFType (concatE (Cons x s_x g) g') t k) @-} 
lem_subtype_in_env_wf :: Env -> Env -> Vname -> Type -> Type -> Subtype -> Type -> Kind -> WFType -> WFType
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFBase env b)
    = WFBase (concatE (Cons x s_x g) g') b
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFRefn env z b p_env_b p z'_ p_z'env_p_bl) = undefined
{-    = WFRefn (concatE (Cons x s_x g) g') z b p_env'_b p z' p_z'env'_p_bl
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_z'env'_p_bl = p_z'env_p_bl ? lem_erase_concat (Cons x s_x g) g' -- (Cons z' (BTBase b) g')
                                       ? lem_erase_concat (Cons x t_x g) g' -- (Cons z' (BTBase b) g')
                                       ? lem_erase_subtype g s_x t_x p_sx_tx
          p_env'_b      = case b of 
            TBool    -> WFBase (concatE (Cons x s_x g) g') b
            TInt     -> WFBase (concatE (Cons x s_x g) g') b
            (FTV a)  -> simpleWFVar (concatE (Cons x s_x g) g') a Base
            (BTV a)  -> impossible ""  -}
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFVar1 {}) 
    = undefined
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFVar2 {})
    = undefined
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFVar3 {})
    = undefined
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFFunc env z t_z k_z p_env_tz t' k' z'_ p_z'env_t')
    = WFFunc (concatE (Cons x s_x g) g') z t_z k_z p_env'_tz t' k' z' p_z'env'_t'
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z k_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') k' p_z'env_t'
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFExis env z t_z k_z p_env_tz t' k' z'_ p_z'env_t')
    = WFExis (concatE (Cons x s_x g) g') z t_z k_z p_env'_tz t' k' z' p_z'env'_t'
        where
          z'            = z'_ ? lem_in_env_concat (Cons x t_x g) g' z'_ -- or lemma binds equal
                              ? lem_in_env_concat (Cons x s_x g) g' z'_
          p_env'_tz   = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t_z k_z p_env_tz
          p_z'env'_t' = lem_subtype_in_env_wf g (Cons z' t_z g') x s_x t_x p_sx_tx 
                                              (unbindT z z' t') k' p_z'env_t'
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFPoly {})
    = undefined
lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t k (WFKind env _t p_env_t_base)
    = WFKind (concatE (Cons x s_x g) g') t p_env'_t_base
        where
          p_env'_t_base = lem_subtype_in_env_wf g g' x s_x t_x p_sx_tx t Base p_env_t_base
