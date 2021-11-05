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
import SystemFTyping
import WellFormedness
import SystemFLemmasFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness

{-@ reflect foo26 @-}   
foo26 x = Just x 
foo26 :: a -> Maybe a 

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Typing Relation and the Subtyping Relation
-----------------------------------------------------------------------------

{-@ reflect selfify @-} 
{-@ selfify :: p:Pred -> b:Basic -> z:Vname -> e:Expr
        -> { p':Pred | fv p' == Set_cup (fv p) (fv e) && 
                       TRefn b z p' == self (TRefn b z p) e } @-}
selfify :: Pred -> Basic -> Vname -> Expr -> Pred
selfify p TBool   z e = App (App (Prim And) p) (App (App (Prim Eqv) (BV z)) e)
selfify p TInt    z e = App (App (Prim And) p) (App (App (Prim Eq)  (BV z)) e)

{-@ reflect self @-}
{-@ self :: t:Type -> e:Expr 
              -> { t':Type | Set_sub (free t') (Set_cup (free t) (fv e)) &&
                 Set_sub (tfreeBV t') (Set_cup (tfreeBV t) (freeBV e)) && 
                 erase t == erase t' && Set_sub (free t') (Set_cup (free t) (fv e)) } @-}
self :: Type -> Expr -> Type
self (TRefn b z p)     e = case b of
  TBool   -> TRefn b z (App (App (Prim And) p) (App (App (Prim Eqv) (BV z)) e))
  TInt    -> TRefn b z (App (App (Prim And) p) (App (App (Prim Eq)  (BV z)) e))
self (TFunc   z t_z t) e = TFunc   z t_z t
self (TExists z t_z t) e = TExists z t_z (self t e)

{-@ lem_tsubBV_self :: z:Vname -> v_z:Value -> t:Type 
        -> { e:Expr | not (Set_mem z (freeBV e)) } 
        -> { pf:_ | tsubBV z v_z (self t e) == self (tsubBV z v_z t) e } @-}
lem_tsubBV_self :: Vname -> Expr -> Type -> Expr -> Proof
lem_tsubBV_self z v_z (TRefn b x p)     e  
  | z == x    = ()
  | otherwise = ()      ? lem_subBV_notin z v_z (Prim And)
                        ? lem_subBV_notin z v_z e
--                        ? lem_subBV_notin z v_z (Prim Eql) 
                        ? lem_subBV_notin z v_z (Bc True)
                        ? lem_subBV_notin z v_z (BV x)
lem_tsubBV_self z v_z (TFunc x t_x t)   e = ()
lem_tsubBV_self z v_z (TExists x t_x t) e 
  | z == x    = ()
  | otherwise = () ? lem_tsubBV_self z v_z t e 

{-@ lem_tsubFV_self :: z:Vname -> v_z:Expr -> t:Type -> { x:Vname | x == z }
       -> { pf:_ | tsubFV z v_z (self t (FV x)) == self (tsubFV z v_z t) v_z } @-}
lem_tsubFV_self :: Vname -> Expr -> Type -> Vname -> Proof
lem_tsubFV_self z v_z (TRefn b w p)     x = case b of
  TBool   -> () 
  TInt    -> () 
lem_tsubFV_self z v_z (TFunc   y t_y t) x = ()
lem_tsubFV_self z v_z (TExists y t_y t) x = () ? lem_tsubFV_self z v_z t x 

{-@ lem_tsubFV_self1 :: z:Vname -> z':Vname -> t:Type -> { x:Vname | x == z } 
      -> { pf:_ | tsubFV z (FV z') (self t (FV x)) == self (tsubFV z (FV z') t) (FV z') } @-}
lem_tsubFV_self1 :: Vname -> Vname -> Type -> Vname -> Proof
lem_tsubFV_self1 z z' (TRefn b w p)     x = case b of
  TBool   -> () 
  TInt    -> () 
lem_tsubFV_self1 z z' (TFunc   y t_y t) x = ()
lem_tsubFV_self1 z z' (TExists y t_y t) x = () ? lem_tsubFV_self1 z z' t x 

{-@ lem_tsubFV_self2 :: z:Vname -> v:Value -> t:Type -> { x:Vname | x != z } 
        -> { pf:_ | tsubFV z v (self t (FV x)) == self (tsubFV z v t) (FV x) } @-}
lem_tsubFV_self2 :: Vname -> Expr -> Type -> Vname -> Proof
lem_tsubFV_self2 z v (TRefn b w p) x = case b of
  TBool   -> ()
  TInt    -> ()
lem_tsubFV_self2 z v (TFunc   y t_y t) x = ()
lem_tsubFV_self2 z v (TExists y t_y t) x = () ? lem_tsubFV_self2 z v t x 


{-@ lem_tsubFV_value_self :: b:Basic -> z:Vname -> p:Pred -> { x:Vname | not (Set_mem x (fv p)) }
        -> v:Value -> { pf:_ | tsubFV x v (self (TRefn b z p) (FV x)) 
                                == TRefn b z (App (App (Prim And) p)
                                                  (App (App (equals b) (BV z)) v)) } @-}
lem_tsubFV_value_self :: Basic -> Vname -> Pred -> Vname -> Expr -> Proof
lem_tsubFV_value_self TBool   z p x v = () ? lem_subFV_notin x v p
lem_tsubFV_value_self TInt    z p x v = () ? lem_subFV_notin x v p

{- @ equals :: b:Basic -> { c:Prim | Set_emp (fv (Prim c)) && Set_emp (freeBV (Prim c)) &&
                  erase_ty c == FTFunc (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool)) } @-}
{-@ reflect equals @-}
{-@ equals :: b:Basic -> { e:Expr | Set_emp (fv e) && Set_emp (freeBV e) } @-}
equals :: Basic -> Expr
equals TBool   = Prim Eqv
equals TInt    = Prim Eq

  --- the Typing Judgement

data HasTypeP where
    HasType :: Env -> Expr -> Type -> HasTypeP -- HasType G e t means G |- e : t

data HasType where 
    TBC   :: Env -> Bool -> HasType
    TIC   :: Env -> Int -> HasType
    TVar1 :: Env -> Vname -> Type -> WFType -> HasType
    TVar2 :: Env -> Vname -> Type -> HasType -> Vname -> Type -> HasType
    TPrm  :: Env -> Prim -> HasType
    TAbs  :: Env -> Vname -> Type -> WFType -> Expr -> Type -> Vname -> HasType -> HasType
    TApp  :: Env -> Expr -> Vname -> Type -> Type -> HasType 
              -> Expr -> HasType -> HasType
    TSub  :: Env -> Expr -> Type -> HasType -> Type -> WFType -> Subtype -> HasType

{-@ data HasType where
        TBC   :: g:Env -> b:Bool -> ProofOf(HasType g (Bc b) (tybc b))
        TIC   :: g:Env -> n:Int -> ProofOf(HasType g (Ic n) (tyic n))
        TVar1 :: g:Env -> { x:Vname | not (in_env x g) } -> t:Type -> ProofOf(WFType g t)
                    -> ProofOf(HasType (Cons x t g) (FV x) (self t (FV x)))
        TVar2 :: g:Env -> { x:Vname | in_env x g } -> t:Type -> ProofOf(HasType g (FV x) t)
                    -> { y:Vname | y != x && not (in_env y g) && not (Set_mem y (free t)) } -> s:Type
                    -> ProofOf(HasType (Cons y s g) (FV x) t)
        TPrm  :: g:Env -> c:Prim -> ProofOf(HasType g (Prim c) (ty c))
        TAbs  :: g:Env -> x:Vname -> t_x:Type -> ProofOf(WFType g t_x) -> e:Expr -> t:Type 
                  -> { y:Vname | not (in_env y g) && not (Set_mem y (fv e)) && not (Set_mem y (free t)) } 
                  -> ProofOf(HasType (Cons y t_x g) (unbind x y e) (unbindT x y t))
                  -> ProofOf(HasType g (Lambda x e) (TFunc x t_x t))
        TApp  :: g:Env -> e:Expr -> x:Vname -> t_x:Type -> t:Type
                  -> ProofOf(HasType g e (TFunc x t_x t)) 
                  -> e':Expr -> ProofOf(HasType g e' t_x) 
                  -> ProofOf(HasType g (App e e') (TExists x t_x t))
        TSub  :: g:Env -> e:Expr -> s:Type -> ProofOf(HasType g e s) -> t:Type
                  -> ProofOf(WFType g t) -> ProofOf(Subtype g s t) 
                  -> ProofOf(HasType g e t) @-} 

{-@ lazy typSize @-}
{-@ measure typSize @-}
{-@ typSize :: HasType -> { v:Int | v >= 0 } @-}
typSize :: HasType -> Int
typSize (TBC {})                             = 1
typSize (TIC {})                             = 1
typSize (TVar1 {})                           = 1
typSize (TVar2 _ _ _ p_x_b _ _)              = (typSize p_x_b)   + 1
typSize (TPrm {})                            = 1
typSize (TAbs _ _ _ _ _ _ _ p_e_b')          = (typSize p_e_b')  + 1
typSize (TApp _ _ _ _ _ p_e_bb' _ p_e'_b)    = (typSize p_e_bb') + (typSize p_e'_b)   + 1
typSize (TSub _ _ _ p_e_s _ _ p_s_t)         = (typSize p_e_s)   + (subtypSize p_s_t) + 1

{-@ reflect isTVar @-}
isTVar :: HasType -> Bool
isTVar (TVar1 {}) = True
isTVar (TVar2 {}) = True
isTVar _          = False

{-@ reflect isTVar1 @-}
isTVar1 :: HasType -> Bool
isTVar1 (TVar1 {}) = True
isTVar1 _          = False

{-@ reflect isTVar2 @-}
isTVar2 :: HasType -> Bool
isTVar2 (TVar2 {}) = True
isTVar2 _          = False

{-@ reflect isTAbs @-}
isTAbs :: HasType -> Bool
isTAbs (TAbs {}) = True
isTAbs _         = False

{-@ reflect isTApp @-}
isTApp :: HasType -> Bool
isTApp (TApp {}) = True
isTApp _         = False

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
    SBase :: Env -> Vname -> Basic -> Pred -> Vname -> Pred -> Vname -> Entails -> Subtype
    SFunc :: Env -> Vname -> Type -> Vname -> Type -> Subtype
               -> Type -> Type -> Vname -> Subtype -> Subtype
    SWitn :: Env -> Expr -> Type -> HasType -> Type -> Vname -> Type
               -> Subtype -> Subtype
    SBind :: Env -> Vname -> Type -> Type -> Type -> Vname -> Subtype -> Subtype

-- edited SFunc 5/5/20: was -> { x2:Vname | not (in_Env x2 g) }. x2 is a BV so there's no
--     possibility for collision with the FV's in the environment g.
{-@ data Subtype where
        SBase :: g:Env -> v1:Vname -> b:Basic -> p1:Pred -> v2:Vname -> p2:Pred 
                 -> { y:Vname | not (in_env y g) && not (Set_mem y (fv p2)) }
                 -> ProofOf(Entails ( Cons y (TRefn b v1 p1) g) (unbind v2 y p2))
                 -> ProofOf(Subtype g (TRefn b v1 p1) (TRefn b v2 p2))
        SFunc :: g:Env -> x1:Vname -> s1:Type -> x2:Vname -> s2:Type
                 -> ProofOf(Subtype g s2 s1) -> t1:Type -> t2:Type
                 -> { y:Vname | not (in_env y g) && not (Set_mem y (free t1))
                                                 && not (Set_mem y (free t2)) }
                 -> ProofOf(Subtype (Cons y s2 g) (unbindT x1 y t1) (unbindT x2 y t2))
                 -> ProofOf(Subtype g (TFunc x1 s1 t1) (TFunc x2 s2 t2))
        SWitn :: g:Env -> e:Value  -> t_x:Type -> ProofOf(HasType g e t_x) 
                 -> t:Type -> x:Vname -> t':Type -> ProofOf(Subtype g t (tsubBV x e t'))
                 -> ProofOf(Subtype g t (TExists x t_x t'))
        SBind :: g:Env -> x:Vname -> t_x:Type -> t:Type -> {t':Type | not Set_mem x (tfreeBV t')} 
                 -> { y:Vname | not (in_env y g) && not (Set_mem y (free t))
                                                 && not (Set_mem y (free t')) }
                 -> ProofOf(Subtype (Cons y t_x g) (unbindT x y t) t')
                 -> ProofOf(Subtype g (TExists x t_x t) t') @-}

{-@ lazy subtypSize @-}
{-@ measure subtypSize @-}
{-@ subtypSize :: Subtype -> { v:Int | v >= 0 } @-}
subtypSize :: Subtype -> Int
subtypSize (SBase {})                              = 1
subtypSize (SFunc _ _ _ _ _ p_s2_s1 _ _ _ p_t1_t2) = (subtypSize p_s2_s1) + (subtypSize p_t1_t2) + 1
subtypSize (SWitn _ _ _ p_e_tx _ _ _ p_t_t')       = (subtypSize p_t_t')  + (typSize p_e_tx)     + 1
subtypSize (SBind _ _ _ _ _ _ p_t_t')              = (subtypSize p_t_t')  + 1

{-@ measure subtypSize' @-}
{-@ subtypSize' :: Subtype -> { v:Int | v >= 0 } @-}
subtypSize' :: Subtype -> Int
subtypSize' (SBase {})                              = 1
subtypSize' (SFunc _ _ _ _ _ p_s2_s1 _ _ _ p_t1_t2) = (subtypSize' p_s2_s1) + (subtypSize' p_t1_t2) + 1
subtypSize' (SWitn _ _ _ p_e_tx _ _ _ p_t_t')       = (subtypSize' p_t_t')  + 1
subtypSize' (SBind _ _ _ _ _ _ p_t_t')              = (subtypSize' p_t_t')  + 1

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

-------------------------------------------------------------------------
----- | CLOSING SUBSTITUTIONS 
-------------------------------------------------------------------------

-- closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
--   the typing env downwards/leftwards. In order for a closing substitution to be
--   "well formed" it must be an element of the denotation the corresponding enivornment

data CSub = CEmpty
            | CCons  Vname Expr CSub
  deriving (Show)
{-@ data CSub  where
        CEmpty :: CSub
        CCons  :: x:Vname -> { v:Value | Set_emp (fv v) && Set_emp (freeBV v) } 
                          -> { th:CSub | not (in_csubst x th ) } 
                          -> { th':CSub | bindsC th'   == Set_cup (Set_sng x)  (bindsC th) } @-}

{-@ reflect bindsC @-}
bindsC :: CSub -> S.Set Vname
bindsC CEmpty          = S.empty
bindsC (CCons  x v th) = S.union (S.singleton x) (bindsC th)

{-@ reflect in_csubst @-}
in_csubst :: Vname -> CSub -> Bool
in_csubst x th = S.member x (bindsC th)

{-@ reflect bound_inC @-}
bound_inC :: Vname -> Expr -> CSub -> Bool
bound_inC x v CEmpty                              = False
bound_inC x v (CCons y v' th) | (x == y)          = (v == v')
                              | otherwise         = bound_inC x v th

{-{-@ measure uniqueC @-}
uniqueC :: CSub -> Bool
uniqueC CEmpty         = True
uniqueC (CCons x v th) = (uniqueC th) && not (S.member x (bindsC th))

{-@ lem_env_uniqueC :: th:CSub -> { pf:_ | uniqueC th } @-}
lem_env_uniqueC :: CSub -> Proof
lem_env_uniqueC CEmpty         = ()
lem_env_uniqueC (CCons x v th) = () ? lem_env_uniqueC th-}

{-@ reflect csubst @-}
{-@ csubst :: th:CSub -> e:Expr -> Expr @-}
csubst :: CSub -> Expr -> Expr
csubst CEmpty          e = e
csubst (CCons  x v th) e = csubst th (subFV x v e)

-- Idea: ctsubst th t = foldr (\(x,e) t' -> tsubFV x e t') t th 
{-@ reflect ctsubst @-}
{-@ ctsubst :: th:CSub -> t:Type -> Type @-}
ctsubst :: CSub -> Type -> Type
ctsubst CEmpty           t = t
ctsubst (CCons  x v  th) t = ctsubst th (tsubFV x v t)

{-@ reflect concatCS @-}
{-@ concatCS :: th:CSub -> { th':CSub | Set_emp (Set_cap (bindsC th) (bindsC th')) }
                          -> { thC:CSub | bindsC thC == Set_cup (bindsC th) (bindsC th') } @-}
concatCS :: CSub -> CSub -> CSub
concatCS th CEmpty           = th
concatCS th (CCons  x v th') = CCons x v (concatCS th th')


{-@ reflect change_varCS @-}
{-@ change_varCS :: th:CSub ->  { x:Vname | in_csubst x th } 
        -> { y:Vname | y == x || not (in_csubst y th) } 
        -> { th':CSub | bindsC th'  == Set_cup (Set_sng y) (Set_dif  (bindsC th) (Set_sng x)) } @-}
change_varCS :: CSub -> Vname -> Vname -> CSub
change_varCS CEmpty            x y = CEmpty
change_varCS (CCons  z v_z th) x y | ( x == z ) = CCons  y v_z th
                                   | otherwise  = CCons  z v_z (change_varCS th x y)

{-@ reflect remove_fromCS @-}
{-@ remove_fromCS :: th:CSub -> { x:Vname | in_csubst x th}
        -> { th':CSub | bindsC th' == Set_dif (bindsC th) (Set_sng x) } @-}
remove_fromCS :: CSub -> Vname -> CSub
remove_fromCS (CCons  z v_z th) x | ( x == z ) = th
                                  | otherwise  = CCons  z v_z (remove_fromCS th x)

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
    DRefn :: Basic -> Vname -> Pred -> Expr -> HasFType -> EvalsTo -> Denotes
    DFunc :: Vname -> Type -> Type -> Expr -> HasFType
              -> (Expr -> Denotes -> ValueDenoted) -> Denotes
    DExis :: Vname -> Type -> Type -> Expr -> HasFType
              -> Expr -> Denotes -> Denotes -> Denotes
{-@ data Denotes where
        DRefn :: b:Basic -> x:Vname -> p:Pred -> v:Value  
                  -> ProofOf(HasFType FEmpty v (FTBasic b))
                  -> ProofOf(EvalsTo (subBV x v p) (Bc True)) 
                  -> ProofOf(Denotes (TRefn b x p) v)
        DFunc :: x:Vname -> t_x:Type -> t:Type -> v:Value  
                  -> ProofOf(HasFType FEmpty v (erase (TFunc x t_x t)))
                  -> ( v_x:Value -> ProofOf(Denotes t_x v_x)
                                 -> ProofOf(ValueDenoted (App v v_x) (tsubBV x v_x t)) ) 
                  -> ProofOf(Denotes (TFunc x t_x t) v)
        DExis :: x:Vname -> t_x:Type -> t:Type -> v:Value 
                  -> ProofOf(HasFType FEmpty v (erase t))
                  -> v_x:Value -> ProofOf(Denotes t_x v_x)
                  -> ProofOf(Denotes (tsubBV x v_x t) v)
                  -> ProofOf(Denotes (TExists x t_x t) v)  @-}

{-@ get_ftyp_from_den :: t:Type -> v:Value -> ProofOf(Denotes t v)
              -> ProofOf(HasFType FEmpty v (erase t)) @-}
get_ftyp_from_den :: Type -> Expr -> Denotes -> HasFType
get_ftyp_from_den t v (DRefn b _ _ _ pf_v_b _)     = pf_v_b
get_ftyp_from_den t v (DFunc _ _ _ _ pf_v_b _)     = pf_v_b
get_ftyp_from_den t v (DExis _ _ _ _ pf_v_b _ _ _) = pf_v_b

{-@ lem_den_nofv :: v:Value -> t:Type -> ProofOf(Denotes t v) -> { pf:_ | Set_emp (fv v) } @-}
lem_den_nofv :: Expr -> Type -> Denotes -> Proof
lem_den_nofv v t den_t_v = lem_fv_subset_bindsF FEmpty v (erase t) pf_v_bt
  where
    pf_v_bt = get_ftyp_from_den t v den_t_v

{-@ lem_den_nobv :: v:Value -> t:Type -> ProofOf(Denotes t v) -> { pf:_ | Set_emp (freeBV v) } @-}
lem_den_nobv :: Expr -> Type -> Denotes -> Proof
lem_den_nobv v t den_t_v = lem_freeBV_emptyB FEmpty v (erase t) pf_v_bt
  where
    pf_v_bt = get_ftyp_from_den t v den_t_v

{-@ get_obj_from_dfunc :: x:Vname -> s:Type -> t:Type -> v:Value 
        -> ProofOf(Denotes (TFunc x s t) v) -> v':Value 
        -> ProofOf(Denotes s v') -> ProofOf(ValueDenoted (App v v') (tsubBV x v' t)) @-}  
get_obj_from_dfunc :: Vname -> Type -> Type -> Expr -> Denotes 
                                    -> Expr -> Denotes -> ValueDenoted
get_obj_from_dfunc x s t v (DFunc _ _ _ _ _ prover) v' den_s_v' = prover v' den_s_v' 

-- Denotations of Environments, [[g]]. There are two cases:
--   1. [[ Empty ]] = { CEmpty }.
--   2. [[ Cons x t g ]] = { CCons x v_x th | Denotes th(t) v_x && th \in [[ g ]] }
data DenotesEnvP where 
    DenotesEnv :: Env -> CSub -> DenotesEnvP 

data DenotesEnv where
    DEmp :: DenotesEnv
    DExt :: Env -> CSub -> DenotesEnv -> Vname -> Type -> Expr -> Denotes -> DenotesEnv
{-@ data DenotesEnv where 
        DEmp  :: ProofOf(DenotesEnv Empty CEmpty)
        DExt  :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) -> { x:Vname | not (in_env x g) } 
                 -> t:Type -> { v:Value | Set_emp (fv v) && Set_emp (freeBV v) }
                 -> ProofOf(Denotes (ctsubst th t) v)
                 -> ProofOf(DenotesEnv (Cons x t g) (CCons x v th)) @-}

{-@ lem_binds_env_th :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> { pf:_ | binds g == bindsC th } @-}
lem_binds_env_th :: Env -> CSub -> DenotesEnv -> Proof
lem_binds_env_th g th DEmp                                       = ()
lem_binds_env_th g th (DExt  g' th' den_g'_th' x t v den_th't_v) = () ? lem_binds_env_th g' th' den_g'_th'
