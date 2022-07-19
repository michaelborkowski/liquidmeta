{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import SystemFWellFormedness            

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation
-----------------------------------------------------------------------------

data HasFType where
    FTBC   :: FEnv -> Bool -> HasFType
    FTIC   :: FEnv -> Int -> HasFType
    FTVar1 :: FEnv -> Vname -> FType -> HasFType 
    FTVar2 :: FEnv -> Vname -> FType -> HasFType -> Vname -> FType -> HasFType
    FTVar3 :: FEnv -> Vname -> FType -> HasFType -> Vname -> Kind -> HasFType
    FTPrm  :: FEnv -> Prim -> HasFType
    FTAbs  :: FEnv -> FType -> Kind -> WFFT -> Expr -> FType -> Names
                   -> (Vname -> HasFType) -> HasFType
    FTApp  :: FEnv -> Expr -> FType -> FType -> HasFType 
                   -> Expr -> HasFType -> HasFType
    FTAbsT :: FEnv -> Kind -> Expr -> FType -> Names -> (Vname -> HasFType) -> HasFType
    FTAppT :: FEnv -> Expr -> Kind -> FType -> HasFType -> Type -> WFFT -> HasFType
    FTLet  :: FEnv -> Expr -> FType -> HasFType -> Expr -> FType -> Names
                   -> (Vname -> HasFType) -> HasFType
    FTAnn  :: FEnv -> Expr -> FType -> Type -> HasFType -> HasFType

{-@ data HasFType where
        FTBC   :: g:FEnv -> b:Bool -> ProofOf(HasFType g (Bc b) (FTBasic TBool))
        FTIC   :: g:FEnv -> n:Int -> ProofOf(HasFType g (Ic n) (FTBasic TInt))
        FTVar1 :: g:FEnv -> { x:Vname | not (in_envF x g) } -> b:FType 
                    -> ProofOf(HasFType (FCons x b g) (FV x) b)
        FTVar2 :: g:FEnv -> { x:Vname | in_envF x g } -> b:FType -> ProofOf(HasFType g (FV x) b)
                    -> { y:Vname | y != x && not (in_envF y g) } -> b':FType 
                    -> ProofOf(HasFType (FCons y b' g) (FV x) b)
        FTVar3 :: g:FEnv -> { x:Vname | in_envF x g } -> b:FType -> ProofOf(HasFType g (FV x) b)
                    -> { y:Vname | y != x && not (in_envF y g) }  -> k:Kind
                    -> ProofOf(HasFType (FConsT y k g) (FV x) b)
        FTPrm  :: g:FEnv -> c:Prim  -> ProofOf(HasFType g (Prim c) (erase_ty c))
        FTAbs  :: g:FEnv -> b:FType -> k:Kind -> ProofOf(WFFT g b k) -> e:Expr -> b':FType -> nms:Names
                  -> ( { y:Vname | NotElem y nms } -> ProofOf(HasFType (FCons y b g) (unbind y e) b') )
                  -> ProofOf(HasFType g (Lambda e) (FTFunc b b'))
        FTApp  :: g:FEnv -> e:Expr -> b:FType -> b':FType
                  -> ProofOf(HasFType g e (FTFunc b b')) 
                  -> e':Expr -> ProofOf(HasFType g e' b) 
                  -> ProofOf(HasFType g (App e e') b')
        FTAbsT :: g:FEnv -> k:Kind -> e:Expr -> b:FType -> nms:Names
                  -> ( { a':Vname | NotElem a' nms }
                         -> ProofOf(HasFType (FConsT a' k g) (unbind_tv a' e) (unbindFT a' b)) )
                  -> ProofOf(HasFType g (LambdaT k e) (FTPoly k b))
        FTAppT :: g:FEnv -> e:Expr -> k:Kind -> t':FType
                -> ProofOf(HasFType g e (FTPoly k t')) 
                -> { rt:UserType | Set_sub (free rt) (vbindsF g) && 
                                   Set_sub (freeTV rt) (tvbindsF g) && isLCT rt }
                -> ProofOf(WFFT g (erase rt) k)
                -> ProofOf(HasFType g (AppT e rt) (ftsubBV (erase rt) t'))
        FTLet  :: g:FEnv -> e_x:Expr -> b:FType -> ProofOf(HasFType g e_x b)
                -> e:Expr -> b':FType -> nms:Names
                -> ( { y:Vname | NotElem y nms } -> ProofOf(HasFType (FCons y b g) (unbind y e) b') )
                -> ProofOf(HasFType g (Let e_x e) b')
        FTAnn  :: g:FEnv -> e:Expr -> b:FType 
                -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (vbindsF g) 
                                               && Set_sub (freeTV t1) (tvbindsF g) && isLCT t1 }
                -> ProofOf(HasFType g e b) -> ProofOf(HasFType g (Annot e t1) b) @-}

{-@ reflect isFTVar @-}
isFTVar :: HasFType -> Bool
isFTVar (FTVar1 {}) = True
isFTVar (FTVar2 {}) = True
isFTVar (FTVar3 {}) = True
isFTVar _           = False

{-@ reflect isFTAbs @-}
isFTAbs :: HasFType -> Bool
isFTAbs (FTAbs {}) = True
isFTAbs _          = False

{-@ reflect isFTApp @-}
isFTApp :: HasFType -> Bool
isFTApp (FTApp {}) = True
isFTApp _          = False

{-@ reflect isFTAbsT @-}
isFTAbsT :: HasFType -> Bool
isFTAbsT (FTAbsT {}) = True
isFTAbsT _           = False

{-@ reflect isFTAppT @-}
isFTAppT :: HasFType -> Bool
isFTAppT (FTAppT {}) = True
isFTAppT _           = False

{-@ reflect isFTLet @-}
isFTLet :: HasFType -> Bool
isFTLet (FTLet {}) = True
isFTLet _          = False

{-@ reflect isFTAnn @-}
isFTAnn :: HasFType -> Bool
isFTAnn (FTAnn {}) = True
isFTAnn _          = False

{-@ simpleFTVar :: g:FEnv -> { x:Vname | in_envF x g} -> { t:FType | bound_inF x t g } 
                -> ProofOf(HasFType g (FV x) t) @-}
simpleFTVar :: FEnv -> Vname -> FType -> HasFType
simpleFTVar g x t = case g of
  (FCons y s g') ->  case (x == y, t == s) of   -- g = Empty is impossible
        (True, True) -> FTVar1 g' x t           -- x = y but t != s is impossible
        (False, _)   -> FTVar2 g' x t (simpleFTVar g' x t) y s
  (FConsT a k g') -> case (x == a) of
        False        -> FTVar3 g' x t (simpleFTVar g' x t) a k

data PHasFType where
    PFTEmp  :: FEnv -> PHasFType
    PFTCons :: FEnv -> Expr -> HasFType -> Preds -> PHasFType -> PHasFType

{-@ data PHasFType where
        PFTEmp  :: g:FEnv -> ProofOf(PHasFType g PEmpty)
        PFTCons :: g:FEnv -> p:Expr   -> ProofOf(HasFType g p (FTBasic TBool))
                          -> ps:Preds -> ProofOf(PHasFType g ps)
                          -> ProofOf(PHasFType g (PCons p ps)) @-}

-------------------------------------------------------------------------
----- | REFINEMENT TYPES of BUILT-IN PRIMITIVES
-------------------------------------------------------------------------

{-@ reflect tybc @-} -- Refined Constant Typing
{-@ tybc :: b:Bool -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
tybc :: Bool -> Type
tybc b  = TRefn TBool (PCons (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) 
                                       (BV 0)) (Bc b))  PEmpty)

{-@ reflect tyic @-}
{-@ tyic :: n:Int -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
tyic :: Int -> Type
tyic n  = TRefn TInt  (PCons (App (App (AppT (Prim Eql) (TRefn TInt  PEmpty))
                                       (BV 0)) (Ic n))  PEmpty)

{-@ reflect refn_pred @-}
{-@ refn_pred :: c:Prim  -> { p:Expr | Set_emp (fv p) && Set_emp (ftv p) } @-}
refn_pred :: Prim -> Expr
refn_pred And      = App (App (Prim Eqv) (BV 0)) 
                               (App (App (Prim And) (BV 2)) (BV 1)) 
refn_pred Or       = App (App (Prim Eqv) (BV 0)) 
                               (App (App (Prim Or) (BV 2)) (BV 1)) 
refn_pred Not      = App (App (Prim Eqv) (BV 0)) 
                           (App (Prim Not) (BV 1)) 
refn_pred Eqv      = App (App (Prim Eqv) (BV 0))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (BV 2)) (BV 1)))
                                    (App (App (Prim And) (App (Prim Not) (BV 2)))
                                         (App (Prim Not) (BV 1))))
refn_pred Imp      = App (App (Prim Eqv) (BV 0))
                               (App (App (Prim Or) (App (Prim Not) (BV 2))) (BV 1))
refn_pred Leq      = App (App (Prim Eqv) (BV 0))
                               (App (App (Prim Leq) (BV 2)) (BV 1)) 
refn_pred (Leqn n) = App (App (Prim Eqv) (BV 0))
                           (App (App (Prim Leq) (Ic n)) (BV 1)) 
refn_pred Eq       = App (App (Prim Eqv) (BV 0))
                               (App (App (Prim Eq) (BV 2)) (BV 1))
refn_pred (Eqn n)  = App (App (Prim Eqv) (BV 0))
                           (App (App (Prim Eq) (Ic n)) (BV 1))
refn_pred Leql     = App (App (Prim Eqv) (BV 0))
                           (App (App (AppT (Prim Leql) (TRefn (BTV 0) PEmpty)) (BV 2)) (BV 1))
refn_pred Eql      = App (App (Prim Eqv) (BV 0))
                           (App (App (AppT (Prim Eql)  (TRefn (BTV 0) PEmpty)) (BV 2)) (BV 1))

{-@ reflect ty @-} -- Primitive Typing            
{-@ ty :: c:Prim -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
ty :: Prim -> Type
ty And      = TFunc (inType And)      (ty' And)
ty Or       = TFunc (inType Or)       (ty' Or)
ty Not      = TFunc (inType Not)      (ty' Not)
ty Eqv      = TFunc (inType Eqv)      (ty' Eqv)
ty Imp      = TFunc (inType Imp)      (ty' Imp)
ty Leq      = TFunc (inType Leq)      (ty' Leq)
ty (Leqn n) = TFunc (inType (Leqn n)) (ty' (Leqn n))
ty Eq       = TFunc (inType Eq)       (ty' Eq)
ty (Eqn n)  = TFunc (inType (Eqn n))  (ty' (Eqn n))
ty Leql     = TPoly Base (TFunc (inType Leql) (ty' Leql))
ty Eql      = TPoly Base (TFunc (inType Eql)  (ty' Eql))

{-@ reflect erase_ty @-}
{-@ erase_ty :: c:Prim -> { t:FType | Set_emp (ffreeTV t) && t == erase (ty c) && isLCFT t } @-}
erase_ty :: Prim -> FType
erase_ty And      = FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
erase_ty Or       = FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
erase_ty Not      = FTFunc (FTBasic TBool) (FTBasic TBool)
erase_ty Eqv      = FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
erase_ty Imp      = FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
erase_ty Leq      = FTFunc (FTBasic TInt)  (FTFunc (FTBasic TInt)  (FTBasic TBool))
erase_ty (Leqn n) = FTFunc (FTBasic TInt)  (FTBasic TBool)
erase_ty Eq       = FTFunc (FTBasic TInt)  (FTFunc (FTBasic TInt)  (FTBasic TBool))
erase_ty (Eqn n)  = FTFunc (FTBasic TInt)  (FTBasic TBool)
erase_ty Leql     = FTPoly Base (FTFunc (FTBasic (BTV 0))
                                          (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))
erase_ty Eql      = FTPoly Base (FTFunc (FTBasic (BTV 0)) 
                                          (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))

{-@ reflect inType @-}
{-@ inType :: c:Prim -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
inType :: Prim -> Type
inType And     = TRefn TBool   PEmpty 
inType Or      = TRefn TBool   PEmpty
inType Eqv     = TRefn TBool   PEmpty
inType Imp     = TRefn TBool   PEmpty
inType Not     = TRefn TBool   PEmpty
inType Leql    = TRefn (BTV 0) PEmpty
inType Eql     = TRefn (BTV 0) PEmpty
inType _       = TRefn TInt    PEmpty

{-@ reflect ty' @-}
{-@ ty' :: c:Prim -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
ty' :: Prim -> Type
ty' And      = TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred And) PEmpty))
ty' Or       = TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Or)  PEmpty))
ty' Not      =                             TRefn TBool (PCons (refn_pred Not) PEmpty)
ty' Eqv      = TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Eqv) PEmpty))
ty' Imp      = TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Imp) PEmpty))
ty' Leq      = TFunc (TRefn TInt  PEmpty) (TRefn TBool (PCons (refn_pred Leq) PEmpty))
ty' (Leqn n) =                             TRefn TBool (PCons (refn_pred (Leqn n)) PEmpty)
ty' Eq       = TFunc (TRefn TInt  PEmpty) (TRefn TBool (PCons (refn_pred Eq)  PEmpty)) 
ty' (Eqn n)  =                             TRefn TBool (PCons (refn_pred (Eqn n)) PEmpty)
ty' Leql     = TFunc (TRefn (BTV 0) PEmpty) (TRefn TBool (PCons (refn_pred Leql) PEmpty))
ty' Eql      = TFunc (TRefn (BTV 0) PEmpty) (TRefn TBool (PCons (refn_pred Eql) PEmpty))
