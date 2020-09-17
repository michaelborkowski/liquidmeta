{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SystemFTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import SystemFWellFormedness

-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation
-----------------------------------------------------------------------------

data HasFTypeP where
    HasFType :: FEnv -> Expr -> FType -> HasFTypeP 

data HasFType where
    FTBC   :: FEnv -> Bool -> HasFType
    FTIC   :: FEnv -> Int -> HasFType
    FTVar1 :: FEnv -> Vname -> FType -> HasFType 
    FTVar2 :: FEnv -> Vname -> FType -> HasFType -> Vname -> FType -> HasFType
    FTVar3 :: FEnv -> Vname -> FType -> HasFType -> Vname -> Kind -> HasFType
    FTPrm  :: FEnv -> Prim -> HasFType
    FTAbs  :: FEnv -> Vname -> FType -> Kind -> WFFT -> Expr -> FType 
                   -> Vname -> HasFType -> HasFType
    FTApp  :: FEnv -> Expr -> FType -> FType -> HasFType 
                   -> Expr -> HasFType -> HasFType
    FTAbsT :: FEnv -> Vname -> Kind -> Expr -> FType -> Vname -> HasFType -> HasFType
    FTAppT :: FEnv -> Expr -> Vname -> Kind -> FType -> HasFType -> Type -> WFFT -> HasFType
    FTLet  :: FEnv -> Expr -> FType -> HasFType -> Vname -> Expr
                   -> FType -> Vname -> HasFType -> HasFType
    FTAnn  :: FEnv -> Expr -> FType -> Type -> HasFType -> HasFType

{-@ data HasFType where
    FTBC   :: g:FEnv -> b:Bool -> ProofOf(HasFType g (Bc b) (FTBasic TBool))
 |  FTIC   :: g:FEnv -> n:Int -> ProofOf(HasFType g (Ic n) (FTBasic TInt))
 |  FTVar1 :: g:FEnv -> { x:Vname | not (in_envF x g) } -> b:FType 
                -> ProofOf(HasFType (FCons x b g) (FV x) b)
 |  FTVar2 :: g:FEnv -> { x:Vname | in_envF x g } -> b:FType -> ProofOf(HasFType g (FV x) b)
                -> { y:Vname | y != x && not (in_envF y g) } -> b':FType 
                -> ProofOf(HasFType (FCons y b' g) (FV x) b)
 |  FTVar3 :: g:FEnv -> { x:Vname | in_envF x g } -> b:FType -> ProofOf(HasFType g (FV x) b)
                -> { y:Vname | y != x && not (in_envF y g) }  -> k:Kind
                -> ProofOf(HasFType (FConsT y k g) (FV x) b)
 |  FTPrm  :: g:FEnv -> c:Prim  -> ProofOf(HasFType g (Prim c) (erase (ty c)))
 |  FTAbs  :: g:FEnv -> x:Vname -> b:FType -> k:Kind -> ProofOf(WFFT g b k) -> e:Expr -> b':FType
                -> { y:Vname | not (in_envF y g) && not (Set_mem y (fv e)) && not (Set_mem y (ftv e)) }
                -> ProofOf(HasFType (FCons y b g) (unbind x y e) b')
                -> ProofOf(HasFType g (Lambda x e) (FTFunc b b'))
 |  FTApp  :: g:FEnv -> e:Expr -> b:FType -> b':FType
                -> ProofOf(HasFType g e (FTFunc b b')) 
                -> e':Expr -> ProofOf(HasFType g e' b) 
                -> ProofOf(HasFType g (App e e') b')
 |  FTAbsT :: g:FEnv -> a:Vname -> k:Kind -> e:Expr -> b:FType
                -> { a':Vname | not (in_envF a' g) && not (Set_mem a' (fv e)) 
                                  && not (Set_mem a' (ftv e)) && not (Set_mem a' (ffreeTV b)) }
                -> ProofOf(HasFType (FConsT a' k g) (unbind_tv a a' e) (unbindFT a a' b))
                -> ProofOf(HasFType g (LambdaT a k e) (FTPoly a k b))
 |  FTAppT :: g:FEnv -> e:Expr -> a:Vname -> k:Kind -> t':FType
                -> ProofOf(HasFType g e (FTPoly a k t')) 
                -> { rt:Type | Set_sub (Set_cup (free rt) (freeTV rt)) (bindsF g) }
                -> ProofOf(WFFT g (erase rt) k)
                -> ProofOf(HasFType g (AppT e rt) (ftsubBV a (erase rt) t'))
 |  FTLet  :: g:FEnv -> e_x:Expr -> b:FType -> ProofOf(HasFType g e_x b)
                -> x:Vname -> e:Expr -> b':FType 
                -> { y:Vname | not (in_envF y g) && not (Set_mem y (fv e)) && not (Set_mem y (ftv e)) }
                -> ProofOf(HasFType (FCons y b g) (unbind x y e) b')
                -> ProofOf(HasFType g (Let x e_x e) b')
 |  FTAnn  :: g:FEnv -> e:Expr -> b:FType 
                -> { t1:Type | (erase t1 == b) && Set_sub (Set_cup (free t1) (freeTV t1)) (bindsF g) }
                -> ProofOf(HasFType g e b) -> ProofOf(HasFType g (Annot e t1) b)  @-} 

-- old version : -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsF g) && Set_emp (tfreeBV t1) }
  
{-@ measure ftypSize @-}
{-@ ftypSize :: HasFType -> { v:Int | v >= 0 } @-}
ftypSize :: HasFType -> Int
ftypSize (FTBC {})                           = 1
ftypSize (FTIC {})                           = 1
ftypSize (FTVar1 {})                         = 1
ftypSize (FTVar2 _ _ _ p_x_b _ _)            = (ftypSize p_x_b)   + 1
ftypSize (FTVar3 _ _ _ p_x_b _ _)            = (ftypSize p_x_b)   + 1
ftypSize (FTPrm {})                          = 1
ftypSize (FTAbs _ _ _ _ _ _ _ _ p_e_b')      = (ftypSize p_e_b')  + 1
ftypSize (FTApp _ _ _ _ p_e_bb' _ p_e'_b)    = (ftypSize p_e_bb') + (ftypSize p_e'_b) + 1
ftypSize (FTAbsT _ _ _ _ _ _ p_e_b)          = (ftypSize p_e_b)  + 1
ftypSize (FTAppT _ _ _ _ _ p_e_at' _ _)      = (ftypSize p_e_at') + 1
ftypSize (FTLet _ _ _ p_ex_b _ _ _ _ p_e_b') = (ftypSize p_ex_b)  + (ftypSize p_e_b') + 1
ftypSize (FTAnn _ _ _ _ p_e_b)               = (ftypSize p_e_b)   + 1

{- @ automatic-instances simpleFTVar @-}
{-@ simpleFTVar :: g:FEnv -> { x:Vname | in_envF x g} -> { t:FType | bound_inF x t g } 
                -> ProofOf(HasFType g (FV x) t) @-}
simpleFTVar :: FEnv -> Vname -> FType -> HasFType
simpleFTVar g x t = case g of
  (FCons y s g') ->  case (x == y, t == s) of   -- g = Empty is impossible
        (True, True) -> FTVar1 g' x t           -- x = y but t != s is impossible
        (False, _)   -> FTVar2 g' x t (simpleFTVar g' x t) y s
  (FConsT a k g') -> case (x == a) of
        False        -> FTVar3 g' x t (simpleFTVar g' x t) a k


-------------------------------------------------------------------------
----- | REFINEMENT TYPES of BUILT-IN PRIMITIVES
-------------------------------------------------------------------------

{-@ reflect tybc @-} -- Refined Constant Typing
tybc :: Bool -> Type
tybc True  = TRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc True))
tybc False = TRefn TBool 1 (App (App (Prim Eqv) (BV 1)) (Bc False))

{-@ reflect tyic @-}
tyic :: Int -> Type
tyic n = TRefn TInt 1 (App (App (Prim Eq) (BV 1)) (Ic n))

{-@ reflect refn_pred_freeBV @-}
refn_pred_freeBV :: Prim -> S.Set Vname
refn_pred_freeBV Not      = S.fromList [3,2]
refn_pred_freeBV (Leqn _) = S.fromList [3,2]
refn_pred_freeBV (Eqn _)  = S.fromList [3,2]
refn_pred_freeBV _        = S.fromList [3,2,1]

{- @ refn_pred :: c:Prim -> { p:Pred | noDefns p && Set_sub (freeBV p) (refn_pred_freeBV c) -}
{-@ reflect refn_pred @-}
{-@ refn_pred :: c:Prim -> { p:Pred | noDefns p && Set_emp (fv p) } @-}
refn_pred :: Prim -> Pred
refn_pred And      = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim And) (BV 1)) (BV 2)) 
refn_pred Or       = App (App (Prim Eqv) (BV 3)) 
                               (App (App (Prim Or) (BV 1)) (BV 2)) 
refn_pred Not      = App (App (Prim Eqv) (BV 3)) 
                           (App (Prim Not) (BV 2)) 
refn_pred Eqv      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (BV 1)) (BV 2)))
                                    (App (App (Prim And) (App (Prim Not) (BV 1)))
                                         (App (Prim Not) (BV 2))))
refn_pred Leq      = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Leq) (BV 1)) (BV 2)) 
refn_pred (Leqn n) = App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Leq) (Ic n)) (BV 2)) 
refn_pred Eq       = App (App (Prim Eqv) (BV 3))
                               (App (App (Prim Eq) (BV 1)) (BV 2))
refn_pred (Eqn n)  = App (App (Prim Eqv) (BV 3))
                           (App (App (Prim Eq) (Ic n)) (BV 2))

{-@ reflect un321_refn_pred @-}
{- @ un321_refn_pred :: c:Prim 
     -> { p:Pred | un321_refn_pred c == unbind 3 3 (un21_refn_pred c) } @-}
{- @ un321_refn_pred :: c:Prim -> { p:Pred | noDefns p } @-}
un321_refn_pred :: Prim -> Pred
un321_refn_pred And      = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim And) (FV 1)) (FV 2)) 
un321_refn_pred Or       = App (App (Prim Eqv) (FV 3)) 
                               (App (App (Prim Or) (FV 1)) (FV 2)) 
un321_refn_pred Not      = App (App (Prim Eqv) (FV 3)) 
                               (App (Prim Not) (FV 2)) 
un321_refn_pred Eqv      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Or) 
                                    (App (App (Prim And) (FV 1)) (FV 2)))
                                    (App (App (Prim And) (App (Prim Not) (FV 1)))
                                         (App (Prim Not) (FV 2))))
un321_refn_pred Leq      = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Leq) (FV 1)) (FV 2)) 
un321_refn_pred (Leqn n) = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Leq) (Ic n)) (FV 2)) 
un321_refn_pred Eq       = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Eq) (FV 1)) (FV 2))
un321_refn_pred (Eqn n)  = App (App (Prim Eqv) (FV 3))
                               (App (App (Prim Eq) (Ic n)) (FV 2))

{-@ reflect ty @-} -- Primitive Typing            -- removed: && Set_emp (tfreeBV t)
{-@ ty :: c:Prim -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
--                                 && noDefnsInRefns Empty t && isWellFormed Empty t Star } @-}
--                                 && noDefnsInRefns Empty t } @-}
ty :: Prim -> Type
--ty c = TFunc (firstBV c) (inType c) (ty' c)
ty And      = TFunc (firstBV And)      (inType And)      (ty' And)
ty Or       = TFunc (firstBV Or)       (inType Or)       (ty' Or)
ty Not      = TFunc (firstBV Not)      (inType Not)      (ty' Not)
ty Eqv      = TFunc (firstBV Eqv)      (inType Eqv)      (ty' Eqv)
ty Leq      = TFunc (firstBV Leq)      (inType Leq)      (ty' Leq)
ty (Leqn n) = TFunc (firstBV (Leqn n)) (inType (Leqn n)) (ty' (Leqn n))
ty Eq       = TFunc (firstBV Eq)       (inType Eq)       (ty' Eq)
ty (Eqn n)  = TFunc (firstBV (Eqn n))  (inType (Eqn n))  (ty' (Eqn n))
{- this is the real definition
ty And      = TFunc 1 (TRefn TBool 1 (Bc True)) 
                  (TFunc 2 (TRefn TBool 2 (Bc True)) 
                      (TRefn TBool 3 (refn_pred And)))
ty Or       = TFunc 1 (TRefn TBool 1 (Bc True)) 
                  (TFunc 2 (TRefn TBool 2 (Bc True)) 
                      (TRefn TBool 3  (refn_pred Or)))
ty Not      = TFunc 2 (TRefn TBool 2 (Bc True)) 
                  (TRefn TBool 3 (refn_pred Not))
ty Eqv      = TFunc 1 (TRefn TBool 1 (Bc True))
                  (TFunc 2 (TRefn TBool 2 (Bc True))  
                      (TRefn TBool 3 (refn_pred Eqv)))
ty Leq      = TFunc 1 (TRefn TInt 1 (Bc True)) 
                  (TFunc 2 (TRefn TInt 2 (Bc True)) 
                      (TRefn TBool 3 (refn_pred Leq)))
ty (Leqn n) = TFunc 2 (TRefn TInt 2 (Bc True)) 
                  (TRefn TBool 3 (refn_pred (Leqn n)))
ty Eq       = TFunc 1 (TRefn TInt 1 (Bc True)) 
                  (TFunc 2 (TRefn TInt 2 (Bc True)) 
                      (TRefn TBool 3 (refn_pred Eq)))
ty (Eqn n)  = TFunc 2 (TRefn TInt 2 (Bc True)) 
                  (TRefn TBool 3 (refn_pred (Eqn n))) -}

{-@ reflect firstBV @-}
firstBV :: Prim -> Int
firstBV Not      = 2
firstBV (Leqn _) = 2
firstBV (Eqn _)  = 2
firstBV _        = 1

{-@ reflect inType @-}
{-@ inType :: c:Prim -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
--                                   && noDefnsInRefns Empty t && isWellFormed Empty t Base } @-}
inType :: Prim -> Type
inType And = TRefn TBool 1 (Bc True)
inType Or  = TRefn TBool 1 (Bc True)
inType Eqv = TRefn TBool 1 (Bc True)
inType Not = TRefn TBool 2 (Bc True)
inType Leq = TRefn TInt 1 (Bc True)
inType Eq  = TRefn TInt 1 (Bc True)
inType _   = TRefn TInt 2 (Bc True)

{-@ reflect ty' @-}
{-@ ty' :: c:Prim -> { t:Type | Set_emp (free t) && Set_emp (freeTV t) } @-}
--                && noDefnsInRefns (Cons (firstBV c) (inType c) Empty) (unbindT (firstBV c) (firstBV c) t) 
--                && isWellFormed (Cons (firstBV c) (inType c) Empty) (unbindT (firstBV c) (firstBV c) t) Star } @-}
ty' :: Prim -> Type
ty' And      = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3 (refn_pred And))
ty' Or       = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3  (refn_pred Or))
ty' Not      = TRefn TBool 3 (refn_pred Not)
ty' Eqv      = TFunc 2 (TRefn TBool 2 (Bc True)) (TRefn TBool 3 (refn_pred Eqv))
ty' Leq      = TFunc 2 (TRefn TInt 2 (Bc True)) (TRefn TBool 3 (refn_pred Leq))
ty' (Leqn n) = TRefn TBool 3 (refn_pred (Leqn n))
ty' Eq       = TFunc 2 (TRefn TInt 2 (Bc True)) (TRefn TBool 3 (refn_pred Eq))
ty' (Eqn n)  = TRefn TBool 3 (refn_pred (Eqn n))


------------------------------------------------------------
---- | Limited Bi-directional TYPE Checking and Synthesis --
------------------------------------------------------------
--
-- The only expressions fow which we are trying to automate the production of
--    are the refinements found in the types of the built in primitives, in ty(c)
--    These consist of constants, primitives, variables and function application only. In
--    particular this rules out lambdas, Lambdas and polymorphic type application

{-@ reflect noDefns @-}
noDefns :: Expr -> Bool
noDefns (Bc _)          = True
noDefns (Ic _)          = True
noDefns (BV _)          = True
noDefns (FV _)          = True
noDefns (Prim _)        = True
noDefns (Lambda _ _)    = False
noDefns (App e e')      = (noDefns e) && (noDefns e')
noDefns (LambdaT _ _ _) = False
noDefns (AppT e t)      = False -- was: (noDefns e)
noDefns (Let _ _ _)     = False
noDefns (Annot e t)     = noDefns e
noDefns Crash           = True

{-@ reflect checkType @-}
{-@ checkType :: FEnv -> { e:Expr | noDefns e } -> t:FType -> Bool / [esize e] @-}
checkType :: FEnv -> Expr -> FType -> Bool
checkType g (Bc b) t         = ( t == FTBasic TBool )
checkType g (Ic n) t         = ( t == FTBasic TInt )
checkType g (Prim c) t       = ( t == erase (ty c) )
checkType g (BV x) t         = False
checkType g (FV x) t         = bound_inF x t g
checkType g (App e e') t     = case ( synthType g e' ) of
    (Just t')       -> checkType g e (FTFunc t' t)
    _               -> False
{-checkType g (AppT e t2) t    = case ( synthType g e ) of
    (Just (FTPoly a k t1))  -> ( t == ftsubBV a (erase t2) t1 ) &&
                               ( S.isSubsetOf (free t2) (bindsF g) ) &&
                               ( S.isSubsetOf (freeTV t2) (bindsF g) )
    _                       -> False -}
checkType g (Annot e liqt) t   = ( checkType g e t ) && ( t == erase liqt ) &&
                                 ( S.isSubsetOf (free liqt) (bindsF g) ) &&
                                 ( S.isSubsetOf (freeTV liqt) (bindsF g) )
                                 {- ( S.null (tfreeBV liqt) ) -}
checkType g Crash t            = False -- Crash is untypable

{-@ reflect synthType @-}
{-@ synthType :: FEnv -> { e:Expr | noDefns e } -> Maybe FType / [esize e] @-}
synthType :: FEnv -> Expr -> Maybe FType
synthType g (Bc b)          = Just ( FTBasic TBool )
synthType g (Ic n)          = Just ( FTBasic TInt )
synthType g (Prim c)        = Just ( erase (ty c) )
synthType g (BV x)          = Nothing
synthType g (FV x)          = lookupF x g
synthType g (App e e')      = case ( synthType g e' ) of
    Nothing    -> Nothing
    (Just t')  -> case ( synthType g e ) of
        (Just (FTFunc t_x t)) -> if ( t_x == t' ) then Just t else Nothing
        _                     -> Nothing
{-synthType g (AppT e t2)     = case ( synthType g e ) of
    (Just (FTPoly a k t1))    -> case ( S.isSubsetOf (free t2)   (bindsF g) &&
                                        S.isSubsetOf (freeTV t2) (bindsF g) ) of
	True  -> Just (ftsubBV a (erase t2) t1)
        False -> Nothing
    _                         -> Nothing -}
synthType g (Annot e liqt)  = case ( checkType g e (erase liqt) && -- S.null (tfreeBV liqt) &&
                                     S.isSubsetOf (free liqt) (bindsF g) &&
                                     S.isSubsetOf (freeTV liqt) (bindsF g) ) of
    True  -> Just (erase liqt)
    False -> Nothing
synthType g Crash           = Nothing

{-@ lem_check_synth :: g:FEnv -> { e:Expr | noDefns e } -> { t:FType | synthType g e == Just t }
                              -> { pf:_ | checkType g e t } @-}
lem_check_synth :: FEnv -> Expr -> FType -> Proof
lem_check_synth g (Bc b) t         = case t of 
    (FTBasic TBool) -> ()
lem_check_synth g (Ic n) t         = case t of
    (FTBasic TInt)  -> () 
lem_check_synth g (Prim c) t       = ()
lem_check_synth g (FV x) t         = lem_lookup_boundinF x t g 
lem_check_synth g (App e e') t     = case (synthType g e') of
    (Just t')       -> lem_check_synth g e (FTFunc t' t)   -- where  (Just t') = synthType g e' 
    Nothing         -> impossible ""
{-lem_check_synth g (AppT e t2) t    = case (synthType g e) of 
    (Just (FTPoly a k t1))  -> ()-}
lem_check_synth g (Annot e liqt) t = ()

{-@ makeHasFType :: g:FEnv -> { e:Expr | noDefns e } -> { t:FType | checkType g e t }
        -> ProofOf(HasFType g e t) / [esize e] @-}
makeHasFType :: FEnv -> Expr -> FType -> HasFType
makeHasFType g (Bc b) t         = case t of
    (FTBasic TBool) -> FTBC g b
makeHasFType g (Ic n) t         = case t of
    (FTBasic TInt)  -> FTIC g n
makeHasFType g (Prim c) t       = FTPrm g c
makeHasFType g (FV x) t         = simpleFTVar g (x? lem_boundin_inenvF x t g ) t
makeHasFType g (App e e') t     = FTApp g e t' t pf_e_t't e' pf_e'_t'
  where
    (Just t')  = synthType g e'
    pf_e_t't   = makeHasFType g e (FTFunc t' t)
    pf_e'_t'   = makeHasFType g e' (t' ? lem_check_synth g e' t')
{- makeHasFType g (AppT e rt) t    = FTAppT g e a k t1 pf_e_at1 rt {- wfft rt -}
  where
    (Just (FTPoly a k t1)) = synthType g e 
    pf_e_at1               = makeHasFType g e (FTPoly a k t1 ? lem_check_synth g e (FTPoly a k t1)) -}
makeHasFType g (Annot e liqt) t = FTAnn g e t liqt pf_e_t
  where
    pf_e_t = makeHasFType g e t


