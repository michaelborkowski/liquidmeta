{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}  
{-@ LIQUID "--no-totality" @-}      -- TODO: assume
{-@ LIQUID "--reflection"  @-}
{- @ LIQUID "--ple-local"         @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}

module PLELocalTest where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

semantics = (Step, EvalsTo)

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
    FTAbs  :: FEnv -> Vname -> FType -> Expr -> FType -> Vname -> HasFType -> HasFType
    FTApp  :: FEnv -> Expr -> FType -> FType -> HasFType 
                   -> Expr -> HasFType -> HasFType
    FTAbsT :: FEnv -> Vname -> Kind -> Expr -> FType -> Vname -> HasFType -> HasFType
    FTAppT :: FEnv -> Expr -> Vname -> Kind -> FType -> HasFType -> Type -> HasFType
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
 |  FTAbs  :: g:FEnv -> x:Vname -> b:FType -> e:Expr -> b':FType
                -> { y:Vname | not (in_envF y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasFType (FCons y b g) (unbind x y e) b')
                -> ProofOf(HasFType g (Lambda x e) (FTFunc b b'))
 |  FTApp  :: g:FEnv -> e:Expr -> b:FType -> b':FType
                -> ProofOf(HasFType g e (FTFunc b b')) 
                -> e':Expr -> ProofOf(HasFType g e' b) 
                -> ProofOf(HasFType g (App e e') b')
 |  FTAbsT :: g:FEnv -> a:Vname -> k:Kind -> e:Expr -> b:FType
                -> { a':Vname | not (in_envF a' g) && not (Set_mem a' (fv e)) && not (Set_mem a' (ftv e)) }
                -> ProofOf(HasFType (FConsT a' k g) (unbind_tv a a' e) b)
                -> ProofOf(HasFType g (LambdaT a k e) (FTPoly a k b))
 |  FTAppT :: g:FEnv -> e:Expr -> a:Vname -> k:Kind -> t':FType
                -> ProofOf(HasFType g e (FTPoly a k t')) 
                -> t:Type -> ProofOf(HasFType g (AppT e t) (ftsubBV a (erase t) t'))
 |  FTLet  :: g:FEnv -> e_x:Expr -> b:FType -> ProofOf(HasFType g e_x b)
                -> x:Vname -> e:Expr -> b':FType 
                -> { y:Vname | not (in_envF y g) && not (Set_mem y (fv e)) }
                -> ProofOf(HasFType (FCons y b g) (unbind x y e) b')
                -> ProofOf(HasFType g (Let x e_x e) b')
 |  FTAnn  :: g:FEnv -> e:Expr -> b:FType 
                -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsF g)  }
                -> ProofOf(HasFType g e b) -> ProofOf(HasFType g (Annot e t1) b)  @-} 

-- old version : -> { t1:Type | (erase t1 == b) && Set_sub (free t1) (bindsF g) && Set_emp (tfreeBV t1) }
  
{-@ measure ftypSize @-}
{-@ ftypSize :: HasFType -> { v:Int | v >= 0 } @-}
ftypSize :: HasFType -> Int
ftypSize (FTBC {})                           = 1
ftypSize (FTIC {})                           = 1
ftypSize (FTVar1 {})                         = 1
ftypSize (FTVar2 _ _ _ p_x_b _ _)            = (ftypSize p_x_b)   + 1
ftypSize (FTAbs _ _ _ _ _ _ p_e_b')          = (ftypSize p_e_b')  + 1
ftypSize (FTApp _ _ _ _ p_e_bb' _ p_e'_b)    = (ftypSize p_e_bb') + (ftypSize p_e'_b) + 1
ftypSize (FTAbsT _ _ _ _ _ _ p_e_b)          = (ftypSize p_e_b)  + 1
ftypSize (FTAppT _ _ _ _ _ p_e_at' _)        = (ftypSize p_e_at') + 1
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




------------------------------------------------------------
---- | Limited Bi-directional TYPE Checking and Synthesis --
------------------------------------------------------------
--
-- The only expressions fow which we are trying to automate the production of
--    are the refinements found in the types of the built in primitives, in ty(c)
--    These consist of constants, primitives, variables and function application only.

{- @ automatic-instances noDefns @-}
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
noDefns (AppT e t)      = (noDefns e) -- && (noDefns e')
noDefns (Let _ _ _)     = False
noDefns (Annot e t)     = noDefns e
noDefns Crash           = True

{- @ automatic-instances checkType @-}
{-@ reflect checkType @-}
{- @ checkType :: FEnv -> { e:Expr | noDefns e } -> t:FType -> Bool / [esize e] @-}
{-@ checkType :: FEnv -> e:Expr -> t:FType -> Bool / [esize e] @-}
checkType :: FEnv -> Expr -> FType -> Bool
checkType g (Bc b) t         = ( t == FTBasic TBool )
checkType g (Ic n) t         = ( t == FTBasic TInt )
checkType g (BV x) t         = False
checkType g (FV x) t         = bound_inF x t g
checkType g (App e e') t     = case ( synthType g e' ) of
    (Just t')       -> checkType g e (FTFunc t' t)
    _               -> False
checkType g (AppT e t2) t    = case ( synthType g e ) of
    (Just (FTPoly a k t1))    -> ( t == ftsubBV a (erase t2) t1 )
    _                       -> False
checkType g (Annot e liqt) t   = ( checkType g e t ) && ( t == erase liqt ) &&
                                 ( S.isSubsetOf (free liqt) (bindsF g) ) {- &&
                                 ( S.null (tfreeBV liqt) ) -}
checkType g Crash t            = False -- Crash is untypable
checkType g _ t                = False   

{- @ automatic-instances synthType @-}
{-@ reflect synthType @-}
{- @ synthType :: FEnv -> { e:Expr | noDefns e } -> Maybe FType / [esize e] @-}
{-@ synthType :: FEnv -> e:Expr -> Maybe FType / [esize e] @-}
synthType :: FEnv -> Expr -> Maybe FType
synthType g (Bc b)          = Just ( FTBasic TBool )
synthType g (Ic n)          = Just ( FTBasic TInt )
synthType g (BV x)          = Nothing
synthType g (FV x)          = lookupF x g
synthType g (App e e')      = case ( synthType g e' ) of
    Nothing    -> Nothing
    (Just t')  -> case ( synthType g e ) of
        (Just (FTFunc t_x t)) -> if ( t_x == t' ) then Just t else Nothing
        _                     -> Nothing
synthType g (AppT e t2)     = case ( synthType g e ) of
    (Just (FTPoly a k t1))   -> Just (ftsubBV a (erase t2) t1)
    _                      -> Nothing
synthType g (Annot e liqt)  = case ( checkType g e (erase liqt) && -- S.null (tfreeBV liqt) &&
                                     S.isSubsetOf (free liqt) (bindsF g) ) of
    True  -> Just (erase liqt)
    False -> Nothing
synthType g Crash           = Nothing
synthType g _               = Nothing

{- @ automatic-instances lem_check_synth @-}
{-@ lem_check_synth :: g:FEnv -> { e:Expr | noDefns e } -> { t:FType | synthType g e == Just t }
                              -> { pf:_ | checkType g e t } @-}
lem_check_synth :: FEnv -> Expr -> FType -> Proof
lem_check_synth g (Bc b) t         = case t of 
    (FTBasic TBool) -> ()
lem_check_synth g (Ic n) t         = case t of
    (FTBasic TInt)  -> () 
lem_check_synth g (FV x) t         = lem_lookup_boundinF x t g 
lem_check_synth g (App e e') t     = case (synthType g e') of
    (Just t')       -> lem_check_synth g e (FTFunc t' t)   -- where  (Just t') = synthType g e' 
    Nothing         -> impossible ""
lem_check_synth g (AppT e t2) t    = () -- TODO: recheck this
  where
    (Just (FTPoly a k t1)) = synthType g e
lem_check_synth g (Annot e liqt) t = ()


{- @ automatic-instances makeHasFType @-}
{-@ makeHasFType :: g:FEnv -> { e:Expr | noDefns e } -> { t:FType | checkType g e t }
        -> ProofOf(HasFType g e t) / [esize e] @-}
makeHasFType :: FEnv -> Expr -> FType -> HasFType
makeHasFType g (Bc b) t         = case t of
    (FTBasic TBool) -> FTBC g b
makeHasFType g (Ic n) t         = case t of
    (FTBasic TInt)  -> FTIC g n
makeHasFType g (FV x) t         = simpleFTVar g (x? lem_boundin_inenvF x t g ) t
{-
makeHasFType g (App e e') t     = FTApp g e t' t pf_e_t't e' pf_e'_t'
  where
    (Just t')  = synthType g e'
    pf_e_t't   = makeHasFType g e (FTFunc t' t)
    pf_e'_t'   = makeHasFType g e' (t' ? lem_check_synth g e' t')
makeHasFType g (AppT e t2) t    = FTAppT g e a k t1 pf_e_at1 t2
  where
    (Just (FTPoly a k t1)) = synthType g e 
    pf_e_at1               = makeHasFType g e (FTPoly a k t1)
makeHasFType g (Annot e liqt) t = FTAnn g e t liqt pf_e_t
  where
    pf_e_t = makeHasFType g e t
-}
