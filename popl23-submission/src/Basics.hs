{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Basics where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
  ---   Term level expressions 
  ---   We use the locally nameless representation for variables
  ---     "free" variables are named with ints because easier to pick fresh ones
  ---     "bound" ones are deBruijn indices, separate series for BV and BTV

{-@ type Vname =  { v:Int | v >= 0 } @-} 
type Vname = Int

{-@ type Index =  { v:Int | v >= 0 } @-} 
type Index = Int

data Prim = And | Or | Not | Eqv | Imp
          | Leq | Leqn Int              
          | Eq  | Eqn Int 
          | Leql | Eql                 -- Leql and Eql are polymorphic
  deriving (Eq, Show)   

{-@ data Expr where
        Bc      :: Bool  -> Expr
        Ic      :: Int   -> Expr
        Prim    :: Prim  -> Expr 
        BV      :: Index -> Expr
        FV      :: Vname -> Expr
        Lambda  :: Expr  -> Expr
        App     :: Expr  -> Expr -> Expr
        LambdaT :: Kind  -> Expr -> Expr
        AppT    :: Expr  -> Type -> Expr
        Let     :: Expr  -> Expr -> Expr
        Annot   :: Expr  -> Type -> Expr @-} 
data Expr = Bc Bool                   -- True, False
          | Ic Int                    -- 0, 1, 2, ...
          | Prim Prim                 -- built-in primitive functions 
          | BV Index                  -- BOUND Variables: bound to a Lambda, Let or :t
          | FV Vname                  -- FREE Variables: bound in an environment
          | Lambda Expr               -- \x.e          abstractions    (x is nameless)
          | App Expr Expr             -- e e'          applications
          | LambdaT Kind Expr         -- /\a:k.e  type abstractions    (a is nameless)
          | AppT Expr Type            -- e [bt]   type applications 
          | Let Expr Expr             -- let x = e1 in e2              (x is nameless)
          | Annot Expr Type           -- e : t
  deriving Eq

{-@ lazy esize @-}
{-@ measure esize @-}
{-@ esize :: e:Expr -> { v:Int | v >= 0 } @-}
esize :: Expr -> Int      
esize (Bc _)            = 1
esize (Ic _)            = 1
esize (Prim _)          = 1
esize (BV _)            = 1
esize (FV _)            = 1
esize (Lambda   e)      = (esize e)   + 1
esize (App e e')        = (esize e)   + (esize e') + 1
esize (LambdaT   k e)   = (esize e)   + 1
esize (AppT e t)        = (esize e)   + (tsize t) + 1
esize (Let   e_x e)     = (esize e_x) + (esize e) + 1
esize (Annot e t)       = (esize e)   + (tsize t) + 1

{-@ type Value = { v:Expr | isValue v } @-}

{-@ reflect isValue @-} -- meaning: is a syntactic value 
isValue :: Expr -> Bool
isValue (Bc _)          = True
isValue (Ic _)          = True
isValue (Prim c)        = True
isValue (FV _)          = True 
isValue (BV _)          = True 
isValue (Lambda   e)    = True 
isValue (LambdaT   k e) = True
isValue _               = False


{-@ measure fv @-} 
{-@ fv :: e:Expr -> S.Set Vname / [esize e] @-}
fv :: Expr -> S.Set Vname
fv (Bc _)          = S.empty
fv (Ic _)          = S.empty
fv (Prim _)        = S.empty
fv (BV _)          = S.empty
fv (FV x)          = S.singleton x
fv (Lambda   e)    = fv e 
fv (App e e')      = S.union (fv e) (fv e')
fv (LambdaT   k e) = fv e
fv (AppT e t)      = S.union (fv e) (free t)
fv (Let   ex e)    = S.union (fv ex) (fv e)
fv (Annot e t)     = S.union (fv e) (free t) 

{-@ measure fvList @-} 
{-@ fvList :: e:Expr -> { xs:Names | listElts xs == fv e } / [esize e] @-}
fvList :: Expr -> Names
fvList (Bc _)          = []
fvList (Ic _)          = []
fvList (Prim _)        = []
fvList (BV _)          = []
fvList (FV x)          = [x]
fvList (Lambda   e)    = fvList e 
fvList (App e e')      = union (fvList e) (fvList e')
fvList (LambdaT   k e) = fvList e
fvList (AppT e t)      = union (fvList e) (freeList t)
fvList (Let   ex e)    = union (fvList ex) (fvList e)
fvList (Annot e t)     = union (fvList e) (freeList t) 

{-@ measure ftv @-}
{-@ ftv :: e:Expr -> S.Set Vname / [esize e] @-}
ftv :: Expr -> S.Set Vname
ftv (Bc _)          = S.empty
ftv (Ic _)          = S.empty
ftv (Prim _)        = S.empty
ftv (BV _)          = S.empty
ftv (FV x)          = S.empty -- differs from fv
ftv (Lambda   e)    = ftv e 
ftv (App e e')      = S.union (ftv e) (ftv e')
ftv (LambdaT   k e) = ftv e
ftv (AppT e t)      = S.union (ftv e) (freeTV t)
ftv (Let   ex e)    = S.union (ftv ex) (ftv e) 
ftv (Annot e t)     = S.union (ftv e) (freeTV t) -- fv e

{-@ reflect isLC @-} 
isLC :: Expr -> Bool
isLC e = isLC_at 0 0 e

{-@ reflect isLC_at @-}
{-@ isLC_at :: Index -> Index -> e:Expr -> Bool / [esize e] @-}
isLC_at :: Index -> Index -> Expr -> Bool
isLC_at j_x j_a (Bc _)         = True
isLC_at j_x j_a (Ic _)         = True
isLC_at j_x j_a (Prim _)       = True
isLC_at j_x j_a (BV i)         = i < j_x
isLC_at j_x j_a (FV _)         = True
isLC_at j_x j_a (Lambda e)     = isLC_at (j_x+1) j_a e
isLC_at j_x j_a (App e e')     = isLC_at j_x j_a e     && isLC_at j_x j_a e'
isLC_at j_x j_a (LambdaT k e)  = isLC_at j_x (j_a+1) e
isLC_at j_x j_a (AppT e t)     = isLC_at j_x j_a e     && isLCT_at j_x j_a t
isLC_at j_x j_a (Let ex e)     = isLC_at j_x j_a ex    && isLC_at (j_x+1) j_a e 
isLC_at j_x j_a (Annot e t)    = isLC_at j_x j_a e     && isLCT_at j_x j_a t

{-@ reflect unbind @-} -- unbind opens (BV i) to (FV y) in e 
{-@ unbind :: y:Vname -> e:Expr 
                -> { e':Expr | Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                               Set_sub (fv e) (fv e') && 
                               Set_sub (ftv e) (ftv e') && Set_sub (ftv e') (ftv e) &&
                               esize e == esize e' } / [esize e] @-}
unbind :: Vname -> Expr -> Expr
unbind y e = open_at 0 y e -- subBV x (FV y) e

{-@ reflect open_at @-}
{-@ open_at :: j:Index -> y:Vname -> e:Expr
                 -> { e':Expr | Set_sub (fv e') (Set_cup (Set_sng y) (fv e)) &&
                                Set_sub (fv e) (fv e') &&
                                Set_sub (ftv e) (ftv e') && Set_sub (ftv e') (ftv e) &&
                                esize e == esize e' } / [esize e] @-}
open_at :: Index -> Vname -> Expr -> Expr
open_at j y (Bc b)             = Bc b
open_at j y (Ic n)             = Ic n
open_at j y (Prim c)           = Prim c
open_at j y (BV i) | i == j    = FV y
                   | otherwise = BV i
open_at j y (FV x)             = FV x
open_at j y (Lambda e)         = Lambda (open_at (j+1) y e)
open_at j y (App e e')         = App   (open_at j y e)  (open_at j y e')
open_at j y (LambdaT k e)      = LambdaT k (open_at j y e)  -- not j+1
open_at j y (AppT e t)         = AppT  (open_at j y e)  (openT_at j y t)
open_at j y (Let ex e)         = Let   (open_at j y ex) (open_at (j+1) y e)
open_at j y (Annot e t)        = Annot (open_at j y e)  (openT_at j y t)

{-@ reflect unbind_tv @-} -- unbind converts (BTV a) to (FTV a') in e -- aka "chgBTV"
{-@ unbind_tv :: a':Vname -> e:Expr 
                    -> { e':Expr | Set_sub (ftv e') (Set_cup (Set_sng a') (ftv e)) &&
                                   Set_sub (ftv e) (ftv e') && 
                                   Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (fv e)  &&  esize e == esize e' &&
                                   ( e == Bc True => e' == Bc True ) } / [esize e] @-}
unbind_tv :: Vname -> Expr -> Expr
unbind_tv a' e = open_tv_at 0 a' e

{-@ reflect open_tv_at @-}
{-@ open_tv_at :: j:Index -> a':Vname -> e:Expr
                    -> { e':Expr | Set_sub (ftv e') (Set_cup (Set_sng a') (ftv e)) &&
                                   Set_sub (ftv e) (ftv e') && 
                                   Set_sub (fv e) (fv e') && 
                                   Set_sub (fv e') (fv e)  &&  esize e == esize e' } / [esize e] @-}
open_tv_at :: Index -> Vname -> Expr -> Expr
open_tv_at j a' (Bc b)                       = Bc b
open_tv_at j a' (Ic n)                       = Ic n
open_tv_at j a' (Prim p)                     = Prim p
open_tv_at j a' (BV i)                       = BV i -- looking for type vars
open_tv_at j a' (FV y)                       = FV y
open_tv_at j a' (Lambda e)                   = Lambda    (open_tv_at j a' e)  -- not j+1
open_tv_at j a' (App e e')                   = App       (open_tv_at j a' e)  (open_tv_at j a' e')
open_tv_at j a' (LambdaT k e)                = LambdaT k (open_tv_at (j+1) a' e)
open_tv_at j a' (AppT e t)                   = AppT      (open_tv_at j a' e)  (open_tvT_at j a' t)
open_tv_at j a' (Let e1 e2  )                = Let       (open_tv_at j a' e1) (open_tv_at  j a' e2) --not j+1
open_tv_at j a' (Annot e t)                  = Annot     (open_tv_at j a' e)  (open_tvT_at j a' t)

  --- TERM-LEVEL SUBSTITUTION
{-@ reflect subFV @-} -- substitute a value for a term variable in a term 
{-@ subFV :: x:Vname -> { v:Expr | isValue v } -> e:Expr
                     -> { e':Expr | (Set_mem x (fv e) || e == e') &&
                      ( Set_sub (fv e') (Set_cup (fv v) (Set_dif (fv e) (Set_sng x)))) &&
                      ( (not (Set_mem x (fv v))) => not (Set_mem x (fv e')) ) && 
                        Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                      ( e == Bc True => e' == Bc True )  &&
                      ( isValue e => isValue e' ) } / [esize e] @-}
subFV :: Vname -> Expr -> Expr -> Expr
subFV x v_x (Bc b)                    = Bc b
subFV x v_x (Ic n)                    = Ic n
subFV x v_x (Prim p)                  = Prim p
subFV x v_x (BV i)                    = BV i
subFV x v_x (FV y) | x == y           = v_x  
                   | otherwise        = FV y
subFV x v_x (Lambda   e)              = Lambda    (subFV x v_x e)
subFV x v_x (App e e')                = App   (subFV x v_x e)  (subFV x v_x e')
subFV x v_x (LambdaT   k e)           = LambdaT   k (subFV x v_x e)
subFV x v_x (AppT e bt)               = AppT  (subFV x v_x e) (tsubFV x v_x bt)
subFV x v_x (Let   e1 e2)             = Let   (subFV x v_x e1) (subFV x v_x e2)
subFV x v_x (Annot e t)               = Annot (subFV x v_x e) (tsubFV x v_x t) 

{-@ reflect subFTV @-} -- substitute a type for a type variable in a term  
{-@ subFTV :: a:Vname -> t:UserType -> e:Expr 
                      -> { e':Expr | (Set_mem a (ftv e) || e == e') &&
                       ( Set_sub (ftv e') (Set_cup (freeTV t) (Set_dif (ftv e) (Set_sng a)))) &&
                         Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                       ( isValue e => isValue e' ) && 
                       ( e == Bc True => e' == Bc True )} / [esize e] @-}
subFTV :: Vname -> Type -> Expr -> Expr
subFTV a t_a (Bc b)                    = Bc b
subFTV a t_a (Ic n)                    = Ic n
subFTV a t_a (Prim p)                  = Prim p
subFTV a t_a (BV i)                    = BV i
subFTV a t_a (FV y)                    = FV y
subFTV a t_a (Lambda   e)              = Lambda     (subFTV a t_a e)
subFTV a t_a (App e e')                = App   (subFTV a t_a e)  (subFTV a t_a e')
subFTV a t_a (LambdaT    k e)          = LambdaT    k (subFTV a t_a e)
subFTV a t_a (AppT e t)                = AppT  (subFTV a t_a e) (tsubFTV a t_a t)
subFTV a t_a (Let   e1 e2)             = Let   (subFTV a t_a e1) (subFTV a t_a e2)
subFTV a t_a (Annot e t)               = Annot (subFTV a t_a e) (tsubFTV a t_a t) 

{-@ reflect subBV @-} -- unbind opens (BV 0) to v in e 
{-@ subBV :: v:Value -> e:Expr 
                -> { e':Expr | Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                               Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                             ( esize v != 1 || esize e == esize e') } / [esize e] @-}
subBV :: Expr -> Expr -> Expr
subBV v e = subBV_at 0 v e 

{-@ reflect subBV_at @-}
{-@ subBV_at :: j:Index -> v:Value -> e:Expr
                 -> { e':Expr | Set_sub (fv e') (Set_cup (fv e) (fv v)) &&
                                Set_sub (ftv e') (Set_cup (ftv e) (ftv v)) &&
                              ( esize v != 1 || esize e == esize e') } / [esize e] @-}
subBV_at :: Index -> Expr -> Expr -> Expr
subBV_at j v (Bc b)             = Bc b
subBV_at j v (Ic n)             = Ic n
subBV_at j v (Prim c)           = Prim c
subBV_at j v (BV i) | i == j    = v
                    | otherwise = BV i
subBV_at j v (FV x)             = FV x
subBV_at j v (Lambda e)         = Lambda (subBV_at (j+1) v e)
subBV_at j v (App e e')         = App   (subBV_at j v e)  (subBV_at j v e')
subBV_at j v (LambdaT k e)      = LambdaT k (subBV_at j v e)  -- not j+1
subBV_at j v (AppT e t)         = AppT  (subBV_at j v e)  (tsubBV_at j v t)
subBV_at j v (Let ex e)         = Let   (subBV_at j v ex) (subBV_at (j+1) v e)
subBV_at j v (Annot e t)        = Annot (subBV_at j v e)  (tsubBV_at j v t)

{-@ reflect subBTV @-} -- substitute in a type for a BOUND TYPE var
{-@ subBTV :: t:UserType -> e:Expr
                     -> { e':Expr | Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (freeTV t)) &&
                                    ( e == Bc True => e' == Bc True ) } / [esize e] @-}
subBTV :: Type -> Expr -> Expr
subBTV t e = subBTV_at 0 t e

{-@ reflect subBTV_at @-} -- substitute in a type for a BOUND TYPE var
{-@ subBTV_at :: j:Index -> t:UserType -> e:Expr
                     -> { e':Expr | Set_sub (fv e') (Set_cup (fv e) (free t)) &&
                                    Set_sub (ftv e') (Set_cup (ftv e) (freeTV t)) &&
                                    ( e == Bc True => e' == Bc True ) } / [esize e] @-}
subBTV_at :: Index -> Type -> Expr -> Expr
subBTV_at j t_a (Bc b)                       = Bc b
subBTV_at j t_a (Ic n)                       = Ic n
subBTV_at j t_a (Prim p)                     = Prim p
subBTV_at j t_a (BV y)                       = BV y -- looking for type vars
subBTV_at j t_a (FV y)                       = FV y
subBTV_at j t_a (Lambda   e)                 = Lambda    (subBTV_at j t_a e)  -- not j+1
subBTV_at j t_a (App e e')                   = App       (subBTV_at j t_a e)  (subBTV_at j t_a e')
subBTV_at j t_a (LambdaT  k e)               = LambdaT k (subBTV_at (j+1) t_a e)
subBTV_at j t_a (AppT e t)                   = AppT      (subBTV_at j t_a e) (tsubBTV_at j t_a t)
subBTV_at j t_a (Let   e1 e2)                = Let       (subBTV_at j t_a e1) (subBTV_at j t_a e2) -- not j+1
subBTV_at j t_a (Annot e t)                  = Annot     (subBTV_at j t_a e) (tsubBTV_at j t_a t)

  
  ---  Refinements

data Preds = PEmpty                         -- type Preds = [Expr]
           | PCons  Expr Preds
  deriving Eq
{-@ data Preds where 
        PEmpty :: Preds
        PCons  :: p:Expr -> ps:Preds 
                         -> { ps':Preds | Set_sub (fvP ps') (Set_cup (fv p) (fvP ps)) &&
                                          Set_sub (ftvP ps') (Set_cup (ftv p) (ftvP ps)) } @-}

{-@ lazy predsize @-}
{-@ measure predsize @-}
{-@ predsize :: ps:Preds -> { n:Int | n >= 0 && (not (ps == PEmpty) => n > 0) } @-}
predsize :: Preds -> Int
predsize PEmpty       = 0
predsize (PCons p ps) = predsize ps + esize p + 1

{-@ measure fvP @-}
{-@ fvP :: ps:Preds -> S.Set Vname / [predsize ps] @-}
fvP :: Preds -> S.Set Vname
fvP PEmpty       = S.empty
fvP (PCons p ps) = S.union (fv p) (fvP ps)

{-@ measure fvPList @-}
{-@ fvPList :: ps:Preds -> { xs:Names | listElts xs == fvP ps } / [predsize ps] @-}
fvPList :: Preds -> Names
fvPList PEmpty       = []
fvPList (PCons p ps) = union (fvList p) (fvPList ps)

{-@ measure ftvP @-}
{-@ ftvP :: ps:Preds -> S.Set Vname / [predsize ps] @-}
ftvP :: Preds -> S.Set Vname
ftvP PEmpty       = S.empty
ftvP (PCons p ps) = S.union (ftv p) (ftvP ps)

{-@ reflect isLCP @-}
isLCP :: Preds -> Bool
isLCP PEmpty       = True
isLCP (PCons p ps) = isLC p && isLCP ps

{-@ reflect isLCP_at @-}
{-@ isLCP_at :: Index -> Index -> ps:Preds -> Bool / [predsize ps] @-}
isLCP_at :: Index -> Index -> Preds -> Bool
isLCP_at j_x j_a PEmpty       = True
isLCP_at j_x j_a (PCons p ps) = isLC_at j_x j_a p && isLCP_at j_x j_a ps

{-@ reflect strengthen @-}  -- formerly called `strengthen`
{-@ strengthen :: ps:Preds -> rs:Preds -> { rs':Preds | Set_sub (fvP  rs') (Set_cup (fvP  ps) (fvP  rs)) && 
                                                        Set_sub (ftvP rs') (Set_cup (ftvP ps) (ftvP rs)) } @-}
strengthen :: Preds -> Preds -> Preds
strengthen PEmpty       rs = rs 
strengthen (PCons p ps) rs = PCons p (strengthen ps rs)


{-@ reflect unbindP @-}
{-@ unbindP :: y:Vname -> ps:Preds
                 -> { ps':Preds | Set_sub (fvP ps') (Set_cup (Set_sng y) (fvP ps)) &&
                                  Set_sub (fvP ps) (fvP ps') &&
                                  Set_sub (ftvP ps') (ftvP ps) && Set_sub (ftvP ps) (ftvP ps') &&
                                  predsize ps == predsize ps' } / [predsize ps] @-}
unbindP :: Vname -> Preds -> Preds
unbindP y PEmpty       = PEmpty
unbindP y (PCons p ps) = PCons (unbind y p) (unbindP y ps)

{-@ reflect openP_at @-}
{-@ openP_at :: j:Index -> y:Vname -> ps:Preds
                  -> { ps':Preds | Set_sub (fvP ps') (Set_cup (Set_sng y) (fvP ps)) &&
                                   Set_sub (fvP ps) (fvP ps') &&
                                   Set_sub (ftvP ps') (ftvP ps) && Set_sub (ftvP ps) (ftvP ps') &&
                                   predsize ps == predsize ps' } / [predsize ps] @-}
openP_at :: Index -> Vname -> Preds -> Preds
openP_at j y PEmpty       = PEmpty
openP_at j y (PCons p ps) = PCons (open_at j y p) (openP_at j y ps)

{-@ reflect unbind_tvP @-}
{-@ unbind_tvP :: a':Vname -> ps:Preds
                     -> { ps':Preds | Set_sub (ftvP ps') (Set_cup (Set_sng a') (ftvP ps)) &&
                                      Set_sub (fvP ps') (fvP ps)  &&  
                                      Set_sub (fvP ps) (fvP ps') && Set_sub (ftvP ps) (ftvP ps') &&
                                      predsize ps == predsize ps' } / [predsize ps] @-}
unbind_tvP :: Vname -> Preds -> Preds
unbind_tvP a' PEmpty       = PEmpty
unbind_tvP a' (PCons p ps) = PCons (unbind_tv a' p) (unbind_tvP a' ps)

{-@ reflect open_tvP_at @-}
{-@ open_tvP_at :: j:Index -> a':Vname -> ps:Preds
                    -> { ps':Preds | Set_sub (ftvP ps') (Set_cup (Set_sng a') (ftvP ps)) &&
                                     Set_sub (fvP ps') (fvP ps)  &&  
                                     Set_sub (fvP ps) (fvP ps') && Set_sub (ftvP ps) (ftvP ps') &&
                                     predsize ps == predsize ps' } / [predsize ps] @-}
open_tvP_at :: Index -> Vname -> Preds -> Preds
open_tvP_at j a' PEmpty       = PEmpty
open_tvP_at j a' (PCons p ps) = PCons (open_tv_at j a' p) (open_tvP_at j a' ps)

--  |  SUBSTITUTION IN PREDICATES
{-@ reflect psubFV @-} -- substitute a value for a term variable 
{-@ psubFV :: x:Vname -> { v:Expr | isValue v } -> ps:Preds
                      -> { ps':Preds | (Set_mem x (fvP ps) || ps == ps') &&
                       ( Set_sub (fvP ps') (Set_cup (fv v) (Set_dif (fvP ps) (Set_sng x)))) &&
                       ( (not (Set_mem x (fv v))) => not (Set_mem x (fvP ps')) ) &&
                         Set_sub (ftvP ps') (Set_cup (ftvP ps) (ftv v)) } / [predsize ps] @-}
psubFV :: Vname -> Expr -> Preds -> Preds
psubFV x v_x PEmpty       = PEmpty
psubFV x v_x (PCons p ps) = PCons (subFV x v_x p) (psubFV x v_x ps)

{-@ reflect psubFTV @-} -- substitute a type for a type variable
{-@ psubFTV :: a:Vname -> t:UserType -> ps:Preds
                       -> { ps':Preds | (Set_mem a (ftvP ps) || ps == ps') &&
                        ( Set_sub (ftvP ps') (Set_cup (freeTV t) (Set_dif (ftvP ps) (Set_sng a)))) &&
                          Set_sub (fvP ps') (Set_cup (fvP ps) (free t)) } / [predsize ps] @-}
psubFTV :: Vname -> Type -> Preds -> Preds
psubFTV a t_a PEmpty       = PEmpty
psubFTV a t_a (PCons p ps) = PCons (subFTV a t_a p) (psubFTV a t_a ps)

{-@ reflect psubBV @-} -- unbind opens (BV 0) to v in ps
{-@ psubBV :: v:Value -> ps:Preds
                 -> { ps':Preds | Set_sub (fvP ps') (Set_cup (fvP ps) (fv v)) &&
                                  Set_sub (ftvP ps') (Set_cup (ftvP ps) (ftv v)) &&
                                ( esize v != 1 || predsize ps == predsize ps') } / [predsize ps] @-}
psubBV :: Expr -> Preds -> Preds
psubBV v_x PEmpty       = PEmpty
psubBV v_x (PCons p ps) = PCons (subBV v_x p) (psubBV v_x ps)

{-@ reflect psubBV_at @-} -- unbind opens (BV j) to v in ps
{-@ psubBV_at :: j:Index -> v:Value -> ps:Preds
                 -> { ps':Preds | Set_sub (fvP ps') (Set_cup (fvP ps) (fv v)) &&
                                  Set_sub (ftvP ps') (Set_cup (ftvP ps) (ftv v)) &&
                                ( esize v != 1 || predsize ps == predsize ps') } / [predsize ps] @-}
psubBV_at :: Index -> Expr -> Preds -> Preds
psubBV_at j v_x PEmpty       = PEmpty
psubBV_at j v_x (PCons p ps) = PCons (subBV_at j v_x p) (psubBV_at j v_x ps)

{-@ reflect psubBTV @-} -- substitute in a type for a BOUND TYPE var
{-@ psubBTV :: t:UserType -> ps:Preds
                       -> { ps':Preds | Set_sub (fvP ps') (Set_cup (fvP ps) (free t)) &&
                                        Set_sub (ftvP ps') (Set_cup (ftvP ps) (freeTV t)) } / [predsize ps] @-}
psubBTV :: Type -> Preds -> Preds
psubBTV t_a PEmpty       = PEmpty
psubBTV t_a (PCons p ps) = PCons (subBTV t_a p) (psubBTV t_a ps)

{-@ reflect psubBTV_at @-} -- substitute in a type for a BOUND TYPE var
{-@ psubBTV_at :: j:Index -> t:UserType -> ps:Preds
                       -> { ps':Preds | Set_sub (fvP ps') (Set_cup (fvP ps) (free t)) &&
                                        Set_sub (ftvP ps') (Set_cup (ftvP ps) (freeTV t)) } / [predsize ps] @-}
psubBTV_at :: Index -> Type -> Preds -> Preds
psubBTV_at j t_a PEmpty       = PEmpty
psubBTV_at j t_a (PCons p ps) = PCons (subBTV_at j t_a p) (psubBTV_at j t_a ps)


  ---   TYPES

{-@ data Basic where
        TBool ::          Basic
        TInt  ::          Basic
        BTV   :: Index -> Basic
        FTV   :: Vname -> Basic @-}
data Basic = TBool         -- Bool
           | TInt          -- Int
           | BTV     Index   -- a  
           | FTV     Vname   -- a   
  deriving (Eq, Show)

{-@ measure isBTV @-}
isBTV :: Basic -> Bool
isBTV (BTV _) = True
isBTV _       = False

  -- ONLY types with Base Kind may have non-trivial refinements. Star kinded type variables 
  --     may only have the refinement { x : [] }.
data Kind = Base         -- B, base kind
          | Star         -- *, star kind
  deriving (Eq, Show)

{-@ measure ksize @-}
{-@ ksize :: Kind -> { v:Int | v >= 0 } @-}
ksize :: Kind -> Int
ksize Base = 0
ksize Star = 1

data Type where 
    TRefn   :: Basic ->          Preds -> Type     -- b{x0 : [p]}
    TFunc   ::          Type   -> Type -> Type     -- x:t_x -> t
    TExists ::          Type   -> Type -> Type     -- \exists x:t_x. t
    TPoly   ::          Kind   -> Type -> Type     -- \forall a:k. t
  deriving Eq

  -- This would also avoid issues of deBruijn index shifting 
  --   in type variable substitution (in defining push)
{-@ type UserType = { t:Type | noExists t } @-}

{-@ reflect noExists @-}
noExists :: Type -> Bool         
noExists (TRefn b ps)     = True  
noExists (TFunc  t_x t)   = noExists t_x && noExists t
noExists (TExists  t_x t) = False
noExists (TPoly  k   t)   = noExists t

{-@ reflect isMono @-}
{-@ isMono :: UserType -> Bool @-}
isMono :: Type -> Bool
isMono (TRefn _ _)    = True
isMono (TFunc t_x t)  = isMono t_x && isMono t
isMono (TPoly _ _)    = False

{-@ lazy tsize @-}
{-@ measure tsize @-}
{-@ tsize :: t:Type -> { v:Int | v >= 0 } @-} 
tsize :: Type -> Int
tsize (TRefn b   r)         = (predsize r) + 1
tsize (TFunc   t_x t)       = (tsize t_x) + (tsize t) + 1
tsize (TExists   t_x t)     = (tsize t_x) + (tsize t) + 1
tsize (TPoly   k   t)       = (tsize t)   + 1

{-@ measure tdepth @-}  
{-@ tdepth :: t:Type -> { v:Int | v >= 1 } @-} 
tdepth :: Type -> Int
tdepth (TRefn b   r)         = 1
tdepth (TFunc   t_x t)       = (max (tdepth t_x) (tdepth t)) + 1
tdepth (TExists   t_x t)     = (max (tdepth t_x) (tdepth t)) + 1 -- 2
tdepth (TPoly   k   t)       = (tdepth t)   + 1

{-@ measure isTRefn @-}
isTRefn :: Type -> Bool
isTRefn (TRefn {}) = True
isTRefn _          = False

{-@ measure isTFunc @-}
isTFunc :: Type -> Bool
isTFunc (TFunc {}) = True
isTFunc _          = False

{-@ measure isTExists @-}
isTExists :: Type -> Bool
isTExists (TExists {}) = True
isTExists _            = False

{-@ measure isTPoly @-}
isTPoly :: Type -> Bool
isTPoly (TPoly {}) = True
isTPoly _          = False

{-@ measure free @-} -- free TERM variables
{-@ free :: t:Type -> S.Set Vname / [tsize t] @-}
free :: Type -> S.Set Vname
free (TRefn b   rs)     = fvP rs
free (TFunc   t_x t)    = S.union (free t_x) (free t) 
free (TExists   t_x t)  = S.union (free t_x) (free t) 
free (TPoly   k   t)    = free t

{-@ measure freeList @-}
{-@ freeList :: t:Type -> { xs:Names | listElts xs == free t } / [tsize t] @-}
freeList :: Type -> Names
freeList (TRefn b   rs)     = fvPList rs
freeList (TFunc   t_x t)    = union (freeList t_x) (freeList t) 
freeList (TExists   t_x t)  = union (freeList t_x) (freeList t) 
freeList (TPoly   k   t)    = freeList t

{-@ measure freeTV @-} -- free TYPE variables
{-@ freeTV :: t:Type -> S.Set Vname / [tsize t] @-}
freeTV :: Type -> S.Set Vname
freeTV (TRefn b   r)      = case b of 
  (FTV a)      -> S.union (S.singleton a) (ftvP r)
  _            -> ftvP r
freeTV (TFunc   t_x t)    = S.union (freeTV t_x) (freeTV t) 
freeTV (TExists   t_x t)  = S.union (freeTV t_x) (freeTV t) 
freeTV (TPoly   k   t)    = freeTV t

{-@ reflect isLCT @-}
isLCT :: Type -> Bool
isLCT t = isLCT_at 0 0 t

{-@ reflect isLCT_at @-}
{-@ isLCT_at :: Index -> Index -> t:Type -> Bool / [tsize t] @-}
isLCT_at :: Index -> Index -> Type -> Bool
isLCT_at j_x j_a (TRefn   b  rs) = case b of
  (BTV i) -> i < j_a && isLCP_at (j_x+1) j_a rs
  _       ->            isLCP_at (j_x+1) j_a rs
isLCT_at j_x j_a (TFunc   t_x t) = isLCT_at j_x j_a t_x && isLCT_at (j_x+1) j_a t
isLCT_at j_x j_a (TExists t_x t) = isLCT_at j_x j_a t_x && isLCT_at (j_x+1) j_a t
isLCT_at j_x j_a (TPoly   k   t) =                         isLCT_at j_x (j_a+1) t

{-@ reflect unbindT @-}         
{-@ unbindT :: y:Vname -> t:Type 
                       -> { t':Type | Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                      Set_sub (freeTV t') (freeTV t) &&
                                      Set_sub (free t) (free t') && Set_sub (freeTV t) (freeTV t') &&
                                      (noExists t => noExists t') && tsize t == tsize t' &&
                                      tdepth t == tdepth t' && 
                                      erase t == erase t' } / [tsize t] @-} 
unbindT :: Vname -> Type -> Type
unbindT y t = openT_at 0 y t

{-@ reflect openT_at @-}         
{-@ openT_at :: j:Index -> y:Vname -> t:Type 
                        -> { t':Type | Set_sub (free t') (Set_cup (Set_sng y) (free t)) &&
                                       Set_sub (free t) (free t') &&
                                       Set_sub (freeTV t') (freeTV t) && Set_sub (freeTV t) (freeTV t') &&
                                       (noExists t => noExists t') && tsize t == tsize t' &&
                                       tdepth t == tdepth t' && 
                                       erase t == erase t' } / [tsize t] @-} 
openT_at :: Index -> Vname -> Type -> Type
openT_at j y (TRefn b ps)    = TRefn b (openP_at (j+1) y ps)
openT_at j y (TFunc   t_z t) = TFunc   (openT_at j y t_z) (openT_at (j+1) y t)
openT_at j y (TExists t_z t) = TExists (openT_at j y t_z) (openT_at (j+1) y t)
openT_at j y (TPoly   k   t) = TPoly k (openT_at j y t)   -- not j+1

{-@ reflect unbind_tvT @-} 
{-@ unbind_tvT :: a':Vname -> t:Type 
                       -> { t':Type | Set_sub (freeTV t') (Set_cup (Set_sng a') (freeTV t)) &&
                                      Set_sub (free t') (free t) &&
                                      Set_sub (freeTV t) (freeTV t') && Set_sub (free t) (free t') &&
                                      tdepth t == tdepth t' && 
                                      (noExists t => noExists t') && tsize t == tsize t' } / [tsize t] @-} 
unbind_tvT :: Vname -> Type -> Type
unbind_tvT a' t = open_tvT_at 0 a' t

{-@ reflect open_tvT_at @-} 
{-@ open_tvT_at :: j:Index -> a':Vname -> t:Type 
                       -> { t':Type | Set_sub (freeTV t') (Set_cup (Set_sng a') (freeTV t)) &&
                                      Set_sub (free t') (free t) &&
                                      Set_sub (freeTV t) (freeTV t') && Set_sub (free t) (free t') &&
                                      tdepth t == tdepth t' && 
                                      (noExists t => noExists t') && tsize t == tsize t' } / [tsize t] @-} 
open_tvT_at :: Index -> Vname -> Type -> Type
open_tvT_at j a' (TRefn b  ps)     = case b of 
  (BTV i) | i == j  -> TRefn (FTV a') (open_tvP_at j a' ps) -- not j+1
  _                 -> TRefn b        (open_tvP_at j a' ps) -- not j+1
open_tvT_at j a' (TFunc   t_z t)   = TFunc    (open_tvT_at j a' t_z) (open_tvT_at j a' t) -- not j+1
open_tvT_at j a' (TExists t_z t)   = TExists  (open_tvT_at j a' t_z) (open_tvT_at j a' t) -- not j+1
open_tvT_at j a' (TPoly   k  t)    = TPoly k  (open_tvT_at (j+1) a' t)


--  |  SUBSTITUTION IN TYPES
-- When substituting in for a type variable, say a{x:p}[t_a/a], where t_a is not a refined
--     basic type, then we need to express "t_a {x:p}" by pushing the refinement down into t_a.
--     For example a{x:p}[ ( \exists y:Int{y:q}. a'{z:r} )/a] becomes roughly speaking
--             \exists Int{y:q}. a'{z:r `And` p}

{-@ reflect push @-}
{-@ push ::  p:Preds -> t:UserType 
                -> { t':UserType | Set_sub (free t') (Set_cup (free t) (fvP p)) && 
                                   Set_sub (freeTV t') (Set_cup (freeTV t) (ftvP p)) && 
                                 ( p != PEmpty || t == t' ) && tdepth t == tdepth t' && 
                                 ( erase t' == erase t ) } @-}  
push :: Preds -> Type -> Type
push p (TRefn   b     r) = TRefn   b     (strengthen p r)
push p (TFunc     t_y t) = TFunc     t_y t 
--push p (TExists   t_y t) = TExists   t_y (push p t) <-- we would need ShiftAbove p to define this
push p (TPoly     k   t) = TPoly     k   t 

-- Also note that non-trivially-refined Star types are unsound, so we cannot have t_a with Star
--     kind unless p == True, in which case there's nothing to push down. So this only really
--     affects the existential types.

{-@ reflect tsubFV @-}
{-@ tsubFV :: x:Vname -> e:Value -> t:Type  
         -> { t':Type | ( Set_mem x (free t) || t == t' ) && 
                ( Set_sub (free t') (Set_cup (fv e) (Set_dif (free t) (Set_sng x))) ) &&
                  Set_sub (freeTV t') (Set_cup (ftv e) (freeTV t)) &&
                ( (not (Set_mem x (fv e))) => not (Set_mem x (free t')) ) &&
                  tdepth t == tdepth t' && 
                ( noExists t => noExists t' ) } / [tsize t] @-}
tsubFV :: Vname -> Expr -> Type -> Type
tsubFV x v_x (TRefn  b r)     = TRefn b   (psubFV x v_x r)
tsubFV x v_x (TFunc  t_z t)   = TFunc    (tsubFV x v_x t_z) (tsubFV x v_x t)
tsubFV x v_x (TExists  t_z t) = TExists  (tsubFV x v_x t_z) (tsubFV x v_x t)
tsubFV x v_x (TPoly  k   t)   = TPoly    k                  (tsubFV x v_x t)

{-@ reflect tsubFTV @-}
{-@ tsubFTV :: a:Vname -> t_a:UserType -> t:Type 
         -> { t':Type | ( Set_mem a (freeTV t) || t == t' )  &&
                ( Set_sub (freeTV t') (Set_cup (freeTV t_a) (Set_dif (freeTV t) (Set_sng a))) ) &&
                  Set_sub (free t') (Set_cup (free t_a) (free t)) && 
                ( (not (Set_mem a (freeTV t_a))) => not (Set_mem a (freeTV t')) ) &&
                  tdepth t' <= tdepth t_a + tdepth t &&  tdepth t' >= tdepth t &&
                ( noExists t => noExists t' ) } / [tsize t] @-} 
tsubFTV :: Vname -> Type -> Type -> Type
tsubFTV a t_a (TRefn b   r)        = case b of
  (FTV a') | a == a' -> push      (psubFTV a t_a r) t_a
  _                  -> TRefn b   (psubFTV a t_a r)
tsubFTV a t_a (TFunc     t_z t)    = TFunc      (tsubFTV a t_a t_z) (tsubFTV a t_a t)
tsubFTV a t_a (TExists   t_z t)    = TExists    (tsubFTV a t_a t_z) (tsubFTV a t_a t)
tsubFTV a t_a (TPoly      k  t)    = TPoly      k                   (tsubFTV a t_a t)

{-@ reflect tsubBV @-}  
{-@ tsubBV :: v_x:Value -> t:Type  
                -> { t':Type | Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                               Set_sub (freeTV t') (Set_cup (ftv v_x) (freeTV t)) &&
                               erase t == erase t' && tdepth t == tdepth t' &&
                               ( esize v_x != 1 || tsize t == tsize t' ) } / [tsize t] @-}
tsubBV :: Expr -> Type -> Type
tsubBV v_x t = tsubBV_at 0 v_x t

{-@ reflect tsubBV_at @-}  
{-@ tsubBV_at :: j:Index -> v_x:Value -> t:Type  
                -> { t':Type | Set_sub (free t') (Set_cup (fv v_x) (free t)) &&
                               Set_sub (freeTV t') (Set_cup (ftv v_x) (freeTV t)) &&
                               erase t == erase t' && tdepth t == tdepth t' &&
                               ( esize v_x != 1 || tsize t == tsize t' ) } / [tsize t] @-}
tsubBV_at :: Index -> Expr -> Type -> Type
tsubBV_at j v_x (TRefn b ps)    = TRefn b (psubBV_at (j+1) v_x ps)  
tsubBV_at j v_x (TFunc   t_z t) = TFunc   (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
tsubBV_at j v_x (TExists t_z t) = TExists (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
tsubBV_at j v_x (TPoly   k  t)  = TPoly k (tsubBV_at j v_x t)   -- not j+1

{-@ reflect tsubBTV @-}  --  ( isTrivial t_a => tsize t == tsize t' )
{-@ tsubBTV :: t_a:UserType -> t:Type
                -> { t':Type | Set_sub (free t') (Set_cup (free t_a) (free t)) &&
                               tdepth t' <= tdepth t_a + tdepth t && tdepth t' >= tdepth t &&
                               Set_sub (freeTV t') (Set_cup (freeTV t_a) (freeTV t)) } / [tsize t] @-}
tsubBTV :: Type -> Type -> Type
tsubBTV t_a t = tsubBTV_at 0 t_a t

{-@ reflect tsubBTV_at @-}  --  ( isTrivial t_a => tsize t == tsize t' )
{-@ tsubBTV_at :: j:Index -> t_a:UserType -> t:Type
                -> { t':Type | Set_sub (free t') (Set_cup (free t_a) (free t)) &&
                               tdepth t' <= tdepth t_a + tdepth t && tdepth t' >= tdepth t &&
                               Set_sub (freeTV t') (Set_cup (freeTV t_a) (freeTV t)) } / [tsize t] @-}
tsubBTV_at :: Index -> Type -> Type -> Type
tsubBTV_at j t_a (TRefn b   ps)        = case b of 
  (BTV i) | i == j  -> push    (psubBTV_at j t_a ps) t_a -- TExists y t_y (push x r[t_a/a] t')  not j+1
  _                 -> TRefn b (psubBTV_at j t_a ps)     -- looking for BTV, not BV             not j+1
tsubBTV_at j t_a (TFunc   t_z t)    = TFunc    (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  --  not j+1
tsubBTV_at j t_a (TExists t_z t)    = TExists  (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  --  not j+1
tsubBTV_at j t_a (TPoly   k  t)     = TPoly k  (tsubBTV_at (j+1) t_a t)


---------------------------------------------------------------------------
----- | SYNTAX, continued
---------------------------------------------------------------------------

  --- TYPING ENVIRONMENTS ---

data Env = Empty                         -- type Env = [(Vname, Type) or Vname]
         | Cons  Vname Type Env          
         | ConsT Vname Kind Env
--  deriving (Show)
{-@ data Env where 
        Empty :: Env 
        Cons  :: x:Vname -> t:Type -> { g:Env | not (in_env x g) } 
                         -> { g':Env | binds g'   == Set_cup (Set_sng x)  (binds g) &&
                                       vbinds g'  == Set_cup (Set_sng x) (vbinds g) &&
                                       tvbinds g' == tvbinds g &&
                                       Set_cup (vbinds g') (tvbinds g') == binds g' &&
                                       Set_emp (Set_cap (vbinds g') (tvbinds g')) } 
        ConsT :: a:Vname -> k:Kind -> { g:Env | not (in_env a g) } 
                         -> { g':Env | binds g'   == Set_cup (Set_sng a)   (binds g) &&
                                       vbinds g'  == vbinds g &&
                                       tvbinds g' == Set_cup (Set_sng a) (tvbinds g) &&
                                       Set_cup (vbinds g') (tvbinds g') == binds g' &&
                                       Set_emp (Set_cap (vbinds g') (tvbinds g')) }  @-}

{-@ measure envsize @-}
{-@ envsize :: Env -> { n:Int | n >= 0 } @-}
envsize :: Env -> Int
envsize Empty         = 0
envsize (Cons  _ _ g) = envsize g + 1
envsize (ConsT _ _ g) = envsize g + 1

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = {-pleUnfold (-}if x >= y then x else y

{-@ reflect in_env @-}              -- any kind of variable
in_env :: Vname -> Env -> Bool
in_env x g = S.member x (binds g) 

{-@ reflect bound_in @-}            -- term variables only
bound_in :: Vname -> Type -> Env -> Bool
bound_in x t Empty                                 = False
bound_in x t (Cons y t' g) | (x == y)              = (t == t')
                           | otherwise             = bound_in x t g
bound_in x t (ConsT a k g) | (x == a)              = False
                           | otherwise             = bound_in x t g

{-@ reflect tv_bound_in @-}         -- type variables only
tv_bound_in :: Vname -> Kind -> Env -> Bool
tv_bound_in a k Empty                                   = False
tv_bound_in a k (Cons x t g)    | (a == x)              = False
                                | otherwise             = tv_bound_in a k g
tv_bound_in a k (ConsT a' k' g) | (a == a')             = (k == k')
                                | otherwise             = tv_bound_in a k g

{-@ reflect kind_for_tv @-}
{-@ kind_for_tv :: a:Vname -> { g:Env | Set_mem a (tvbinds g) } 
                           -> { k:Kind | tv_bound_in a k g } @-}
kind_for_tv :: Vname -> Env -> Kind
kind_for_tv a (Cons  x  t  g)             = kind_for_tv a g
kind_for_tv a (ConsT a' k' g) | (a == a') = k'
                              | otherwise = kind_for_tv a g

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty         = S.empty
binds (Cons x t g)  = S.union (S.singleton x) (binds g)
binds (ConsT a k g) = S.union (S.singleton a) (binds g)

{-@ reflect v_in_env @-}              -- (term) variables
v_in_env :: Vname -> Env -> Bool
v_in_env x g = S.member x (vbinds g) 

{-@ reflect vbinds @-}
{-@ vbinds :: g:Env -> { s:S.Set Vname | Set_sub s (binds g) } @-}
vbinds :: Env -> S.Set Vname
vbinds Empty         = S.empty
vbinds (Cons x t g)  = S.union (S.singleton x) (vbinds g)
vbinds (ConsT a k g) = vbinds g

{-@ reflect tv_in_env @-}              -- type variables
tv_in_env :: Vname -> Env -> Bool
tv_in_env x g = S.member x (tvbinds g) 

{-@ reflect tvbinds @-}
{-@ tvbinds :: g:Env -> { s:S.Set Vname | Set_sub s (binds g) } @-}
tvbinds :: Env -> S.Set Vname
tvbinds Empty         = S.empty
tvbinds (Cons x t g)  = tvbinds g
tvbinds (ConsT a k g) = S.union (S.singleton a) (tvbinds g)

{-@ lem_binds_invariants :: g:Env -> { pf:_ | Set_cup (vbinds g) (tvbinds g) == binds g &&
                                              Set_emp (Set_cap (vbinds g) (tvbinds g)) } @-}
lem_binds_invariants :: Env -> Proof
lem_binds_invariants Empty           = ()
lem_binds_invariants (Cons x t_x g)  = () ? lem_binds_invariants g
lem_binds_invariants (ConsT a k_a g) = () ? lem_binds_invariants g


  --- BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
  --    but all the refinements, dependent arrow binders, and existentials have been erased.

data FType = FTBasic Basic          -- b: Bool, Int, FTV a, BTV a
           | FTFunc FType FType     -- bt -> bt'
           | FTPoly Kind  FType     -- \forall a:k. bt 
  deriving (Eq, Show)

{-@ measure ftsize @-}
{-@ ftsize :: t:FType -> { v:Int | v >= 0 } @-} 
ftsize :: FType -> Int
ftsize (FTBasic b)      = 1
ftsize (FTFunc t_x   t) = (ftsize t_x) + (ftsize t) + 1
ftsize (FTPoly    k  t) = (ftsize t)   + 1

{-@ measure isBaseF @-}
isBaseF :: FType -> Bool
isBaseF (FTBasic b)     = True
isBaseF _               = False

{-@ reflect erase @-}
erase :: Type -> FType
erase (TRefn b r)     = FTBasic b
erase (TFunc t_x t)   = FTFunc (erase t_x) (erase t)
erase (TExists t_x t) = (erase t)
erase (TPoly  k  t)   = FTPoly k (erase t)

-- there are no term vars in a Bare Type, only type ones
{-@ measure ffreeTV @-} 
{-@ ffreeTV :: t:FType -> S.Set Vname / [ftsize t] @-}
ffreeTV :: FType -> S.Set Vname
ffreeTV (FTBasic b)      = case b of
  (FTV a)                    -> S.singleton a
  _                          -> S.empty
ffreeTV (FTFunc t_x t)   = S.union (ffreeTV t_x) (ffreeTV t) 
ffreeTV (FTPoly   k t)   = ffreeTV t

{-@ measure ffreeTVList @-}
{-@ ffreeTVList :: t:FType -> { xs:Names | listElts xs == ffreeTV t } @-}
ffreeTVList :: FType -> Names
ffreeTVList (FTBasic b)     = case b of
  (FTV a)                       -> [a]
  _                             -> []
ffreeTVList (FTFunc t_x t)  = union (ffreeTVList t_x)  (ffreeTVList t)
ffreeTVList (FTPoly   k t)  = ffreeTVList t

{-@ reflect isLCFT @-}
isLCFT :: FType -> Bool
isLCFT t = isLCFT_at 0 t

{-@ reflect isLCFT_at @-} 
isLCFT_at :: Index -> FType -> Bool
isLCFT_at j (FTBasic b)      = case b of
  (BTV i)                    -> i < j
  _                          -> True
isLCFT_at j (FTFunc t_x t)   = isLCFT_at j t_x && isLCFT_at j t
isLCFT_at j (FTPoly   k t)   = isLCFT_at (j+1) t

{-@ reflect unbindFT @-}
{-@ unbindFT :: a':Vname -> t:FType 
                       -> { t':FType | Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       Set_sub (ffreeTV t) (ffreeTV t') &&
                                       ftsize t == ftsize t' } / [ftsize t] @-} 
unbindFT :: Vname -> FType -> FType
unbindFT a' t = openFT_at 0 a' t

{-@ reflect openFT_at @-}
{-@ openFT_at :: j:Index -> a':Vname -> t:FType
                       -> { t':FType | Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       Set_sub (ffreeTV t) (ffreeTV t') &&
                                       ftsize t == ftsize t' } / [ftsize t] @-} 
openFT_at :: Index -> Vname -> FType -> FType
openFT_at j a' (FTBasic b)    = case b of
  (BTV i) | i == j  -> FTBasic (FTV a')
  _                 -> FTBasic b
openFT_at j a' (FTFunc t_x t) = FTFunc (openFT_at j a' t_x) (openFT_at j a' t)
openFT_at j a' (FTPoly k   t) = FTPoly k (openFT_at (j+1) a' t)

-- System F substituion is simpler because there are no refinements to worry about, so we can just
--   do a single substitution instead of both a variable replacement t[a'/a] and a refinment-streng.
--   substitution t[a:=t_a]
{-@ reflect ftsubFV @-}
{-@ ftsubFV :: a:Vname -> t_a:FType -> t:FType  
         -> { t':FType | ( Set_mem a (ffreeTV t) || t == t' ) && 
                ( Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (Set_dif (ffreeTV t) (Set_sng a))) ) &&
                ( (not (Set_mem a (ffreeTV t_a))) => not (Set_mem a (ffreeTV t')) ) } / [ftsize t] @-}
ftsubFV :: Vname -> FType -> FType -> FType
ftsubFV a t_a (FTBasic b)           = case b of 
  (FTV a') | a == a'                    -> t_a
  _                                     -> FTBasic b
ftsubFV a t_a (FTFunc t_z t)        = FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
ftsubFV a t_a (FTPoly   k t)        = FTPoly k (ftsubFV a t_a t)

{-@ reflect ftsubBV @-} 
{-@ ftsubBV :: t_a:FType -> t:FType  
        -> { t':FType | Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) &&
                        ( ftsize t_a != 1 || ftsize t == ftsize t' ) } / [ftsize t] @-}
ftsubBV :: FType -> FType -> FType
ftsubBV t_a t = ftsubBV_at 0 t_a t

{-@ reflect ftsubBV_at @-} 
{-@ ftsubBV_at :: Index -> t_a:FType -> t:FType  
        -> { t':FType | Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) &&
                        ( ftsize t_a != 1 || ftsize t == ftsize t' ) } / [ftsize t] @-}
ftsubBV_at :: Index -> FType -> FType -> FType
ftsubBV_at j t_a (FTBasic   b)      = case b of 
  (BTV i) | i == j                    -> t_a
  _                                   -> FTBasic b
ftsubBV_at j t_a (FTFunc t_z t)     = FTFunc (ftsubBV_at j t_a t_z) (ftsubBV_at j t_a t)
ftsubBV_at j t_a (FTPoly  k  t)     = FTPoly k (ftsubBV_at (j+1) t_a t)
 

  --- BARE-TYPING ENVIRONMENTS

data FEnv = FEmpty                       -- type FEnv = [(Vname, FType) or Vname]
          | FCons  Vname FType FEnv
          | FConsT Vname Kind  FEnv
--  deriving (Show) 
{-@ data FEnv where
        FEmpty :: FEnv
        FCons  :: x:Vname -> t:FType -> { g:FEnv | not (in_envF x g) } 
                          -> { g':FEnv | bindsF g'   == Set_cup (Set_sng x)  (bindsF g) &&
                                         vbindsF g'  == Set_cup (Set_sng x) (vbindsF g) &&
                                         tvbindsF g' == tvbindsF g &&
                                         Set_cup (vbindsF g') (tvbindsF g') == bindsF g' &&
                                         Set_emp (Set_cap (vbindsF g') (tvbindsF g')) }
        FConsT :: a:Vname -> k:Kind  -> { g:FEnv | not (in_envF a g) } 
                          -> { g':FEnv | bindsF g'   == Set_cup (Set_sng a)   (bindsF g) &&
                                         vbindsF g'  == vbindsF g &&
                                         tvbindsF g' == Set_cup (Set_sng a) (tvbindsF g) &&
                                         Set_cup (vbindsF g') (tvbindsF g') == bindsF g' &&
                                         Set_emp (Set_cap (vbindsF g') (tvbindsF g')) } @-}

{-@ measure fenvsize @-}
{-@ fenvsize :: FEnv -> { n:Int | n >= 0 } @-}
fenvsize :: FEnv -> Int
fenvsize FEmpty         = 0
fenvsize (FCons  _ _ g) = fenvsize g + 1
fenvsize (FConsT _ _ g) = fenvsize g + 1

{-@ reflect in_envF @-}
in_envF :: Vname -> FEnv -> Bool
in_envF x g = S.member x (bindsF g) 

{-@ reflect lookupF @-}
{- @ lookupF :: x:Vname -> g:FEnv -> { mt:Maybe FType | (mt == Just t) => bound_inF x t g } @-}
lookupF :: Vname -> FEnv -> Maybe FType
lookupF x FEmpty                      = Nothing
lookupF x (FCons  y t g) | x == y     = Just t
                         | otherwise  = lookupF x g
lookupF x (FConsT a k g) | x == a     = Nothing
                         | otherwise  = lookupF x g

{-@ reflect bound_inF @-}
{- @ bound_inF :: x:Vname -> t:FType -> g:FEnv 
        -> { b:Bool | (not b || in_envF x g) && (lookupF x g == Just t => bound_inF x t g)} @-}
bound_inF :: Vname -> FType -> FEnv -> Bool
bound_inF x t FEmpty                                  = False
bound_inF x t (FCons  y t' g) | (x == y)              = (t == t')
                              | otherwise             = bound_inF x t g
bound_inF x t (FConsT a k  g) | (x == a)              = False
                              | otherwise             = bound_inF x t g

{-@ reflect tv_bound_inF @-}         -- type variables only
tv_bound_inF :: Vname -> Kind -> FEnv -> Bool
tv_bound_inF a k FEmpty                                   = False
tv_bound_inF a k (FCons x t g)    | (a == x)              = False
                                  | otherwise             = tv_bound_inF a k g
tv_bound_inF a k (FConsT a' k' g) | (a == a')             = (k == k')
                                  | otherwise             = tv_bound_inF a k g

{-@ reflect kind_for_tvF @-}
{-@ kind_for_tvF :: a:Vname -> { g:FEnv | Set_mem a (tvbindsF g) } 
                            -> { k:Kind | tv_bound_inF a k g } @-}
kind_for_tvF :: Vname -> FEnv -> Kind
kind_for_tvF a (FCons  x  t  g)             = kind_for_tvF a g
kind_for_tvF a (FConsT a' k' g) | (a == a') = k'
                                | otherwise = kind_for_tvF a g

{-@ lem_lookup_boundinF :: x:Vname -> t:FType -> { g:FEnv | lookupF x g == Just t }
        -> { pf:_ | bound_inF x t g } @-}
lem_lookup_boundinF :: Vname -> FType -> FEnv -> Proof
lem_lookup_boundinF x t (FCons  y s g) | x == y    = ()
                                       | otherwise = lem_lookup_boundinF x t g
lem_lookup_boundinF x t (FConsT a k g) | x == a    = impossible ""
                                       | otherwise = lem_lookup_boundinF x t g

{-@ lem_boundin_inenvF :: x:Vname -> t:FType -> { g:FEnv | bound_inF x t g}
        -> { pf:_ | in_envF x g } @-}
lem_boundin_inenvF :: Vname -> FType -> FEnv -> Proof
lem_boundin_inenvF x t (FCons y s g)  | x == y    = ()
                                      | otherwise = lem_boundin_inenvF x t g 
lem_boundin_inenvF x t (FConsT a k g) | x == a    = impossible ""
                                      | otherwise = lem_boundin_inenvF x t g 

{-@ lem_tvboundin_inenvF :: a:Vname -> k:Kind -> { g:FEnv | tv_bound_inF a k g}
        -> { pf:_ | in_envF a g } @-}
lem_tvboundin_inenvF :: Vname -> Kind -> FEnv -> Proof
lem_tvboundin_inenvF a k (FCons y s g)    | a == y    = impossible ""
                                          | otherwise = lem_tvboundin_inenvF a k g 
lem_tvboundin_inenvF a k (FConsT a' k' g) | a == a'   = ()
                                          | otherwise = lem_tvboundin_inenvF a k g 

{-@ reflect bindsF @-}
bindsF :: FEnv -> S.Set Vname
bindsF FEmpty         = S.empty
bindsF (FCons  x t g) = S.union (S.singleton x) (bindsF g)
bindsF (FConsT a k g) = S.union (S.singleton a) (bindsF g)

{-@ reflect vbindsF @-}
{-@ vbindsF :: g:FEnv -> { s:S.Set Vname | Set_sub s (bindsF g) } @-}
vbindsF :: FEnv -> S.Set Vname
vbindsF FEmpty         = S.empty
vbindsF (FCons x t g)  = S.union (S.singleton x) (vbindsF g)
vbindsF (FConsT a k g) = vbindsF g

{-@ reflect tvbindsF @-}
{-@ tvbindsF :: g:FEnv -> { s:S.Set Vname | Set_sub s (bindsF g) } @-}
tvbindsF :: FEnv -> S.Set Vname
tvbindsF FEmpty         = S.empty
tvbindsF (FCons x t g)  = tvbindsF g
tvbindsF (FConsT a k g) = S.union (S.singleton a) (tvbindsF g)

{-@ reflect erase_env @-}
{-@ erase_env :: g:Env -> { g':FEnv | binds g == bindsF g' && vbinds g == vbindsF g' 
                                                           && tvbinds g == tvbindsF g'} @-}
erase_env :: Env -> FEnv
erase_env Empty         = FEmpty
erase_env (Cons  x t g) = FCons  x (erase t) (erase_env g)
erase_env (ConsT a k g) = FConsT a k         (erase_env g)

{-@ lem_erase_freeTV :: t:Type -> { pf:_ | Set_sub (ffreeTV (erase t)) (freeTV t) } @-}
lem_erase_freeTV :: Type -> Proof
lem_erase_freeTV (TRefn   b   p) = ()
lem_erase_freeTV (TFunc   t_z t) = () ? lem_erase_freeTV t_z
                                      ? lem_erase_freeTV t
lem_erase_freeTV (TExists t_z t) = () ? lem_erase_freeTV t
lem_erase_freeTV (TPoly    k' t) = () ? lem_erase_freeTV t


---------------------------------------------------------------------------
----- | NAME SETS and FRESH NAMES
---------------------------------------------------------------------------

type Names = [Vname]   -- for cofinite quantification over free names

{-@ predicate IsCup     X Y Z  = listElts X = Set_cup (listElts Y) (listElts Z) @-}
{-@ predicate IsCupEnv  X Y Z  = listElts X = Set_cup (listElts Y) (binds Z)    @-}
{-@ predicate IsCupFEnv X Y Z  = listElts X = Set_cup (listElts Y) (bindsF Z)   @-}
{-@ predicate Elem  X Ys   = Set_mem X (listElts Ys)                            @-}
{-@ predicate NotElem X Ys = not (Elem X Ys)                                    @-}

{-@ reflect union @-}
{-@ union :: ys:Names -> zs:Names -> { xs:Names | IsCup xs ys zs } @-}
union :: Names -> Names -> Names
union xs []         = xs
union xs (y:ys)     = y : (union xs ys)

{-@ unionEnv :: ys:Names -> zs:Env -> { xs:Names | IsCupEnv xs ys zs } @-}
unionEnv :: Names -> Env -> Names
unionEnv xs Empty         = xs
unionEnv xs (Cons  x t g) = x : (unionEnv xs g)
unionEnv xs (ConsT a k g) = a : (unionEnv xs g)

{-@ unionFEnv :: ys:Names -> zs:FEnv -> { xs:Names | IsCupFEnv xs ys zs } @-}
unionFEnv :: Names -> FEnv -> Names
unionFEnv xs FEmpty         = xs
unionFEnv xs (FCons  x t g) = x : (unionFEnv xs g)
unionFEnv xs (FConsT a k g) = a : (unionFEnv xs g)

{-@ fresh :: xs:Names -> { v:Vname | NotElem v xs } @-}
fresh :: Names -> Vname
fresh bs = n `withProof` lem_above_max_fresh n bs
  where
    n    = 1 + maxs bs

{-@ reflect maxs @-}
{-@ maxs :: xs:_ -> {v:_ | v = maxs xs && v >= 0} @-}
maxs :: Names -> Vname
maxs ([])   = 0
maxs (x:xs) = if (x > maxs xs) then x else (maxs xs)

{-@ lem_above_max_fresh :: x:Vname -> xs:{Names | x > maxs xs} -> { pf:_ | NotElem x xs} @-}
lem_above_max_fresh :: Vname -> Names -> Proof
lem_above_max_fresh _ []     = ()
lem_above_max_fresh x (_:ys) = lem_above_max_fresh x ys

{-@ fresh_var :: xs:Names -> g:Env -> { x:Vname | not (in_env x g) && NotElem x xs } @-}
fresh_var :: Names -> Env -> Vname
fresh_var xs g = n `withProof` lem_above_max_nms_env n xs g
  where
    n    = 1 + max_nms_env xs g

{-@ fresh_var_excluding :: xs:Names -> g:Env -> x:Vname 
                -> { y:Vname | not (in_env y g) && y != x && NotElem y xs } @-}
fresh_var_excluding :: Names -> Env -> Vname -> Vname
fresh_var_excluding xs g x = if in_env x g then fresh_var xs g
                                 else fresh_var xs (Cons x (TRefn TBool PEmpty) g)

{-@ reflect max_nms_env @-}
{-@ max_nms_env :: Names -> Env -> { x:Vname | x >= 0 } @-}
max_nms_env :: Names -> Env -> Vname 
max_nms_env ([])   Empty         = 0
max_nms_env ([])   (Cons  x t g) = if (x > max_nms_env [] g) then x else (max_nms_env [] g)
max_nms_env ([])   (ConsT a k g) = if (a > max_nms_env [] g) then a else (max_nms_env [] g)
max_nms_env (x:xs) g             = if (x > max_nms_env xs g) then x else (max_nms_env xs g)

{-@ lem_above_max_nms_env :: x:Vname -> xs:Names -> { g:Env | x > max_nms_env xs g } 
                                      -> { pf:_ | NotElem x xs && not (in_env x g) } @-}
lem_above_max_nms_env :: Vname -> Names -> Env -> Proof
lem_above_max_nms_env _ []     Empty         = ()
lem_above_max_nms_env x []     (Cons  y t g) = lem_above_max_nms_env x [] g
lem_above_max_nms_env x []     (ConsT a k g) = lem_above_max_nms_env x [] g
lem_above_max_nms_env x (_:ys) g             = lem_above_max_nms_env x ys g


{-@ fresh_varF :: xs:Names -> g:FEnv -> { x:Vname | not (in_envF x g) && NotElem x xs } @-}
fresh_varF :: Names -> FEnv -> Vname
fresh_varF xs g = n `withProof` lem_above_max_nms_fenv n xs g
  where
    n    = 1 + max_nms_fenv xs g

{-@ fresh_var_excludingF :: xs:Names -> g:FEnv -> x:Vname 
                -> { y:Vname | not (in_envF y g) && y != x && NotElem y xs } @-}
fresh_var_excludingF :: Names -> FEnv -> Vname -> Vname
fresh_var_excludingF xs g x = if in_envF x g then fresh_varF xs g
                                 else fresh_varF xs (FCons x (FTBasic TBool) g)

{-@ reflect max_nms_fenv @-}
{-@ max_nms_fenv :: Names -> FEnv -> { x:Vname | x >= 0 } @-}
max_nms_fenv :: Names -> FEnv -> Vname 
max_nms_fenv ([])   FEmpty         = 0
max_nms_fenv ([])   (FCons  x t g) = if (x > max_nms_fenv [] g) then x else (max_nms_fenv [] g)
max_nms_fenv ([])   (FConsT a k g) = if (a > max_nms_fenv [] g) then a else (max_nms_fenv [] g)
max_nms_fenv (x:xs) g              = if (x > max_nms_fenv xs g) then x else (max_nms_fenv xs g)

{-@ lem_above_max_nms_fenv :: x:Vname -> xs:Names -> { g:FEnv | x > max_nms_fenv xs g } 
                                      -> { pf:_ | NotElem x xs && not (in_envF x g) } @-}
lem_above_max_nms_fenv :: Vname -> Names -> FEnv -> Proof
lem_above_max_nms_fenv _ []     FEmpty         = ()
lem_above_max_nms_fenv x []     (FCons  y t g) = lem_above_max_nms_fenv x [] g
lem_above_max_nms_fenv x []     (FConsT a k g) = lem_above_max_nms_fenv x [] g
lem_above_max_nms_fenv x (_:ys) g              = lem_above_max_nms_fenv x ys g


{-@ fresh_varT :: xs:Names -> g:Env -> t:Type 
        -> { x:Vname | not (Set_mem x (free t)) && not (in_env x g) && NotElem x xs } @-}
fresh_varT :: Names -> Env -> Type -> Vname
fresh_varT xs g t
  = n `withProof` lem_above_max_nms_type n xs (freeList t) g
      where
        n    = 1 + max_nms_type xs (freeList t) g

{-@ reflect max_nms_type @-}
{-@ max_nms_type :: Names -> Names -> Env -> { x:Vname | x >= 0 } @-}
max_nms_type :: Names -> Names -> Env -> Vname 
max_nms_type ([])   ([])   Empty         = 0
max_nms_type ([])   ([])   (Cons  x t g) 
  = if (x > max_nms_type [] [] g) then x else (max_nms_type [] [] g)
max_nms_type ([])   ([])   (ConsT a k g)
  = if (a > max_nms_type [] [] g) then a else (max_nms_type [] [] g)
max_nms_type ([])   (y:ys) g 
  = if (y > max_nms_type [] ys g) then y else (max_nms_type [] ys g)
max_nms_type (x:xs) ys     g 
  = if (x > max_nms_type xs ys g) then x else (max_nms_type xs ys g)

{-@ lem_above_max_nms_type :: x:Vname -> xs:Names -> ys:Names
        -> { g:Env | x > max_nms_type xs ys g } 
        -> { pf:_ | NotElem x xs && NotElem x ys && not (in_env x g) } @-}
lem_above_max_nms_type :: Vname -> Names -> Names -> Env -> Proof
lem_above_max_nms_type _ []     []     Empty         = ()
lem_above_max_nms_type x []     []     (Cons  y t g) = lem_above_max_nms_type x [] [] g
lem_above_max_nms_type x []     []     (ConsT a k g) = lem_above_max_nms_type x [] [] g
lem_above_max_nms_type x []     (_:ys) g             = lem_above_max_nms_type x [] ys g
lem_above_max_nms_type x (_:xs) ys     g             = lem_above_max_nms_type x xs ys g

{-@ fresh_varFTs :: xs:Names -> g:Env -> t1:FType -> t2:FType 
        -> { x:Vname | not (Set_mem x (ffreeTV t1)) && not (Set_mem x (ffreeTV t2)) && 
                       not (in_env x g)             && NotElem x xs } @-}
fresh_varFTs :: Names -> Env -> FType -> FType -> Vname
fresh_varFTs xs g t1 t2 
  = n `withProof` lem_above_max_nms_ftypes n xs (ffreeTVList t1) (ffreeTVList t2) g
      where
        n    = 1 + max_nms_ftypes xs (ffreeTVList t1) (ffreeTVList t2) g

{-@ reflect max_nms_ftypes @-}
{-@ max_nms_ftypes :: Names -> Names -> Names -> Env -> { x:Vname | x >= 0 } @-}
max_nms_ftypes :: Names -> Names -> Names -> Env -> Vname 
max_nms_ftypes ([])   ([])   ([])   Empty         = 0
max_nms_ftypes ([])   ([])   ([])   (Cons  x t g) 
  = if (x > max_nms_ftypes [] [] [] g) then x else (max_nms_ftypes [] [] [] g)
max_nms_ftypes ([])   ([])   ([])   (ConsT a k g)
  = if (a > max_nms_ftypes [] [] [] g) then a else (max_nms_ftypes [] [] [] g)
max_nms_ftypes ([])   ([])   (z:zs) g 
  = if (z > max_nms_ftypes [] [] zs g) then z else (max_nms_ftypes [] [] zs g)
max_nms_ftypes ([])   (y:ys) zs     g 
  = if (y > max_nms_ftypes [] ys zs g) then y else (max_nms_ftypes [] ys zs g)
max_nms_ftypes (x:xs) ys     zs     g 
  = if (x > max_nms_ftypes xs ys zs g) then x else (max_nms_ftypes xs ys zs g)

{-@ lem_above_max_nms_ftypes :: x:Vname -> xs:Names -> ys:Names -> zs:Names
        -> { g:Env | x > max_nms_ftypes xs ys zs g } 
        -> { pf:_ | NotElem x xs && NotElem x ys && NotElem x zs && not (in_env x g) } @-}
lem_above_max_nms_ftypes :: Vname -> Names -> Names -> Names -> Env -> Proof
lem_above_max_nms_ftypes _ []     []     []     Empty         = ()
lem_above_max_nms_ftypes x []     []     []     (Cons  y t g) 
  = lem_above_max_nms_ftypes x [] [] [] g
lem_above_max_nms_ftypes x []     []     []     (ConsT a k g) 
  = lem_above_max_nms_ftypes x [] [] [] g
lem_above_max_nms_ftypes x []     []     (_:zs) g = lem_above_max_nms_ftypes x [] [] zs g
lem_above_max_nms_ftypes x []     (_:ys) zs     g = lem_above_max_nms_ftypes x [] ys zs g
lem_above_max_nms_ftypes x (_:xs) ys     zs     g = lem_above_max_nms_ftypes x xs ys zs g

---------------------------------------------------------------------------
----- | PROPOSITIONS
---------------------------------------------------------------------------

{-@ reflect withProof @-}
{-@ withProof :: x:a -> Proof -> { v:a | v = x } @-}
withProof :: a -> Proof -> a
withProof x _ = x

{-@ (?) :: x:a -> Proof -> { v:a | v = x } @-}
(?) :: a -> Proof -> a
(?) x _ = x

{-@ measure propOf :: a -> Proposition @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

  --- the Type of all Propositions

data Proposition where
    -- Operational Semantics
    Step :: Expr -> Expr -> Proposition         -- e ~> e'
    EvalsTo :: Expr -> Expr -> Proposition      -- e ~>* e'
    PEvalsTrue :: Preds -> Proposition          -- ps => PEmpty

    -- System F Judgments
    WFFT :: FEnv -> FType -> Kind -> Proposition      --  G |- t : k
    WFFE :: FEnv -> Proposition                       --    |- G
    HasFType :: FEnv -> Expr -> FType -> Proposition  --  G |- e : t
    PHasFType :: FEnv -> Preds -> Proposition         --  G |- ps : [FTBasic TBool]
    
    -- System RF Judgments
    WFType :: Env -> Type -> Kind -> Proposition
    WFEnv :: Env -> Proposition
    HasType :: Env -> Expr -> Type -> Proposition -- HasType G e t means G |- e : t
    Subtype :: Env -> Type -> Type -> Proposition
    Implies :: Env -> Preds -> Preds -> Proposition   --  G |= p => q
