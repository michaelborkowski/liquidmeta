{-# LANGUAGE GADTs #-}

{- @ LIQUID "--no-termination" @-}
{- @ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--exact-data-cons"     @-}
{-@ LIQUID "--short-names" @-}

module Mutual where

import qualified Data.Set as S

type Vname = Int

{-@ data Expr [esize] @-}
data Expr = Bc Bool              -- True, False
          | FV Vname             -- FREE Variables: bound in an environment
          | Lambda Vname Expr    -- \x.e
          | App Expr Expr        -- e e'  TODO or does this become e v ??
          | Annot Expr Type      -- e : t
  deriving (Eq, Show)

{-@ measure esize @-}
{-@ esize :: e:Expr -> { v:Int | v >= 0 } @-}
esize :: Expr -> Int
esize (Bc _)	        = 1
esize (FV _)            = 1
esize (Lambda x e)      = (esize e)   + 1
esize (App e e')        = (esize e)   + (esize e') + 1
esize (Annot e t)       = (esize e)   + (tsize t) + 1

{-@ reflect fv @-}
{-@ fv :: e:Expr -> S.Set Vname / [esize e] @-}
fv :: Expr -> S.Set Vname
fv (Bc _)       = S.empty
fv (FV x)       = S.singleton x
fv (Lambda x e) = (fv e) -- S.difference (fv e) (S.singleton x)
fv (App e e')   = S.union (fv e) (fv e')
fv (Annot e t)  = S.union (fv e) (free t) -- fv e

{-@ reflect subFV @-} 
{-@ subFV :: x:Vname -> v:Expr -> e:Expr -> e':Expr / [esize e] @-}
subFV :: Vname -> Expr -> Expr -> Expr
subFV x e_x (Bc b)                    = Bc b
subFV x e_x (FV y) | x == y           = e_x 
                   | otherwise        = FV y
subFV x e_x (Lambda y e)              = Lambda y (subFV x e_x e)
subFV x e_x (App e e')                = App (subFV x e_x e) (subFV x e_x e')
subFV x e_x (Annot e t)               = Annot (subFV x e_x e) (tsubFV x e_x t) -- TODO not 100%


  ---   TYPES

data Base = TBool
          | TInt
  deriving (Eq, Show)

{-@ data Type [tsize] @-}
data Type = TRefn   Base Vname Expr      -- b{x : p}
          | TFunc   Vname Type Type      -- x:t_x -> t
  deriving (Eq, Show)

{-@ measure tsize @-}
{-@ tsize :: t:Type -> { v:Int | v >= 0 } @-}
tsize :: Type -> Int
tsize (TRefn b v e)     = (esize e)   + 1
tsize (TFunc x t_x t)   = (tsize t_x) + (tsize t) + 1

{-@ reflect free @-} 
{-@ free :: t:Type -> S.Set Vname / [tsize t] @-}
free :: Type -> S.Set Vname
free (TRefn b v r)      = fv r
free (TFunc x t_x t)    = S.union (free t_x) (free t) 

{-@ reflect tsubFV @-}
{-@ tsubFV :: x:Vname -> e:Expr -> t:Type -> t':Type / [tsize t] @-}
tsubFV :: Vname -> Expr -> Type -> Type
tsubFV x e_x (TRefn b z r)     = TRefn b z (subFV x e_x r)
tsubFV x e_x (TFunc z t_z t)   = TFunc   z (tsubFV x e_x t_z) (tsubFV x e_x t)

