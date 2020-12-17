{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module SameBinders where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

  --- DEFINITIONS
{-
{-@ reflect refn_binders @-} -- all of the "binders" are term variable binders only
{-@ refn_binders :: e:Expr -> S.Set Vname / [esize e] @-}
refn_binders :: Expr -> S.Set Vname
refn_binders (Lambda x e)    = refn_binders e
refn_binders (App e e')      = S.union (refn_binders e)   (refn_binders e')
refn_binders (LambdaT a k e) = refn_binders e
refn_binders (AppT e t)      = S.union (refn_binders e)   (refn_bindersT t)
refn_binders (Let x e_x e)   = S.union (refn_binders e_x) (refn_binders e)
refn_binders (Annot e t)     = S.union (refn_binders e)   (refn_bindersT t)
refn_binders _               = S.empty

{-@ reflect refn_bindersT @-}
{-@ refn_bindersT :: t:Type -> S.Set Vname / [tsize t] @-}
refn_bindersT :: Type -> S.Set Vname
refn_bindersT (TRefn b' x' p')   = S.union (S.singleton x')    (refn_binders p')
refn_bindersT (TFunc x t_x t')   = S.union (refn_bindersT t_x) (refn_bindersT t')
refn_bindersT (TExists x t_x t') = S.union (refn_bindersT t_x) (refn_bindersT t')
refn_bindersT (TPoly a k   t')   = refn_bindersT t'

{-@ reflect binders_are @-}
binders_are :: Type -> Vname -> Bool
binders_are (TRefn b x p)     x' =  x == x'
binders_are (TFunc   x t_x t) x' = binders_are t_x x' && binders_are t x'
binders_are (TExists x t_x t) x' = binders_are t_x x' && binders_are t x'
binders_are (TPoly   a k   t) x' = binders_are t x'
-}
