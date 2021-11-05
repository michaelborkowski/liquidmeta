{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Semantics where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics

--------------------------------------------------------------------------
----- | OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

-- E-Prim    c v -> delta(c,v)
-- E-App1    e e1 -> e' e1 if e->e'
-- E-App2    v e  -> v e'  if e->e'
-- E-AppAbs  (\x. e) v -> e[v/x]
-- E-PrimT   c [t] -> deltaT(c,t)
-- E-AppT    e [t] -> e' [t] id e->e'
-- E-AppTAbs (/\a. e) [t] -> e[t/a]
-- E-Let     let x=e_x in e -> let x=e'_x in e if e_x->e'_x
-- E-LetV    let x=v in e -> e[v/x]
-- E-Ann     e:t -> e':t  if e->e'
-- E-AnnV    v:t -> v

{-@ reflect isCompat @-}
isCompat :: Prim -> Expr -> Bool
isCompat And (Bc _)      = True
isCompat Or  (Bc _)      = True
isCompat Not (Bc _)      = True
isCompat Eqv (Bc _)      = True
isCompat Leq      (Ic _) = True
isCompat (Leqn _) (Ic _) = True
isCompat Eq       (Ic _) = True
isCompat (Eqn _)  (Ic _) = True
isCompat _        _      = False

{-@ reflect delta @-}
{-@ delta :: p:Prim -> { e:Value | isCompat p e } 
                    -> { e':Value | Set_emp (fv e') && Set_emp (ftv e') } @-}
delta :: Prim -> Expr -> Expr
delta And  (Bc True)   = Lambda 1 (BV 1)
delta And  (Bc False)  = Lambda 1 (Bc False)
delta Or   (Bc True)   = Lambda 1 (Bc True)
delta Or   (Bc False)  = Lambda 1 (BV 1)
delta Not  (Bc True)   = Bc False
delta Not  (Bc False)  = Bc True
delta Eqv  (Bc True)   = Lambda 1 (BV 1)
delta Eqv  (Bc False)  = Lambda 1 (App (Prim Not) (BV 1))
delta Leq      (Ic n)  = Prim (Leqn n)
delta (Leqn n) (Ic m)  = Bc (n <= m)
delta Eq       (Ic n)  = Prim (Eqn n)
delta (Eqn n)  (Ic m)  = Bc (n == m)

{-@ reflect isCompatT @-}
isCompatT :: Prim -> Type -> Bool
isCompatT Eql t | erase t == (FTBasic TBool) = True
                | erase t == (FTBasic TInt)  = True
isCompatT _   _                              = False

{-@ reflect deltaT @-}
{-@ deltaT :: c:Prim -> { t:Type | isCompatT c t }
                     -> { e':Value | isTerm e' && Set_emp (fv e') && Set_emp (ftv e') } @-}
deltaT :: Prim -> Type -> Expr
deltaT  Eql    t = case (erase t) of
  (FTBasic b)    -> case b of
    TBool             -> Prim Eqv
    TInt              -> Prim Eq

{-@ reflect isCompatC @-}
isCompatC :: Expr -> Expr -> Bool
isCompatC (Bc _) (Bc _) = True
isCompatC _      _      = False

{-@ reflect deltaC @-}
{-@ deltaC :: v1:Value -> { v2:Value | isCompatC v1 v2 } 
                       -> { v':Value | Set_emp (fv v') && Set_emp (ftv v') } @-}
deltaC :: Expr -> Expr -> Expr
deltaC (Bc True) (Bc True) = Bc True
deltaC (Bc _)    (Bc _)    = Bc False

{-@ lem_deltaC_tt :: v1:Value ->  { v2:Value | isCompatC v1 v2 && deltaC v1 v2 == Bc True}
        -> { pf:_  | v1 == Bc True && v2 == Bc True } @-}
lem_deltaC_tt :: Expr -> Expr -> Proof
lem_deltaC_tt (Bc True) (Bc True) = ()

data Step where
    EPrim :: Prim -> Expr -> Step
    EApp1 :: Expr -> Expr -> Step -> Expr -> Step
    EApp2 :: Expr -> Expr -> Step -> Expr -> Step
    EAppAbs :: Vname -> Expr -> Expr -> Step
    EPrimT :: Prim -> Type -> Step
    EAppT :: Expr -> Expr -> Step -> Type -> Step
    EAppTAbs :: Vname -> Kind -> Expr -> Type -> Step
    ELet  :: Expr -> Expr -> Step -> Vname -> Expr -> Step
    ELetV :: Vname -> Expr -> Expr -> Step
    EAnn  :: Expr -> Expr -> Step -> Type -> Step
    EAnnV :: Expr -> Type -> Step
    EConj1 :: Expr -> Expr -> Step -> Expr -> Step
    EConj2 :: Expr -> Expr -> Step -> Expr -> Step
    EConjV :: Expr -> Expr -> Step

{-@ data Step where 
        EPrim :: c:Prim -> { w:Value | isCompat c w }
                        -> ProofOf( Step (App (Prim c) w) (delta c w) ) 
        EApp1 :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                   -> e1:Expr -> ProofOf( Step (App e e1) (App e' e1)) 
        EApp2 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                   -> v:Value -> ProofOf( Step (App v e) (App v e')) 
        EAppAbs :: x:Vname -> e:Expr -> v:Value  
                   -> ProofOf( Step (App (Lambda x e) v) (subBV x v e)) 
        EPrimT :: c:Prim -> { t:Type | isCompatT c t }
                         -> ProofOf( Step (AppT (Prim c) t) (deltaT c t) ) 
        EAppT :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                   -> t:UserType -> ProofOf( Step (AppT e t) (AppT e' t)) 
        EAppTAbs :: a:Vname -> k:Kind -> e:Expr -> t:UserType 
                   -> ProofOf( Step (AppT (LambdaT a k e) t) (subBTV a t e)) 
        ELet  :: e_x:Expr -> e_x':Expr -> ProofOf( Step e_x e_x' )
                   -> x:Vname -> e:Expr -> ProofOf( Step (Let x e_x e) (Let x e_x' e)) 
        ELetV :: x:Vname -> v:Value -> e:Expr
                   -> ProofOf( Step (Let x v e) (subBV x v e)) 
        EAnn  :: e:Expr -> e':Expr -> ProofOf(Step e e')
                   -> t:Type -> ProofOf(Step (Annot e t) (Annot e' t)) 
        EAnnV :: v:Value -> t:Type -> ProofOf(Step (Annot v t) v) 
        EConj1 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                         -> e1:Expr -> ProofOf( Step (Conj e e1) (Conj e' e1))
        EConj2 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                         -> v:Value -> ProofOf( Step (Conj v e) (Conj v e'))
        EConjV :: v:Value -> { v':Value | isCompatC v v' } 
                          -> ProofOf( Step (Conj v v') (deltaC v v') ) @-} 

data EvalsTo where
    Refl     :: Expr -> EvalsTo
    AddStep  :: Expr -> Expr -> Step -> Expr -> EvalsTo -> EvalsTo
{-@ data EvalsTo where 
        Refl     :: e:Expr -> ProofOf ( EvalsTo e e ) 
        AddStep  :: e1:Expr -> e2:Expr -> ProofOf( Step e1 e2 ) -> e3:Expr
                 -> ProofOf ( EvalsTo e2 e3 ) -> ProofOf( EvalsTo e1 e3 ) @-} 

--------------------------------------------------------------------------
----- | Properties of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

-- EvalsToP is the transitive/reflexive closure of StepP:
{-@ lemma_evals_trans :: e1:Expr -> e2:Expr -> e3:Expr -> ProofOf( EvalsTo e1 e2)
                    -> ProofOf( EvalsTo e2 e3) -> ProofOf( EvalsTo e1 e3) @-} 
lemma_evals_trans :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo -> EvalsTo
lemma_evals_trans e1 e2 e3 (Refl _e1) p_e2e3 = p_e2e3
lemma_evals_trans e1 e2 e3 (AddStep _e1 e p_e1e _e2 p_ee2) p_e2e3 = p_e1e3
  where
    p_e1e3 = AddStep e1 e p_e1e e3 p_ee3
    p_ee3  = lemma_evals_trans e e2 e3 p_ee2 p_e2e3

{-@ lem_step_evals :: e:Expr -> e':Expr -> ProofOf(Step e e') -> ProofOf(EvalsTo e e') @-}
lem_step_evals :: Expr -> Expr -> Step -> EvalsTo
lem_step_evals e e' st_e_e' = AddStep e e' st_e_e' e' (Refl e')

{-@ lemma_add_step_after :: e:Expr -> e':Expr -> ProofOf(EvalsTo e e') -> e'':Expr
                       -> ProofOf(Step e' e'') -> ProofOf(EvalsTo e e'') @-}
lemma_add_step_after :: Expr -> Expr -> EvalsTo -> Expr -> Step -> EvalsTo
lemma_add_step_after e e' (Refl _e)                         e'' st_e'_e'' 
  = AddStep e' e'' st_e'_e'' e'' (Refl e'')
lemma_add_step_after e e' (AddStep _ e1 st_e_e1 _ ev_e1_e') e'' st_e'_e''
  = AddStep e e1 (st_e_e1) e'' (lemma_add_step_after e1 e' ev_e1_e' e'' st_e'_e'')

{-@ lemma_app_many :: e:Expr -> e':Expr -> v':Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (App e v') (App e' v')) @-}
lemma_app_many :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_many e e' v (Refl _e) = Refl (App e v)
lemma_app_many e e' v (AddStep _e e1 s_ee1 _e' p_e1e') = p_ev_e'v
  where
    p_ev_e'v  = AddStep (App e v) (App e1 v) s_ev_e1v (App e' v) p_e1v_e'v
    s_ev_e1v  = EApp1 e e1 s_ee1 v 
    p_e1v_e'v = lemma_app_many e1 e' v p_e1e' 

{-@ lemma_app_many2 :: v:Value -> e:Expr -> e':Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (App v e) (App v e')) @-}
lemma_app_many2 :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_many2 v e e' (Refl _e) = Refl (App v e)
lemma_app_many2 v e e' (AddStep _e e1 s_ee1 _e' p_e1e') = p_ve_ve'
  where
    p_ve_ve'  = AddStep (App v e) (App v e1) s_ve_ve1 (App v e') p_ve1_ve'
    s_ve_ve1  = EApp2 e e1 s_ee1 v 
    p_ve1_ve' = lemma_app_many2 v e1 e' p_e1e' 

{-@ lemma_app_both_many :: e:Expr -> v:Value -> ProofOf(EvalsTo e v)
                             -> e':Expr -> v':Expr -> ProofOf(EvalsTo e' v')
                             -> ProofOf(EvalsTo (App e e') (App v v')) @-}
lemma_app_both_many :: Expr -> Expr -> EvalsTo -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_both_many e v ev_e_v e' v' ev_e'_v' = ev_ee'_vv'
  where
    ev_ee'_ve' = lemma_app_many  e v  e' ev_e_v
    ev_ve'_vv' = lemma_app_many2 v e' v' ev_e'_v'
    ev_ee'_vv' = lemma_evals_trans (App e e') (App v e') (App v v') 
                                   ev_ee'_ve' ev_ve'_vv'

{-@ lemma_appT_many :: e:Expr -> e':Expr -> t:UserType -> ProofOf(EvalsTo e e')
        -> ProofOf(EvalsTo (AppT e t) (AppT e' t)) @-}
lemma_appT_many :: Expr -> Expr -> Type -> EvalsTo -> EvalsTo
lemma_appT_many e e' t (Refl _e) = Refl (AppT e t)
lemma_appT_many e e' t (AddStep  _e e1 s_ee1 _e' p_e1e') = ev_et_e't
  where
   ev_et_e't  = AddStep (AppT e t) (AppT e1 t) s_et_e1t (AppT e' t) ev_e1t_e't
   s_et_e1t   = EAppT e e1 s_ee1 t
   ev_e1t_e't = lemma_appT_many e1 e' t p_e1e'

{-@ lemma_let_many :: x:Vname -> e_x:Expr -> e_x':Expr -> e:Expr 
        -> ProofOf(EvalsTo e_x e_x') -> ProofOf(EvalsTo (Let x e_x e) (Let x e_x' e)) @-}
lemma_let_many :: Vname -> Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_let_many x e_x e_x' e (Refl _ex)                               = Refl (Let x e_x e)
lemma_let_many x e_x e_x' e (AddStep _ex e_x1 s_exex1 _ex' p_ex1ex') = p_let_let'
  where
    s_let_let1  = ELet e_x e_x1 s_exex1 x e
    p_let1_let' = lemma_let_many x e_x1 e_x' e p_ex1ex'
    p_let_let'  = AddStep (Let x e_x e) (Let x e_x1 e) s_let_let1 (Let x e_x' e) p_let1_let'

{-@ lemma_annot_many :: e:Expr -> e':Expr -> t:Type -> ProofOf(EvalsTo e e')
                         -> ProofOf(EvalsTo (Annot e t) (Annot e' t)) @-}
lemma_annot_many :: Expr -> Expr -> Type -> EvalsTo -> EvalsTo
lemma_annot_many e e' t (Refl _e) = Refl (Annot e t)
lemma_annot_many e e' t (AddStep _e e1 s_ee1 _e' p_e1e') = p_et_e't
  where
    s_et_e1t  = EAnn e e1 s_ee1 t
    p_e1t_e't = lemma_annot_many e1 e' t p_e1e'
    p_et_e't  = AddStep (Annot e t) (Annot e1 t) s_et_e1t (Annot e' t) p_e1t_e't

{-@ lemma_conj_many :: e:Expr -> e':Expr -> v':Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (Conj e v') (Conj e' v')) @-}
lemma_conj_many :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_conj_many e e' v (Refl _e) = Refl (Conj e v)
lemma_conj_many e e' v (AddStep _e e1 s_ee1 _e' p_e1e') = p_ev_e'v
  where
    p_ev_e'v  = AddStep (Conj e v) (Conj e1 v) s_ev_e1v (Conj e' v) p_e1v_e'v
    s_ev_e1v  = EConj1 e e1 s_ee1 v 
    p_e1v_e'v = lemma_conj_many e1 e' v p_e1e' 

{-@ lemma_conj_many2 :: v:Value -> e:Expr -> e':Expr -> ProofOf(EvalsTo e e')
                       -> ProofOf(EvalsTo (Conj v e) (Conj v e')) @-}
lemma_conj_many2 :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_conj_many2 v e e' (Refl _e) = Refl (Conj v e)
lemma_conj_many2 v e e' (AddStep _e e1 s_ee1 _e' p_e1e') = p_ve_ve'
  where
    p_ve_ve'  = AddStep (Conj v e) (Conj v e1) s_ve_ve1 (Conj v e') p_ve1_ve'
    s_ve_ve1  = EConj2 e e1 s_ee1 v 
    p_ve1_ve' = lemma_conj_many2 v e1 e' p_e1e' 

{-@ lemma_conj_both_many :: e:Expr -> v:Value -> ProofOf(EvalsTo e v)
                             -> e':Expr -> v':Value -> ProofOf(EvalsTo e' v')
                             -> ProofOf(EvalsTo (Conj e e') (Conj v v')) @-}
lemma_conj_both_many :: Expr -> Expr -> EvalsTo -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_conj_both_many e v ev_e_v e' v' ev_e'_v' = ev_ee'_vv'
  where
    ev_ee'_ve' = lemma_conj_many  e v  e' ev_e_v
    ev_ve'_vv' = lemma_conj_many2 v e' v' ev_e'_v'
    ev_ee'_vv' = lemma_evals_trans (Conj e e') (Conj v e') (Conj v v') 
                                   ev_ee'_ve' ev_ve'_vv'


{-@ data AppReduced where
        AppRed :: e:Expr -> { v:Expr | isValue v } -> ProofOf(EvalsTo e v) -> e':Expr 
                         -> { v':Expr | isValue v' } -> ProofOf(EvalsTo e' v') 
                         -> ProofOf(AppReduced e e') @-}
data AppReduced where
    AppRed :: Expr -> Expr -> EvalsTo -> Expr -> Expr -> EvalsTo -> AppReduced

{-@ lemma_evals_app_value :: e:Expr -> e':Expr -> { v:Expr | isValue v } 
        -> ProofOf(EvalsTo (App e e') v)
        -> ProofOf(AppReduced e e') @-}
lemma_evals_app_value :: Expr -> Expr -> Expr -> EvalsTo -> AppReduced
lemma_evals_app_value e e' v (Refl _v) = impossible "App not a value"
lemma_evals_app_value e e' v (AddStep _ee' eee st_ee'_eee _v ev_eee_v)
  = case st_ee'_eee of 
      (EPrim c w)                 -> AppRed e (Prim c) (Refl (Prim c)) e' w (Refl w)
      (EApp1 _e e1 st_e_e1 _e')   -> AppRed e v1 ev_e_v1 e' v2 ev_e'_v2
        where
          (AppRed _ v1 ev_e1_v1 _ v2 ev_e'_v2) = lemma_evals_app_value e1 e' v ev_eee_v
          ev_e_v1                              = AddStep e e1 st_e_e1 v1 ev_e1_v1
      (EApp2 _e' e2 st_e'_e2 _e)  -> AppRed e e (Refl e) e' v2 ev_e'_v2
        where
          (AppRed _ _ _ _e2 v2 ev_e2_v2)       = lemma_evals_app_value e e2 v ev_eee_v
          ev_e'_v2                             = AddStep e' e2 st_e'_e2 v2 ev_e2_v2
      (EAppAbs x e'' w)           -> AppRed e e (Refl e) e' e' (Refl e')

{-@ data ConjReduced where
        ConjRed :: e:Expr -> { v:Expr | isValue v } -> ProofOf(EvalsTo e v) -> e':Expr 
                         -> { v':Expr | isValue v' } -> ProofOf(EvalsTo e' v') 
                         -> ProofOf(ConjReduced e e') @-}
data ConjReduced where
    ConjRed :: Expr -> Expr -> EvalsTo -> Expr -> Expr -> EvalsTo -> ConjReduced

{-@ lemma_evals_conj_value :: e:Expr -> e':Expr -> { v:Expr | isValue v } 
        -> ProofOf(EvalsTo (Conj e e') v)
        -> ProofOf(ConjReduced e e') @-}
lemma_evals_conj_value :: Expr -> Expr -> Expr -> EvalsTo -> ConjReduced
lemma_evals_conj_value e e' v (Refl _v) = impossible "Conj not a value"
lemma_evals_conj_value e e' v (AddStep _ee' eee st_ee'_eee _v ev_eee_v)
  = case st_ee'_eee of 
      (EConj1 _e e1 st_e_e1 _e')   -> ConjRed e v1 ev_e_v1 e' v2 ev_e'_v2
        where
          (ConjRed _ v1 ev_e1_v1 _ v2 ev_e'_v2) = lemma_evals_conj_value e1 e' v ev_eee_v
          ev_e_v1                              = AddStep e e1 st_e_e1 v1 ev_e1_v1
      (EConj2 _e' e2 st_e'_e2 _e)  -> ConjRed e e (Refl e) e' v2 ev_e'_v2
        where
          (ConjRed _ _ _ _e2 v2 ev_e2_v2)       = lemma_evals_conj_value e e2 v ev_eee_v
          ev_e'_v2                             = AddStep e' e2 st_e'_e2 v2 ev_e2_v2
      (EConjV v v')                -> ConjRed v v (Refl v) v' v' (Refl v')

{-@ lem_evals_trivial :: { tt:Pred | isTrivial tt } -> ProofOf(EvalsTo tt (Bc True)) @-}
lem_evals_trivial :: Expr -> EvalsTo
lem_evals_trivial (Bc True) = Refl (Bc True) 
lem_evals_trivial (Conj p r) = lemma_add_step_after (Conj p r) (Conj p (Bc True))
                                                    ev_pr_idtt (Bc True) (EConjV (Bc True) (Bc True))
  where
    ev_r_tt    = lem_evals_trivial r
    ev_pr_idtt = lemma_conj_many2 p r (Bc True) ev_r_tt

--------------------------------------------------------------------------
----- | Basic LEMMAS of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

{-@ lem_value_stuck :: e:Expr -> e':Expr -> ProofOf(Step e e') -> { pf:_ | not (isValue e) } @-}
lem_value_stuck :: Expr -> Expr -> Step -> Proof
lem_value_stuck e  e' (EPrim _ _)      
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EApp1 _ _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EApp2 _ _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAppAbs _ _ _)  
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EPrimT _ _)      
    = case e of 
        (AppT _ _)   -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAppT _ _ _ _)  
    = case e of 
        (AppT _ _)   -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAppTAbs _ _ _ _)  
    = case e of 
        (AppT _ _)   -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELet _ _ _ _ _) 
    = case e of 
        (Let _ _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELetV _ _ _)    
    = case e of 
        (Let _ _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnn _ _ _ _)   
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnnV _ _)      
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EConj1 _ _ _ _)  
    = case e of 
        (Conj _ _)    -> ()
        (_)           -> impossible ""
lem_value_stuck e  e' (EConj2 _ _ _ _)  
    = case e of 
        (Conj _ _)    -> ()
        (_)           -> impossible ""
lem_value_stuck e  e' (EConjV _ _)  
    = case e of 
        (Conj _ _)    -> ()
        (_)           -> impossible ""

{-@ lem_value_refl :: { v:Expr | isValue v } -> v':Expr -> ProofOf(EvalsTo v v')
                -> { pf:_ | v == v' } @-}
lem_value_refl :: Expr -> Expr -> EvalsTo -> Proof
lem_value_refl v v' (Refl _v) = ()
lem_value_refl v v' (AddStep _v v1 st_v_v1 _v' ev_v1_v')
    = impossible ("stuck" ? lem_value_stuck v v1 st_v_v1)

{-@ lem_step_term :: { e:Expr | isTerm e } -> e1:Expr -> ProofOf(Step e e1) -> { pf:_ | isTerm e1 } @-}
lem_step_term :: Expr -> Expr -> Step -> Proof
lem_step_term e e1 p1@(EPrim c v)       = () ? toProof ( isTerm ( delta c v ) )
lem_step_term e e' (EApp1 e1 e1' p_e1e1' e2) 
  = () ? lem_step_term e1 e1' p_e1e1'     -- e = e1 e2, e' = e1' e2, e'' = e1'' e2
lem_step_term e e' (EApp2 e1 e1' p_e1e1' v1) 
  = () ? lem_step_term e1 e1' p_e1e1'     -- e = v1 e1, e' = v1 e1', e'' = v1 e1''
lem_step_term e e1 (EAppAbs x e' v)     = () ? toProof ( isTerm ( subBV x v e' ) )
lem_step_term e e' (EPrimT c t')        = () 
lem_step_term e e' (EAppT e1 e1' p_e1e1' t') 
  = () ? lem_step_term e1 e1' p_e1e1'
lem_step_term e e1 (EAppTAbs a k e' t') = () ? toProof ( isTerm ( subBTV a t' e' ) )
lem_step_term e e1 (ELet e_x e_x' p_ex_ex' x e1') 
  = () ? lem_step_term e_x e_x' p_ex_ex'
lem_step_term e e1 (ELetV x v e')       = () ? toProof ( isTerm ( subBV x v e') )
lem_step_term e e1 (EAnn e' e1' p_e_e1' t')
  = () ? lem_step_term e' e1' p_e_e1'
lem_step_term e e1 (EAnnV v t')         = ()

{-@ lem_step_pred :: { e:Expr | isPred e } -> e1:Expr -> ProofOf(Step e e1) -> { pf:_ | isPred e1 } @-}
lem_step_pred :: Expr -> Expr -> Step -> Proof
lem_step_pred e e1 p1@(EPrim c v)       = () ? toProof ( isPred ( delta c v ) )
lem_step_pred e e' (EApp1 e1 e1' p_e1e1' e2) 
  = () ? lem_step_term e1 e1' p_e1e1'     -- e = e1 e2, e' = e1' e2, e'' = e1'' e2
lem_step_pred e e' (EApp2 e1 e1' p_e1e1' v1) 
  = () ? lem_step_term e1 e1' p_e1e1'     -- e = v1 e1, e' = v1 e1', e'' = v1 e1''
lem_step_pred e e1 (EAppAbs x e' v)     = () ? toProof ( isPred ( subBV x v e' ) )
lem_step_pred e e' (EPrimT c t')        = () 
lem_step_pred e e' (EAppT e1 e1' p_e1e1' t') 
  = () ? lem_step_term e1 e1' p_e1e1'
lem_step_pred e e1 (EAppTAbs a k e' t') = () ? toProof ( isPred ( subBTV a t' e' ) )
lem_step_pred e e1 (ELet e_x e_x' p_ex_ex' x e1') 
  = () ? lem_step_term e_x e_x' p_ex_ex'
lem_step_pred e e1 (ELetV x v e')       = () ? toProof ( isPred ( subBV x v e') )
lem_step_pred e e1 (EAnn e' e1' p_e_e1' t')
  = () ? lem_step_term e' e1' p_e_e1'
lem_step_pred e e1 (EAnnV v t')         = ()
lem_step_pred e e' (EConj1 e1 e1' p_e1e1' e2) 
  = () ? lem_step_pred e1 e1' p_e1e1'     -- e = e1 e2, e' = e1' e2, e'' = e1'' e2
lem_step_pred e e' (EConj2 e1 e1' p_e1e1' v1) 
  = () ? lem_step_pred e1 e1' p_e1e1'     -- e = v1 e1, e' = v1 e1', e'' = v1 e1''
lem_step_pred e e1 (EConjV v v')        = ()

{-@ lem_evals_term :: e:Term -> e':Expr -> ProofOf(EvalsTo e e') -> { pf:_ | isTerm e' } @-}
lem_evals_term :: Expr -> Expr -> EvalsTo -> Proof
lem_evals_term e e' (Refl _e) = ()
lem_evals_term e e' (AddStep _ e1 st_e_e1 _ ev_e1_e') 
  = () ? lem_evals_term (e1 ? lem_step_term e e1 st_e_e1) e' ev_e1_e'

{-@ lem_evals_pred :: e:Pred -> e':Expr -> ProofOf(EvalsTo e e') -> { pf:_ | isPred e' } @-}
lem_evals_pred :: Expr -> Expr -> EvalsTo -> Proof
lem_evals_pred e e' (Refl _e) = ()
lem_evals_pred e e' (AddStep _ e1 st_e_e1 _ ev_e1_e') 
  = () ? lem_evals_pred (e1 ? lem_step_pred e e1 st_e_e1) e' ev_e1_e'

{-@ lem_sem_det :: e:Expr -> e1:Expr -> ProofOf(Step e e1)
                   -> e2:Expr -> ProofOf(Step e e2) -> { x:_ | e1 == e2 } @-}
lem_sem_det :: Expr -> Expr -> Step -> Expr -> Step -> Proof
lem_sem_det e e1 p1@(EPrim _ _) e2 p2  -- e = App (Prim c) w
    = case p2 of    
        (EPrim _ _)            -> ()            
        (EApp1 f f' p_f_f' f1) -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EApp2 f f' p_f_f' v)  -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppAbs {})           -> impossible "OK"
        (_)                    -> impossible ""
lem_sem_det e e' (EApp1 e1 e1' p_e1e1' e2) e'' pf_e_e''
    = case pf_e_e'' of
        (EPrim _ _)                 -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EApp1 _e1 e1'' p_e1e1'' _) -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''  
        (EApp2 g g' p_g_g' v)       -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EAppAbs {})                -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                         -> impossible "" 
    -- e = e1 e2, e' = e1' e2, e'' = e1'' e2
lem_sem_det e e' (EApp2 e1 e1' p_e1e1' v1) e'' pf_e_e''
    = case pf_e_e'' of
        (EPrim _ _)                 -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EApp1 _v1 v1' p_v1v1' _)   -> impossible ("by lem" ? lem_value_stuck _v1 v1' p_v1v1')
        (EApp2 _ e1'' p_e1e1'' _)   -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''
        (EAppAbs {})                -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                         -> impossible ""
    -- e = v1 e1, e' = v1 e1', e'' = v1 e1''
lem_sem_det e e1 (EAppAbs x e' v) e2 pf_e_e2
    = case pf_e_e2 of 
        (EPrim {})                  -> impossible ""
        (EApp1 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EApp2 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppAbs _x _e' _v)         -> ()
        (_)                         -> impossible ""
lem_sem_det e e' (EPrimT _ _) e'' pf2
    = case pf2 of
        (EPrimT _ _)                -> ()
        (EAppT e1 e1' p_e1e1' _)    -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EAppTAbs {})               -> impossible ""
lem_sem_det e e' (EAppT e1 e1' p_e1e1' t) e'' pf_e_e''
    = case pf_e_e'' of
        (EPrimT _ _)                -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EAppT _e1 e1'' p_e1e1'' _) -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''
        (EAppTAbs {})               -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
lem_sem_det e e1 (EAppTAbs a k e' t) e2 pf_e_e2
    = case pf_e_e2 of
        (EPrim _ _)                 -> impossible ""
        (EAppT f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppTAbs _a _k _e' _t)     -> ()
lem_sem_det e e1 (ELet e_x e_x' p_ex_ex' x e1') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet _ e_x'' p_ex_ex'' _x _) -> () ? lem_sem_det e_x e_x' p_ex_ex' e_x'' p_ex_ex''
        (ELetV _ _ _)                 -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (_)                           -> impossible ""
lem_sem_det e e1 (ELetV x v e') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet e_x e_x' p_ex_ex' _x _) -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (ELetV _ _ _)                 -> ()
        (_)                           -> impossible ""
lem_sem_det e e1 (EAnn e' e1' p_e_e1' t) e2 pf_e_e2
    = case pf_e_e2 of
        (EAnn _e' e2' p_e_e2' _t) -> () ? lem_sem_det e' e1' p_e_e1' e2' p_e_e2'
        (EAnnV {})                -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (_)                       -> impossible ""
lem_sem_det e e1 (EAnnV v t) e2 pf_e_e2
    = case pf_e_e2 of 
        (EAnn e' e1' p_e_e1' t)   -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (EAnnV _v _t)             -> ()
        (_)                       -> impossible "" 
lem_sem_det e e' (EConj1 e1 e1' p_e1e1' e2) e'' pf_e_e''
    = case pf_e_e'' of
        (EConj1 _e1 e1'' p_e1e1'' _) -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''  
        (EConj2 g g' p_g_g' v)       -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (EConjV {})                  -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                          -> impossible "" 
lem_sem_det e e' (EConj2 e1 e1' p_e1e1' v1) e'' pf_e_e''
    = case pf_e_e'' of
        (EConj1 _v1 v1' p_v1v1' _)   -> impossible ("by lem" ? lem_value_stuck _v1 v1' p_v1v1')
        (EConj2 _ e1'' p_e1e1'' _)   -> () ? lem_sem_det e1 e1' p_e1e1' e1'' p_e1e1''
        (EConjV {})                  -> impossible ("by lem" ? lem_value_stuck e1 e1' p_e1e1')
        (_)                          -> impossible ""
lem_sem_det e e1 (EConjV v v') e2 pf_e_e2
    = case pf_e_e2 of 
        (EConj1 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EConj2 f f' p_f_f' _)       -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EConjV _ _)                 -> ()
        (_)                          -> impossible ""

{-@ lem_evals_val_det :: e:Expr -> v1:Value -> ProofOf(EvalsTo e v1)
                   -> v2:Value -> ProofOf(EvalsTo e v2) -> { x:_ | v1 == v2 } @-}
lem_evals_val_det :: Expr -> Expr -> EvalsTo -> Expr -> EvalsTo -> Proof
lem_evals_val_det e v1 (Refl _v1) v2 ev_e_v2 = case (ev_e_v2) of
  (Refl _v2)                 -> () 
  (AddStep _ e' st_e_e' _ _) -> impossible ("by lemma" ? lem_value_stuck e e' st_e_e')
lem_evals_val_det e v1 (AddStep _ e1 st_e_e1 _ ev_e1_v1) v2 ev_e_v2 = case (ev_e_v2) of
  (Refl _v2)                       -> impossible ("by lemma" ? lem_value_stuck e e1 st_e_e1)
  (AddStep _ e2 st_e_e2 _ ev_e2_v2) -> lem_evals_val_det (e1 ? lem_sem_det e e1 st_e_e1 e2 st_e_e2)
                                                         v1 ev_e1_v1 v2 ev_e2_v2

{-@ lem_decompose_evals :: e:Expr -> e':Expr -> v:Value -> ProofOf(EvalsTo e e') 
                                  -> ProofOf(EvalsTo e v) -> ProofOf(EvalsTo e' v) @-}
lem_decompose_evals :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo -> EvalsTo
lem_decompose_evals e e' v ev_e_e' ev_e_v = case ev_e_e' of
  (Refl _e)                         -> ev_e_v
  (AddStep _ e1 st_e_e1 _ ev_e1_e') -> case ev_e_v of
    (Refl _) -> impossible ("by lemma" ? lem_value_stuck v e1 st_e_e1)
    (AddStep _ e2 st_e_e2 _ ev_e2_v) -> lem_decompose_evals e1 e' v ev_e1_e' ev_e1_v
      where
        ev_e1_v = ev_e2_v ? lem_sem_det e e1 st_e_e1 e2 st_e_e2


{-@ data CommonEvals where
        BothEv :: e:Expr -> e':Expr -> e'':Expr -> ProofOf(EvalsTo e e'') 
                         -> ProofOf(EvalsTo e' e'') -> ProofOf(CommonEvals e e') @-}

data CommonEvals where
    BothEv :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo -> CommonEvals

{-@ lem_common_evals_extend :: e:Expr -> e':Expr -> ProofOf(CommonEvals e e')
        -> v:Value -> ProofOf(EvalsTo e v) -> ProofOf(EvalsTo e' v) @-}
lem_common_evals_extend :: Expr -> Expr -> CommonEvals -> Expr -> EvalsTo -> EvalsTo
lem_common_evals_extend e e' (BothEv _ _ e1 ev_e_e1 ev_e'_e1) v ev_e_v
  = lemma_evals_trans e' e1 v ev_e'_e1 ev_e1_v
      where
        ev_e1_v = lem_decompose_evals e e1 v ev_e_e1 ev_e_v
