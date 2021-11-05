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
{-@ delta :: p:Prim -> { e:Value | isCompat p e } -> { e':Value | Set_emp (fv e') } @-}
delta :: Prim -> Expr -> Expr
delta And (Bc True)   = Lambda 1 (BV 1)
delta And (Bc False)  = Lambda 1 (Bc False)
delta Or  (Bc True)   = Lambda 1 (Bc True)
delta Or  (Bc False)  = Lambda 1 (BV 1)
delta Not (Bc True)   = Bc False
delta Not (Bc False)  = Bc True
delta Eqv (Bc True)   = Lambda 1 (BV 1)
delta Eqv (Bc False)  = Lambda 1 (App (Prim Not) (BV 1))
delta Leq      (Ic n) = Prim (Leqn n)
delta (Leqn n) (Ic m) = Bc (n <= m)
delta Eq       (Ic n) = Prim (Eqn n)
delta (Eqn n)  (Ic m) = Bc (n == m)

data StepP where
    Step :: Expr -> Expr -> StepP

data Step where
    EPrim :: Prim -> Expr -> Step
    EApp1 :: Expr -> Expr -> Step -> Expr -> Step
    EApp2 :: Expr -> Expr -> Step -> Expr -> Step
    EAppAbs :: Vname -> Expr -> Expr -> Step

{-@ data Step where 
        EPrim :: c:Prim -> { w:Value | isCompat c w } 
                        -> ProofOf( Step (App (Prim c) w) (delta c w) ) 
        EApp1 :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                   -> e1:Expr -> ProofOf( Step (App e e1) (App e' e1)) 
        EApp2 :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                   -> v:Value -> ProofOf( Step (App v e) (App v e')) 
        EAppAbs :: x:Vname -> e:Expr -> v:Value  
                   -> ProofOf( Step (App (Lambda x e) v) (subBV x v e))  @-} -- @-}

data EvalsToP where
    EvalsTo :: Expr -> Expr -> EvalsToP

data EvalsTo where
    Refl     :: Expr -> EvalsTo
    AddStep  :: Expr -> Expr -> Step -> Expr -> EvalsTo -> EvalsTo
{-@ data EvalsTo where 
        Refl     :: e:Expr -> ProofOf ( EvalsTo e e ) 
        AddStep  :: e1:Expr -> e2:Expr -> ProofOf( Step e1 e2 ) -> e3:Expr
                 -> ProofOf ( EvalsTo e2 e3 ) -> ProofOf( EvalsTo e1 e3 ) @-} -- @-} 

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
                             -> e':Expr -> v':Value -> ProofOf(EvalsTo e' v')
                             -> ProofOf(EvalsTo (App e e') (App v v')) @-}
lemma_app_both_many :: Expr -> Expr -> EvalsTo -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_app_both_many e v ev_e_v e' v' ev_e'_v' = ev_ee'_vv'
  where
    ev_ee'_ve' = lemma_app_many  e v  e' ev_e_v
    ev_ve'_vv' = lemma_app_many2 v e' v' ev_e'_v'
    ev_ee'_vv' = lemma_evals_trans (App e e') (App v e') (App v v') 
                                   ev_ee'_ve' ev_ve'_vv'

data AppReducedP where
    AppReduced :: Expr -> Expr -> AppReducedP

{-@ data AppReduced where
        AppRed :: e:Expr -> { v:Expr | isValue v } -> ProofOf(EvalsTo e v) -> e':Expr 
                    -> { v':Expr | isValue v' } -> ProofOf(EvalsTo e' v') -> ProofOf(AppReduced e e') @-}
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

--------------------------------------------------------------------------
----- | Basic LEMMAS of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

{-@ lem_value_stuck :: e:Expr -> e':Expr -> ProofOf(Step e e') 
                   -> { proof:_ | not (isValue e) } @-}
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

{-@ lem_value_refl :: { v:Expr | isValue v } -> v':Expr -> ProofOf(EvalsTo v v')
                -> { pf:_ | v == v' } @-}
lem_value_refl :: Expr -> Expr -> EvalsTo -> Proof
lem_value_refl v v' (Refl _v) = ()
lem_value_refl v v' (AddStep _v v1 st_v_v1 _v' ev_v1_v')
    = impossible ("stuck" ? lem_value_stuck v v1 st_v_v1)

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
