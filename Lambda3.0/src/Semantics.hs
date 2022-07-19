{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Semantics where

import Prelude hiding (id, max)
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
-- E-Switch  switch e as -> switch e' as if e->e'
-- E-SwitchV switch (D v1 .. vn) as -> lookup()[v1/x1]...[vn/xn]

{-@ reflect isCompat @-}
isCompat :: Prim -> Const -> Bool
isCompat And  (Bc _)      = True
isCompat Or   (Bc _)      = True
isCompat Not  (Bc _)      = True
isCompat Eqv  (Bc _)      = True
isCompat Imp  (Bc _)      = True
isCompat Leq       (Ic _) = True
isCompat (Leqn _)  (Ic _) = True
isCompat Eq        (Ic _) = True
isCompat (Eqn _)   (Ic _) = True
isCompat _         _      = False

{-@ reflect delta @-}
{-@ delta :: p:Prim -> { e:Const | isCompat p e } 
                    -> { e':Value | Set_emp (fv e') && Set_emp (ftv e') } @-}
delta :: Prim -> Const -> Expr
delta And  (Bc True)   = Lambda (BV 0)
delta And  (Bc False)  = Lambda (C (Bc False))
delta Or   (Bc True)   = Lambda (C (Bc True))
delta Or   (Bc False)  = Lambda (BV 0)
delta Not  (Bc True)   = C (Bc False)
delta Not  (Bc False)  = C (Bc True)
delta Eqv  (Bc True)   = Lambda (BV 0)
delta Eqv  (Bc False)  = Lambda (App (C (Prim Not)) (BV 0))
delta Imp  (Bc True)   = Lambda (BV 0)
delta Imp  (Bc False)  = Lambda (C (Bc True))
delta Leq      (Ic n)  = C (Prim (Leqn n))
delta (Leqn n) (Ic m)  = C (Bc (n <= m))
delta Eq       (Ic n)  = C (Prim (Eqn n))
delta (Eqn n)  (Ic m)  = C (Bc (n == m))

{-@ reflect isCompatT @-}
isCompatT :: Prim -> Type -> Bool
isCompatT Eql t  | erase t == (FTBasic TBool) = True
                 | erase t == (FTBasic TInt)  = True
isCompatT Leql t | erase t == (FTBasic TBool) = True
                 | erase t == (FTBasic TInt)  = True
isCompatT _   _                               = False

{-@ reflect deltaT @-}
{-@ deltaT :: c:Prim -> { t:Type | isCompatT c t }
                     -> { e':Value | Set_emp (fv e') && Set_emp (ftv e') } @-}
deltaT :: Prim -> Type -> Expr
deltaT  Eql    t = case (erase t) of
  (FTBasic TBool)    -> C (Prim Eqv)
  (FTBasic TInt)     -> C (Prim Eq)
deltaT  Leql   t = case (erase t) of
  (FTBasic TBool)    -> C (Prim Imp) 
  (FTBasic TInt)     -> C (Prim Leq)

  -- reflected functions for match scrutinees

{-@ reflect altsIds @-}
altsIds :: Alts -> S.Set Id
altsIds AEmpty           = S.empty
altsIds (ACons dc e as)  = S.union (S.singleton (dcid dc)) (altsIds as)

{-@ reflect altsLookup @-}
{-@ altsLookup :: i:Id -> { as:Alts | Set_mem i (altsIds as) } -> Expr @-}
altsLookup :: Id -> Alts -> Expr
altsLookup i (ACons dc e as) | i == dcid dc  = e
                             | otherwise     = altsLookup i as

{-                     :: DataValue -> Alts -> Bool -}
{-@ predicate HasMatch DV AS =   Set_mem (dcid (dvdc DV)) (altsIds AS) && FullyApplied DV @-}

{-@ reflect getMatch @-}
{-@ getMatch :: dv:DataValue -> { as:Alts | HasMatch dv as } -> Expr @-}
getMatch :: Expr -> Alts -> Expr
getMatch dv as = altsLookup (dcid (dvdc dv)) as

{-@ reflect subMatch @-}
{-@ subMatch :: dv:DataValue -> { as:Alts | HasMatch dv as } -> Expr @-}
subMatch :: Expr -> Alts -> Expr
subMatch dv as = subMany dv (getMatch dv as)

{-@ reflect subMany @-}
{- @ subMany :: { dv:DataValue | argCount dv == arity (dvdc dv) } -> Expr -> Expr @-}
{-@ subMany :: DataValue -> Expr -> Expr @-}
subMany :: Expr -> Expr -> Expr
subMany (C (Dc _)) e = e
subMany (App dv v) e = subBV v (subMany dv e)

data Step where
    EPrim    :: Prim -> Const -> Step
    EApp1    :: Expr -> Expr -> Step -> Expr -> Step
    EApp2    :: Expr -> Expr -> Step -> Expr -> Step
    EAppAbs  :: Expr -> Expr -> Step
    EPrimT   :: Prim -> Type -> Step
    EAppT    :: Expr -> Expr -> Step -> Type -> Step
    EAppTAbs :: Kind -> Expr -> Type -> Step
    ELet     :: Expr -> Expr -> Step -> Expr -> Step
    ELetV    :: Expr -> Expr -> Step
    EAnn     :: Expr -> Expr -> Step -> Type -> Step
    EAnnV    :: Expr -> Type -> Step
    ESwitch  :: Expr -> Expr -> Step -> Alts -> Step
    ESwitchV :: Expr -> Alts -> Step

{-@ data Step where 
        EPrim    :: c:Prim -> { w:Const | isCompat c w }
                      -> ProofOf( Step (App (C (Prim c)) (C w)) (delta c w) ) 
        EApp1    :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                      -> e1:Expr -> ProofOf( Step (App e e1) (App e' e1)) 
        EApp2    :: e:Expr -> e':Expr -> ProofOf( Step e e' )
                      -> v:Value -> ProofOf( Step (App v e) (App v e')) 
        EAppAbs  :: e:Expr -> v:Value -> ProofOf( Step (App (Lambda e) v) (subBV v e)) 
        EPrimT   :: c:Prim -> { t:Type | isCompatT c t }
                      -> ProofOf( Step (AppT (C (Prim c)) t) (deltaT c t) ) 
        EAppT    :: e:Expr -> e':Expr -> ProofOf( Step e e' ) 
                      -> t:UserType -> ProofOf( Step (AppT e t) (AppT e' t)) 
        EAppTAbs :: k:Kind -> e:Expr -> t:UserType 
                      -> ProofOf( Step (AppT (LambdaT k e) t) (subBTV t e)) 
        ELet     :: e_x:Expr -> e_x':Expr -> ProofOf( Step e_x e_x' )
                      -> e:Expr -> ProofOf( Step (Let e_x e) (Let e_x' e)) 
        ELetV    :: v:Value -> e:Expr -> ProofOf( Step (Let v e) (subBV v e)) 
        EAnn     :: e:Expr -> e':Expr -> ProofOf(Step e e')
                      -> t:Type -> ProofOf(Step (Annot e t) (Annot e' t)) 
        EAnnV    :: v:Value -> t:Type -> ProofOf(Step (Annot v t) v) 
        ESwitch  :: e:Expr -> e':Expr -> ProofOf(Step e e')
                      -> as:Alts -> ProofOf(Step (Switch e as) (Switch e' as))
        ESwitchV :: dv:DataValue -> { as:Alts | HasMatch dv as }
                      -> ProofOf(Step (Switch dv as) (subMatch dv as))
@-}

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

{-@ lemma_let_many :: e_x:Expr -> e_x':Expr -> e:Expr 
        -> ProofOf(EvalsTo e_x e_x') -> ProofOf(EvalsTo (Let e_x e) (Let e_x' e)) @-}
lemma_let_many :: Expr -> Expr -> Expr -> EvalsTo -> EvalsTo
lemma_let_many e_x e_x' e (Refl _ex)                               = Refl (Let e_x e)
lemma_let_many e_x e_x' e (AddStep _ex e_x1 s_exex1 _ex' p_ex1ex') = p_let_let'
  where
    s_let_let1  = ELet e_x e_x1 s_exex1 e
    p_let1_let' = lemma_let_many e_x1 e_x' e p_ex1ex'
    p_let_let'  = AddStep (Let e_x e) (Let e_x1 e) s_let_let1 (Let e_x' e) p_let1_let'

{-@ lemma_annot_many :: e:Expr -> e':Expr -> t:Type -> ProofOf(EvalsTo e e')
                         -> ProofOf(EvalsTo (Annot e t) (Annot e' t)) @-}
lemma_annot_many :: Expr -> Expr -> Type -> EvalsTo -> EvalsTo
lemma_annot_many e e' t (Refl _e) = Refl (Annot e t)
lemma_annot_many e e' t (AddStep _e e1 s_ee1 _e' p_e1e') = p_et_e't
  where
    s_et_e1t  = EAnn e e1 s_ee1 t
    p_e1t_e't = lemma_annot_many e1 e' t p_e1e'
    p_et_e't  = AddStep (Annot e t) (Annot e1 t) s_et_e1t (Annot e' t) p_e1t_e't

--------------------------------------------------------------------------
----- | Basic LEMMAS of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------

{-@ lem_value_stuck :: e:Expr -> e':Expr -> ProofOf(Step e e') -> { pf:_ | not (isValue e) } @-}
lem_value_stuck :: Expr -> Expr -> Step -> Proof
lem_value_stuck e  e' (EPrim _ _)      
    = case e of 
        (App _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EApp1 e1 e1' p_e1_e1' e2)  
    = case e of 
        (App _e1 _e2)    -> lem_value_stuck e1 e1' p_e1_e1'
        (_)              -> impossible ""
lem_value_stuck e  e' (EApp2 e2 e2' p_e2_e2' v1)
    = case e of 
        (App _e2 _v1)    -> lem_value_stuck e2 e2' p_e2_e2'
        (_)              -> impossible ""
lem_value_stuck e  e' (EAppAbs _ _)  
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
lem_value_stuck e  e' (EAppTAbs _ _ _)  
    = case e of 
        (AppT _ _)   -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELet _ _ _ _) 
    = case e of 
        (Let _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ELetV _ _)    
    = case e of 
        (Let _ _)    -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnn _ _ _ _)   
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (EAnnV _ _)      
    = case e of 
        (Annot _ _)  -> ()
        (_)          -> impossible ""
lem_value_stuck e  e' (ESwitch _ _ _ _)   
    = case e of 
        (Switch _ _)  -> ()
        (_)           -> impossible ""
lem_value_stuck e  e' (ESwitchV _ _)      
    = case e of 
        (Switch _ _)  -> ()
        (_)           -> impossible ""

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
lem_sem_det e e1 (EAppAbs e' v) e2 pf_e_e2
    = case pf_e_e2 of 
        (EPrim {})               -> impossible ""
        (EApp1 f f' p_f_f' _)    -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EApp2 f f' p_f_f' _)    -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppAbs _e' _v)         -> ()
        (_)                      -> impossible ""
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
lem_sem_det e e1 (EAppTAbs k e' t) e2 pf_e_e2
    = case pf_e_e2 of
        (EPrim _ _)              -> impossible ""
        (EAppT f f' p_f_f' _)    -> impossible ("by lem" ? lem_value_stuck f f' p_f_f')
        (EAppTAbs _k _e' _t)     -> ()
lem_sem_det e e1 (ELet e_x e_x' p_ex_ex' e1') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet _ e_x'' p_ex_ex'' _) -> () ? lem_sem_det e_x e_x' p_ex_ex' e_x'' p_ex_ex''
        (ELetV _ _)                -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (_)                        -> impossible ""
lem_sem_det e e1 (ELetV v e') e2 pf_e_e2
    = case pf_e_e2 of 
        (ELet e_x e_x' p_ex_ex' _) -> impossible ("by" ? lem_value_stuck e_x e_x' p_ex_ex')
        (ELetV _ _)                -> ()
        (_)                        -> impossible ""
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
lem_sem_det e e1 (ESwitch e' e1' p_e_e1' as) e2 pf_e_e2
    = case pf_e_e2 of
        (ESwitch _e' e2' p_e_e2' _as) -> () ? lem_sem_det e' e1' p_e_e1' e2' p_e_e2'
        (ESwitchV {})                 -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (_)                           -> impossible ""
lem_sem_det e e1 (ESwitchV dv as) e2 pf_e_e2
    = case pf_e_e2 of 
        (ESwitch e' e1' p_e_e1' _as)   -> impossible ("by lem" ? lem_value_stuck e' e1' p_e_e1')
        (ESwitchV _dv _as)             -> ()
        (_)                            -> impossible "" 

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
