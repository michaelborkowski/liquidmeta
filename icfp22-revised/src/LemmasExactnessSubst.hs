{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"   @-}
{-@ LIQUID "--short-names" @-}

module LemmasExactnessSubst where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof,(?))
import qualified Data.Set as S

import Basics
import LocalClosure
import Strengthenings
import Semantics
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness
import BasicPropsWellFormedness
import SystemFLemmasWeaken
import SystemFLemmasSubstitution
import Typing
import PrimitivesWFType
import LemmasWeakenWF
import LemmasWellFormedness
import SubstitutionLemmaWF
import LemmasTyping
import LemmasSubtyping

  -- We need to show "equivalence" between eqlPred and eqlPred' because 
  --   eqlPred doesn't commute well with subFTV

{-@ reflect eqlPred' @-}  
{-@ eqlPred' :: { t:Type | isTRefn t } -> e:Expr -> p':Expr @-}
eqlPred' :: Type -> Expr -> Expr
eqlPred' (TRefn b ps) e = App (App (AppT (Prim Eql) (TRefn b ps)) (BV 0)) e

{-@ lem_open_at_eqlPred' :: y:Vname -> b:Basic -> ps:Preds 
        -> { e:Expr | isLC e } -> { pf:_ | open_at 0 y (eqlPred' (TRefn b ps) e)
                             == App (App (AppT (Prim Eql) (TRefn b (openP_at 1 y ps))) (FV y)) e } @-}
lem_open_at_eqlPred' ::  Vname -> Basic -> Preds -> Expr -> Proof
lem_open_at_eqlPred' y b ps e = () ? lem_open_at_lc_at   0 y 0 0 e
                                   ? toProof (unbind y (Prim Eql) === Prim Eql)
                                   ? toProof (unbind y (BV 0) === FV y)

{-@ lem_eqlPred_sub :: g:Env -> b:Basic ->  ps:Preds  -> qs:Preds 
      -> { e:Expr | isLC e }
      -> { pf:Subtype | propOf pf == Subtype g (TRefn b (PCons (eqlPred  (TRefn b ps) e) qs))
                                               (TRefn b (PCons (eqlPred' (TRefn b ps) e) qs)) } @-} 
lem_eqlPred_sub :: Env -> Basic -> Preds -> Preds -> Expr -> Subtype
lem_eqlPred_sub g b ps qs e = SBase g b (PCons (eqlPred  (TRefn b ps) e) qs) 
                                        (PCons (eqlPred' (TRefn b ps) e) qs) nms mk_imp_eqlqs_eql'qs
  where
    {-@ mk_imp_eqlqs_eql'qs :: { y:Vname | NotElem y nms }
          -> ProofOf(Implies (Cons y (TRefn b PEmpty) g) 
                             (unbindP y (PCons (eqlPred  (TRefn b ps) e) qs))
                             (unbindP y (PCons (eqlPred' (TRefn b ps) e) qs)) ) @-}
    mk_imp_eqlqs_eql'qs y = IStren y b qs g (unbindP y (PCons (eqlPred  (TRefn b ps) e) PEmpty))
                                            (unbindP y (PCons (eqlPred' (TRefn b ps) e) PEmpty)) (mk_imp_eql_eql' y)
                                   ? lem_strengthen_one (unbind y (eqlPred  (TRefn b ps) e)) (unbindP y qs)
                                   ? lem_strengthen_one (unbind y (eqlPred' (TRefn b ps) e)) (unbindP y qs)
    {-@ mk_imp_eql_eql' :: { y:Vname | NotElem y nms }
          -> ProofOf(Implies (Cons y (TRefn b qs) g) 
                             (unbindP y (PCons (eqlPred  (TRefn b ps) e) PEmpty))
                             (unbindP y (PCons (eqlPred' (TRefn b ps) e) PEmpty)) ) @-}
    mk_imp_eql_eql' y = IEqlSub (Cons y (TRefn b qs) g) b y e (openP_at 1 y ps) 
                                ? lem_open_at_eqlPred  y b (openP_at 1 y ps) e
                                ? lem_open_at_eqlPred' y b (openP_at 1 y ps) e   
                                ? toProof ( unbindP y PEmpty === PEmpty )
                                ? toProof ( eqlPred (TRefn b ps) e === eqlPred (TRefn b PEmpty) e )
    nms = unionEnv [] g

{-@ lem_self_push :: g:Env -> a:Vname -> ps:Preds -> b:Basic -> qs:Preds -> z:Vname
      -> { pf:Subtype | propOf pf == 
                   Subtype g (self (tsubFTV a (TRefn b qs) (TRefn (FTV a) ps)) (FV z) Base)
                             (tsubFTV a (TRefn b qs) (self (TRefn (FTV a) ps)  (FV z) Base)) } @-}
lem_self_push :: Env -> Vname -> Preds -> Basic -> Preds -> Vname -> Subtype
lem_self_push g a ps b qs z = lem_eqlPred_sub g b qs (strengthen (psubFTV a (TRefn b qs) ps) qs) (FV z)

{-@ lem_self_subst_tv_sub :: g:Env -> a:Vname -> { t_a:UserType | isLCT t_a } -> { t':Type | isLCT t' }
        -> z:Vname -> k':Kind -> ProofOf(WFType g (tsubFTV a t_a t') k')
        -> ProofOf(HasFType (erase_env g) (FV z) (erase (tsubFTV a t_a t')))
        -> { pf_sub:Subtype | propOf pf_sub == Subtype g (self (tsubFTV a t_a t') (FV z) k') 
                                                         (tsubFTV a t_a (self t' (FV z) k')) } 
         / [tdepth t'] @-}
lem_self_subst_tv_sub :: Env -> Vname -> Type -> Type -> Vname -> Kind -> WFType 
                             -> HasFType -> Subtype
lem_self_subst_tv_sub g a t_a (TRefn b ps)     z Base p_g_t'ta p_z_t'ta = case b of
  (FTV a') | a == a' -> case t_a of                    -- TODO: unused is p_g_t'ta
    (TRefn b' qs)  -> lem_self_push g a ps b' qs z
    (TFunc t1 t2)  -> impossible ("by" ? lem_wf_tfunc_star g t1 t2 (p_g_t'ta
                                       ? toProof ( tsubFTV a (TFunc t1 t2) (TRefn (FTV a) ps)
                                               === push (psubFTV a t_a ps) (TFunc t1 t2) 
                                               === TFunc t1 t2)))
    (TPoly k1 t1)  -> impossible ("by" ? lem_wf_tpoly_star g k1 t1 (p_g_t'ta
                                       ? toProof ( tsubFTV a (TPoly k1 t1) (TRefn (FTV a) ps)
                                               === push (psubFTV a t_a ps) (TPoly k1 t1)
                                               === TPoly k1 t1)))
  _                -> lem_sub_refl g (TRefn b (PCons eqlz (psubFTV a t_a ps))) Base (p_g_selft'ta
                             ? toProof ( eqlPred (TRefn b (psubFTV a t_a ps)) (FV z) === eqlz )
                             ? toProof ( tsubFTV a t_a (TRefn b (PCons eqlz ps))
                                     === TRefn b (psubFTV a t_a (PCons eqlz ps))
                                     === TRefn b (PCons (subFTV a t_a eqlz) (psubFTV a t_a ps))
                                       ? lem_tsubFTV_eqlPred a t_a b ps (FV z)
                                     === TRefn b (PCons eqlz (psubFTV a t_a ps)) )  )
      where
        p_g_selft'ta = lem_selfify_wf g (tsubFTV a t_a (TRefn b ps)) Base p_g_t'ta (FV z) p_z_t'ta
        eqlz = eqlPred (TRefn b ps) (FV z) 
lem_self_subst_tv_sub g a t_a (TFunc   t_z t1) z Base p_g_t'ta _
  = impossible ("by" ? lem_wf_tfunc_star g (tsubFTV a t_a t_z) (tsubFTV a t_a t1) p_g_t'ta)
lem_self_subst_tv_sub g a t_a (TExists t_z t1) z Base p_g_t'ta p_z_t'ta 
  = case lem_wfexis_for_wf_texists g (tsubFTV a t_a t_z) (tsubFTV a t_a t1) Base p_g_t'ta of
      (WFExis _ _ k_z p_g_tzta _ _ nms mk_p_yg_t1ta)
        -> lem_subtype_in_exists g (tsubFTV a t_a t_z) 
                                 (self (tsubFTV a t_a t1) (FV z) Base)
                                 (tsubFTV a t_a (self t1 (FV z) Base)  ? lc_proof) 
                                 k_z p_g_tzta nms' mk_p_self_t1ta_sub
                 where
                   lc_proof = lem_islct_at_tsubFTV 0 0 a t_a t_z
                            ? lem_self_islct_at    1               t1 (FV z) Base
                            ? lem_islct_at_tsubFTV 1 0 a t_a (self t1 (FV z) Base)
                   {-@ mk_p_self_t1ta_sub :: { y:Vname | NotElem y nms' } 
                         -> { pf:Subtype | propOf pf == 
                                 Subtype (Cons y (tsubFTV a t_a t_z) g)
                                         (unbindT y (self (tsubFTV a t_a t1) (FV z) Base)) 
                                         (unbindT y (tsubFTV a t_a (self t1 (FV z) Base))) } @-}
                   mk_p_self_t1ta_sub :: Vname -> Subtype
                   mk_p_self_t1ta_sub y = lem_self_subst_tv_sub (Cons y (tsubFTV a t_a t_z) g) a t_a 
                                            (unbindT y t1 ? lem_islct_at_before_openT_at 0 0 y t1) 
                                            z Base (mk_p_yg_t1ta y 
                                               ? lem_commute_tsubFTV_unbindT a t_a y t1)
                                            p_yg_z_t1ta
                                        ? lem_unbindT_self y (tsubFTV a t_a t1) (FV z) Base
                                        ? lem_unbindT_self y t1 (FV z) Base
                                        ? lem_commute_tsubFTV_unbindT a t_a y (self t1 (FV z) Base)
                     where
                       p_yg_z_t1ta      = lem_weaken_ftyp (erase_env g) FEmpty (FV z) 
                                            (erase (tsubFTV a t_a (unbindT y t1)) ? ftyp_pf)
                                            p_z_t'ta y (erase (tsubFTV a t_a t_z))
                       ftyp_pf          = lem_erase_tsubFTV a t_a (unbindT y t1)
                                        ? lem_erase_tsubFTV a t_a (TExists t_z t1)
                   nms'                 = a:(unionEnv nms g)  
lem_self_subst_tv_sub g a t_a (TPoly   k1 t1)  z Base p_g_t'ta _
  = impossible ("by" ? lem_wf_tpoly_star g k1 (tsubFTV a t_a t1) p_g_t'ta)
lem_self_subst_tv_sub g a t_a t'               z Star p_g_t'ta _
  = lem_sub_refl g (tsubFTV a t_a t') Star p_g_t'ta
