{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsCSubst where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics
import SystemFWellFormedness
import SystemFTyping
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments
import BasicPropsWellFormedness
import SystemFLemmasWellFormedness
import SystemFLemmasFTyping
import SystemFLemmasSubstitution
import Typing

{-@ reflect foo26 @-}   
foo26 x = Just x 
foo26 :: a -> Maybe a 


-- | Substitution Properties

-- with bound type vars, these are only equiv up to alhpa-renaming bound variables
{-@ lem_erase_subtype :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2)
               -> { pf:_ | normalize (erase t1) == normalize (erase t2) } @-}
lem_erase_subtype :: Env -> Type -> Type -> Subtype -> Proof
lem_erase_subtype g t1 t2 (SBase _g x1 b p1 x2 p2 y _) = ()
lem_erase_subtype g t1 t2 (SFunc _g x1 s1 x2 s2 p_s2_s1 t1' t2' y p_t1'_t2')
    = undefined {-() ? lem_erase_subtype g s2 s1 p_s2_s1
         ? lem_erase_tsubBV x1 (FV y) t1' ? lem_erase_tsubBV x2 (FV y) t2'
         ? lem_erase_subtype (Cons y s2 g) (unbindT x1 y t1') (unbindT x2 y t2') p_t1'_t2'  -}
lem_erase_subtype g t1 t2 (SWitn _g v t_x p_v_tx _t1 x t' p_t1_t'v)
    = undefined {- toProof ( erase t1 ? lem_erase_subtype g t1 (tsubBV x v t') p_t1_t'v
            === erase (tsubBV x v t') ? lem_erase_tsubBV x v t'
            === erase t' === erase (TExists x t_x t') ) -}
lem_erase_subtype g t1 t2 (SBind _g x t_x t _t2 y p_t_t')
    = () ? lem_erase_subtype (Cons y t_x g) (unbindT x y t) t2 p_t_t'
         ? lem_erase_tsubBV x (FV y) t
lem_erase_subtype g t1 t2 (SPoly {}) 
    = undefined

{-@ lem_erase_th_sub :: g:Env -> t1:Type -> t2:Type -> ProofOf(Subtype g t1 t2) -> th:CSub 
        -> { pf:_ | normalize (erase (ctsubst th t1)) == normalize (erase (ctsubst th t2)) } @-}
lem_erase_th_sub :: Env -> Type -> Type -> Subtype -> CSub -> Proof
lem_erase_th_sub g t1 t2 p_t1_t2 th = toProof ( normalize (erase (ctsubst th t1))
                                              ? lem_erase_ctsubst th t1
                                            === normalize (erase t1) ? lem_erase_subtype g t1 t2 p_t1_t2
                                            === normalize (erase t2) ? lem_erase_ctsubst th t2
                                            === normalize (erase (ctsubst th t2)) ) 

-- | Closing Substitution Properties

{-@ lem_unroll_ctsubst_left :: th:CSub -> { x:Vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_emp (fv v_x) && Set_emp (ftv v_x) } ->  t:Type
        -> { pf:_ | ctsubst (CCons x v_x th) t == tsubFV x v_x (ctsubst th t) } @-}
lem_unroll_ctsubst_left :: CSub -> Vname -> Expr -> Type -> Proof
lem_unroll_ctsubst_left CEmpty           x v_x t = ()
lem_unroll_ctsubst_left (CCons y v_y th) x v_x t = () {-toProof ( ctsubst (CCons x v_x (CCons y v_y th)) t
                                                         === ctsubst (CCons y v_y th) (tsubFV x v_x t)
                                                         === ctsubst th (tsubFV y v_y (tsubFV x v_x t))-}
                                                           ? lem_subFV_notin x v_x v_y
                                                           ? toProof ( subFV x v_x v_y === v_y )
--                                                         === ctsubst th (tsubFV y (subFV x v_x v_y) (tsubFV x v_x t))
                                                           ? lem_commute_tsubFV y v_y x v_x t
{-                                                         === ctsubst th (tsubFV x v_x (tsubFV y v_y t))
                                                         === ctsubst (CCons x v_x th) (tsubFV y v_y t)-}
                                                           ? lem_unroll_ctsubst_left th x v_x (tsubFV y v_y t)
{-                                                         === tsubFV x v_x (ctsubst th (tsubFV y v_y t))
                                                         === tsubFV x v_x (ctsubst (CCons y v_y th) t) )-}
lem_unroll_ctsubst_left (CConsT a t_a th) x v_x t' 
  = undefined

{-@ lem_unroll_ctsubst_tv_left :: th:CSub -> { a:Vname | not (in_csubst a th) } 
        -> { t_a:Type | Set_emp (free t_a) && Set_emp (freeTV t_a) } ->  t:Type
        -> { pf:_ | ctsubst (CConsT a t_a th) t == tsubFTV a t_a (ctsubst th t) } @-}
lem_unroll_ctsubst_tv_left :: CSub -> Vname -> Type -> Type -> Proof
lem_unroll_ctsubst_tv_left CEmpty           a t_a t = ()
lem_unroll_ctsubst_tv_left (CCons y v_y th) a t_a t
  = undefined
lem_unroll_ctsubst_tv_left (CConsT a' t' th) a t_a t
  = undefined

{-@ lem_in_csubst_concatCS :: th:CSub -> { th':CSub | Set_emp (Set_cap (bindsC th) (bindsC th')) }   
      -> x:Vname -> {pf:_ | (in_csubst x (concatCS th th')) <=> ((in_csubst x th) || (in_csubst x th'))} @-} 
lem_in_csubst_concatCS :: CSub -> CSub -> Vname -> Proof
lem_in_csubst_concatCS th CEmpty          x = () 
lem_in_csubst_concatCS th (CCons y v th') x = () ? lem_in_csubst_concatCS th th' x 
lem_in_csubst_concatCS th (CConsT a t th') x = () ? lem_in_csubst_concatCS th th' x 

{-@ lem_binds_cons_concatCS :: th:CSub -> {  th':CSub | Set_emp (Set_cap (bindsC th) (bindsC th')) }
      -> { x:Vname | not (Set_mem x (bindsC th)) && not (Set_mem x (bindsC th')) } 
      -> { v_x:Value | Set_emp (fv v_x) && Set_emp (ftv v_x) }
      -> { pf:_ | Set_sub (bindsC (concatCS th th')) (bindsC (concatCS (CCons x v_x th) th')) &&
             bindsC (concatCS (CCons x v_x th) th') == Set_cup (Set_cup (bindsC th) (Set_sng x)) (bindsC th') } @-}
lem_binds_cons_concatCS :: CSub -> CSub -> Vname -> Expr -> Proof
lem_binds_cons_concatCS th CEmpty          x v_x = ()
lem_binds_cons_concatCS th (CCons y s th') x v_x = () ? lem_binds_cons_concatCS th th' x v_x
lem_binds_cons_concatCS th (CConsT a t th') x v_x = () ? lem_binds_cons_concatCS th th' x v_x
-- add a type var version of the above

  --- various distributive properties of csubst and ctsubst

{-@ lem_csubst_bc :: th:CSub -> b:Bool -> { pf:_ | csubst th (Bc b) == Bc b } @-}
lem_csubst_bc :: CSub -> Bool -> Proof
lem_csubst_bc (CEmpty)       b = ()
lem_csubst_bc (CCons x v th) b = () ? lem_csubst_bc th b
lem_csubst_bc (CConsT a t th) b = () ? lem_csubst_bc th b

{-@ lem_csubst_ic :: th:CSub -> n:Int -> { pf:_ | csubst th (Ic n) == Ic n } @-}
lem_csubst_ic :: CSub -> Int -> Proof
lem_csubst_ic (CEmpty)       n = ()
lem_csubst_ic (CCons x v th) n = () ? lem_csubst_ic th n
lem_csubst_ic (CConsT a t th) n = () ? lem_csubst_ic th n

{-@ lem_csubst_prim :: th:CSub -> c:Prim -> { pf:_ | csubst th (Prim c) == Prim c } @-}
lem_csubst_prim :: CSub -> Prim -> Proof
lem_csubst_prim (CEmpty)       c = ()
lem_csubst_prim (CCons x v th) c = () ? lem_csubst_prim th c
lem_csubst_prim (CConsT a t th) c = () ? lem_csubst_prim th c

{-@ lem_csubst_bv :: th:CSub -> y:Vname -> { pf:_ | csubst th (BV y) == BV y } @-}
lem_csubst_bv :: CSub -> Vname -> Proof
lem_csubst_bv (CEmpty)       y = ()
lem_csubst_bv (CCons x v th) y = () ? lem_csubst_bv th y
lem_csubst_bv (CConsT a t th) y = () ? lem_csubst_bv th y

{-@ lem_csubst_fv :: th:CSub -> { y:Vname | not (in_csubst y th) } -> { pf:_ | csubst th (FV y) == FV y } @-} 
lem_csubst_fv :: CSub -> Vname -> Proof
lem_csubst_fv (CEmpty)        y = ()
lem_csubst_fv (CCons x v th)  y = () ? lem_csubst_fv th y 
lem_csubst_fv (CConsT a t th) y = () ? lem_csubst_fv th y 

{-@ lem_csubst_lambda :: th:CSub -> x:Vname 
        -> e:Expr -> { pf:_ | csubst th (Lambda x e) == Lambda x (csubst th e) } @-}
lem_csubst_lambda :: CSub -> Vname -> Expr -> Proof
lem_csubst_lambda (CEmpty)        x e = ()
lem_csubst_lambda (CCons y v th)  x e = () ? lem_csubst_lambda th x (subFV y v e)
lem_csubst_lambda (CConsT a t th) x e = () ? lem_csubst_lambda th x (subFTV a t e)

{-@ lem_csubst_app :: th:CSub -> e:Expr -> e':Expr 
               -> { pf:_ | csubst th (App e e') == App (csubst th e) (csubst th e') } @-}
lem_csubst_app :: CSub -> Expr -> Expr -> Proof
lem_csubst_app (CEmpty)        e e' = ()
lem_csubst_app (CCons y v th)  e e' = () ? lem_csubst_app th (subFV y v e) (subFV y v e')
lem_csubst_app (CConsT a t th) e e' = () ? lem_csubst_app th (subFTV a t e) (subFTV a t e')

{-@ lem_csubst_let :: th:CSub -> x:Vname -> e_x:Expr -> e:Expr 
        -> { pf:_ | csubst th (Let x e_x e) == Let x (csubst th e_x) (csubst th e) } @-}
lem_csubst_let :: CSub -> Vname -> Expr -> Expr -> Proof
lem_csubst_let (CEmpty)       x e_x e = ()
lem_csubst_let (CCons y v th) x e_x e = () ? lem_csubst_let th x (subFV y v e_x) (subFV y v e)
lem_csubst_let (CConsT a t th) x e_x e = () ? lem_csubst_let th x (subFTV a t e_x) (subFTV a t e)

{-@ lem_csubst_annot :: th:CSub -> e:Expr
        -> t:Type -> { pf:_ | csubst th (Annot e t) == Annot (csubst th e) (ctsubst th t) } @-}
lem_csubst_annot :: CSub -> Expr -> Type -> Proof
lem_csubst_annot (CEmpty)       e t = ()
lem_csubst_annot (CCons y v th) e t = () ? lem_csubst_annot th (subFV y v e) (tsubFV y v t)
lem_csubst_annot (CConsT a t_a th) e t = () ? lem_csubst_annot th (subFTV a t_a e) (tsubFTV a t_a t)

{-@ lem_ctsubst_refn :: th:CSub -> b:Basic -> x:Vname -> p:Expr
               -> { pf:_ | ctsubst th (TRefn b x p) == TRefn b x (csubst th p) } @-}
lem_ctsubst_refn :: CSub -> Basic -> Vname -> Expr -> Proof
lem_ctsubst_refn (CEmpty)       b x p = ()
lem_ctsubst_refn (CCons y v th) b x p 
  = undefined {-toProof ( ctsubst (CCons y v th) (TRefn b x p)
                                              === ctsubst th (tsubFV y v (TRefn b x p))
                                              === ctsubst th (TRefn b x (subFV y v p))
                                                ? lem_ctsubst_refn th b x (subFV y v p)
                                              === TRefn b x (csubst th (subFV y v p)) 
                                              === TRefn b x (csubst (CCons y v th) p) )-}
lem_ctsubst_refn (CConsT a t_a th) b x p
  = undefined

{-@ lem_ctsubst_func :: th:CSub -> x:Vname -> t_x:Type -> t:Type
        -> { pf:_ | ctsubst th (TFunc x t_x t) == TFunc x (ctsubst th t_x) (ctsubst th t) } @-}  
lem_ctsubst_func :: CSub -> Vname -> Type -> Type -> Proof
lem_ctsubst_func (CEmpty)       x t_x t = ()
lem_ctsubst_func (CCons y v th) x t_x t 
    = () ? lem_ctsubst_func th x (tsubFV y v t_x) (tsubFV y v t) 
lem_ctsubst_func (CConsT a t_a th) x t_x t 
    = () ? lem_ctsubst_func th x (tsubFTV a t_a t_x) (tsubFTV a t_a t)

{-@ lem_ctsubst_exis :: th:CSub -> x:Vname -> t_x:Type -> t:Type
        -> {pf:_ | ctsubst th (TExists x t_x t) == TExists x (ctsubst th t_x) (ctsubst th t)} @-}  
lem_ctsubst_exis :: CSub -> Vname -> Type -> Type -> Proof
lem_ctsubst_exis (CEmpty)       x t_x t = ()
lem_ctsubst_exis (CCons y v th) x t_x t 
    = () ? lem_ctsubst_exis th x (tsubFV y v t_x) (tsubFV y v t) 
lem_ctsubst_exis (CConsT a t_a th) x t_x t 
    = undefined

{-@ lem_ctsubst_poly :: th:CSub -> a:Vname -> k:Kind -> t:Type
        -> { pf:_ | ctsubst th (TPoly a k t) == TPoly a k (ctsubst th t) } @-}  
lem_ctsubst_poly :: CSub -> Vname -> Kind -> Type -> Proof
lem_ctsubst_poly (CEmpty)           a k t = ()
lem_ctsubst_poly (CCons  y  v   th) a k t  
    = () ? lem_ctsubst_poly th a k (tsubFV y v t) 
lem_ctsubst_poly (CConsT a' t'  th) a k t 
    = () ? lem_ctsubst_poly th a k (tsubFTV a' t' t)


{-@ lem_ctsubst_self_refn :: th:CSub -> b:Basic -> z:Vname -> p:Pred -> x:Vname 
        -> { pf:_ | ctsubst th (self (TRefn b z p) x) == 
		        TRefn b z (App (App (Prim And) (csubst th p)) 
                                       (App (App (equals b) (BV z)) (csubst th (FV x)))) } @-}
lem_ctsubst_self_refn :: CSub -> Basic -> Vname -> Pred -> Vname -> Proof
lem_ctsubst_self_refn th b z p x  = undefined {-
          = () {-toProof ( ctsubst th (self (TRefn b z p) x)
                  === ctsubst th (TRefn b z (App (App (Prim And) p) (App (App (Prim (equals b)) (BV z)) (FV x))))-}
                    ? lem_ctsubst_refn th b z (selfify p b z x)
--                  === TRefn b z (csubst th (App (App (Prim And) p) (App (App (Prim (equals b)) (BV z)) (FV x))))
                    ? lem_csubst_app th (App (Prim And) p) (App (App (equals b) (BV z)) (FV x))
{-                  === TRefn b z (App (csubst th (App (Prim And) p)) 
                                     (csubst th (App (App (Prim (equals b)) (BV z)) (FV x))))-}
                    ? lem_csubst_app th (Prim And) p
                    ? lem_csubst_app th (App (equals b) (BV z)) (FV x)
{-                  === TRefn b z (App (App (csubst th (Prim And)) (csubst th p))
                                     (App (csubst th (App (Prim (equals b)) (BV z))) (csubst th (FV x))))-}
                    ? lem_csubst_prim th And 
                    ? lem_csubst_app th (equals b) (BV z) 
{-                  === TRefn b z (App (App (Prim And) (csubst th p))
                                     (App (App (csubst th (Prim (equals b))) (csubst th (BV z))) (csubst th (FV x))))-}
                    ? lem_csubst_appt --what should this be?
                    ? lem_csubst_prim th (equals b) -- break this out?
                    ? lem_csubst_bv th z
{-                  === TRefn b z (App (App (Prim And) (csubst th p))
                                     (App (App (Prim (equals b)) (BV z)) (csubst th (FV x)))) ) -}
-}

{-@ lem_ctsubst_self_refn_notin :: th:CSub -> b:Basic -> z:Vname -> p:Pred -> { x:Vname | not (in_csubst x th) }
        -> { pf:_ | ctsubst th (self (TRefn b z p) x) == self (ctsubst th (TRefn b z p)) x } @-}
lem_ctsubst_self_refn_notin :: CSub -> Basic -> Vname -> Pred -> Vname -> Proof
lem_ctsubst_self_refn_notin th b z p x 
          = ()--toProof ( ctsubst th (self (TRefn b z p) x) 
                    ? lem_ctsubst_self_refn th b z p x 
{-                  === TRefn b z (App (App (Prim And) (csubst th p))
                                (App (App (Prim (equals b)) (BV z)) (csubst th (FV x)))) -}
                    ? lem_csubst_fv th x
{-                  === TRefn b z (App (App (Prim And) (csubst th p)) 
                                (App (App (Prim (equals b)) (BV z)) (FV x))) 
                  === TRefn b z (selfify (csubst th p) b z x)
                  === self (TRefn b z (csubst th p)) x-}
                    ? lem_ctsubst_refn th b z p
--                  === self (ctsubst th (TRefn b z p)) x )

{-@ lem_ctsubst_self_notin :: th:CSub -> t:Type -> { x:Vname | not (in_csubst x th) }
        -> { pf:_ | ctsubst th (self t x) == self (ctsubst th t) x } @-}
lem_ctsubst_self_notin :: CSub -> Type -> Vname -> Proof
lem_ctsubst_self_notin th (TRefn b z p)      x = () ? lem_ctsubst_self_refn_notin th b z p x
lem_ctsubst_self_notin th (TFunc z t_z t')   x = () ? lem_ctsubst_func th z t_z t'
lem_ctsubst_self_notin th (TExists z t_z t') x = () ? lem_ctsubst_exis th z t_z (self t' x)
                                                    ? lem_ctsubst_self_notin th t' x
                                                    ? lem_ctsubst_exis th z t_z t'
--     ctsubst th (self (TExists z t_z t') x) === ctsubst th (TExists z t_z (self t' x))
lem_ctsubst_self_notin th (TPoly a k   t')   x = () ? lem_ctsubst_poly th a k   t' 


-- TODO: this. TODO: lem_ctsubst_fv
  --- Various properties of csubst/ctsubst and free/bound variables

{-@ lem_csubst_binds :: g:Env -> th:CSub -> ProofOf(DenotesEnv g th) 
        -> { pf:_ | binds g == bindsC th } @-}
lem_csubst_binds :: Env -> CSub -> DenotesEnv -> Proof
lem_csubst_binds g th DEmp                                            = ()
lem_csubst_binds g th (DExt g' th' den_g'_th' x t_x v_x den_th'tx_vx) 
    = () ? lem_csubst_binds g' th' den_g'_th'
lem_csubst_binds g th (DExtT {})
    = undefined

{-@ lem_csubst_nofv :: th:CSub -> { e:Expr | Set_emp (fv e) }
        -> { pf:_ | csubst th e == e } @-}
lem_csubst_nofv :: CSub -> Expr -> Proof
lem_csubst_nofv (CEmpty)       e = ()
lem_csubst_nofv (CCons x v th) e = () ? lem_csubst_nofv th e
                                      ? toProof ( subFV x v e === e )
lem_csubst_nofv (CConsT a t_a th) e
  = undefined

{-@ lem_ctsubst_nofree :: th:CSub -> { t:Type | Set_emp (free t) }
        -> { pf:_ | ctsubst th t == t } @-}
lem_ctsubst_nofree :: CSub -> Type -> Proof
lem_ctsubst_nofree (CEmpty)       t = ()
lem_ctsubst_nofree (CCons x v th) t = () ? lem_ctsubst_nofree th t
                                         ? toProof ( tsubFV x v t === t )
lem_ctsubst_nofree (CConsT a t_a th) t
  = undefined

{-{-@ lem_csubst_freeBV :: th:CSub -> e:Expr
        -> { pf:_ | freeBV (csubst th e) == freeBV e } @-}
lem_csubst_freeBV :: CSub -> Expr -> Proof
lem_csubst_freeBV (CEmpty)       e = ()
lem_csubst_freeBV (CCons x v th) e = () ? lem_csubst_freeBV th (subFV x v e)
                         ? toProof ( freeBV (subFV x v e) === freeBV e )

{-@ lem_ctsubst_tfreeBV :: th:CSub -> t:Type
        -> { pf:_ | tfreeBV (ctsubst th t) == tfreeBV t } @-}
lem_ctsubst_tfreeBV :: CSub -> Type -> Proof
lem_ctsubst_tfreeBV (CEmpty)       t = ()
lem_ctsubst_tfreeBV (CCons x v th) t = () ? lem_ctsubst_tfreeBV th (tsubFV x v t)
                         ? toProof ( tfreeBV (tsubFV x v t) === tfreeBV t )-}

-- was        -> { pf:_ | isValue (csubst th v) && Set_emp (freeBV (csubst th v)) } @-}
{-@ lem_csubst_value :: th:CSub -> v:Value  
        -> { pf:_ | isValue (csubst th v) } @-}
lem_csubst_value :: CSub -> Expr -> Proof
lem_csubst_value (CEmpty)         v = ()
lem_csubst_value (CCons y v_y th) v = () ? lem_csubst_value th (subFV y v_y v)
lem_csubst_value (CConsT a t_a th) v
  = undefined

{-@ lem_ctsubst_head_not_free :: x:Vname 
        -> { v_x:Value | Set_emp (fv v_x) && Set_emp (ftv v_x) &&
                         Set_emp (freeBV v_x) && Set_emp (freeBTV v_x) } 
        -> { th:CSub | not (Set_mem x (bindsC th)) }
        -> { t:Type | not (Set_mem x (free t)) } 
        -> { pf:_ | ctsubst (CCons x v_x th) t == ctsubst th t } @-}
lem_ctsubst_head_not_free :: Vname -> Expr -> CSub -> Type -> Proof
lem_ctsubst_head_not_free x v_x th t = toProof ( ctsubst (CCons x v_x th) t
                                             === ctsubst th (tsubFV x v_x t)
                                             === ctsubst th t )

  --- Commutative laws relating csubst/ctsubst and subBV/tsubBV 

{-@ lem_csubst_subBV :: x:Vname -> v:Value -> bt:FType 
           -> ProofOf(HasFType FEmpty v bt) -> th:CSub -> p:Expr
           -> { pf:_ | csubst th (subBV x v p) == subBV x v (csubst th p) } @-}
lem_csubst_subBV :: Vname -> Expr -> FType -> HasFType -> CSub -> Expr -> Proof
lem_csubst_subBV x v bt pf_v_b (CEmpty)         p = ()
lem_csubst_subBV x v bt pf_v_b (CCons y v_y th) p 
    = () ? lem_commute_subFV_subBV1 x v 
                   (y `withProof` lem_fv_bound_in_fenv FEmpty v bt pf_v_b y) v_y p
         ? lem_csubst_subBV x v bt pf_v_b th (subFV y v_y p)
lem_csubst_subBV x v bt pf_v_b (CConsT a t_a th) p
    = undefined

{-@ lem_ctsubst_tsubBV :: x:Vname -> v:Value -> bt:FType
           -> ProofOf(HasFType FEmpty v bt) -> th:CSub -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_tsubBV :: Vname -> Expr -> FType -> HasFType -> CSub -> Type -> Proof
lem_ctsubst_tsubBV x v bt pf_v_b (CEmpty)         t = ()
lem_ctsubst_tsubBV x v bt pf_v_b (CCons y v_y th) t 
    = () ? lem_commute_tsubFV_tsubBV1 x v 
                   (y `withProof` lem_fv_bound_in_fenv FEmpty v bt pf_v_b y) v_y t
         ? lem_ctsubst_tsubBV x v bt pf_v_b th (tsubFV y v_y t)
lem_ctsubst_tsubBV x v bt pf_v_b (CConsT a t_a th) t 
    = undefined

{-@ lem_csubst_and_unbind :: x:Vname -> y:Vname 
           -> v:Value -> bt:FType -> ProofOf(HasFType FEmpty v bt)
           -> { th:CSub | not (Set_mem y (bindsC th)) } -> { p:Expr | not (Set_mem y (fv p)) }
           -> { pf:_ | csubst (CCons y v th) (unbind x y p) == subBV x v (csubst th p) } @-}
lem_csubst_and_unbind :: Vname -> Vname -> Expr -> FType -> HasFType -> CSub -> Expr -> Proof
lem_csubst_and_unbind x y v b pf_v_b th p = () {-toProof ( 
       csubst (CCons y (v-}  ? lem_fv_subset_bindsF FEmpty v b pf_v_b{-) th) (unbind x y p) 
   === csubst th (subFV y v (unbind x y p))-}
     ? lem_subFV_unbind x y v p
--   === csubst th (subBV x v p)
     ? lem_csubst_subBV x v b pf_v_b th p
--   === subBV x v (csubst th p) )

{-@ lem_ctsubst_and_unbindT :: x:Vname -> y:Vname
           -> v:Value -> bt:FType -> ProofOf(HasFType FEmpty v bt)
           -> { th:CSub | not (Set_mem y (bindsC th)) } -> { t:Type | not (Set_mem y (free t)) }
           -> { pf:_ | ctsubst (CCons y v th) (unbindT x y t) == tsubBV x v (ctsubst th t) } @-}
lem_ctsubst_and_unbindT :: Vname -> Vname -> Expr -> FType -> HasFType 
           -> CSub -> Type -> Proof
lem_ctsubst_and_unbindT x y v bt pf_v_b th t = () {-toProof ( 
       ctsubst (CCons y (v-} ? lem_fv_subset_bindsF FEmpty v bt pf_v_b{-) th) (unbindT x y t)
   === ctsubst th (tsubFV y v (unbindT x y t))-}
     ? lem_tsubFV_unbindT x y v t
--   === ctsubst th (tsubBV x v t)
     ? lem_ctsubst_tsubBV x v bt pf_v_b th t
--   === tsubBV x v (ctsubst th t) )

{-@ lem_commute_csubst_subBV :: th:CSub -> x:Vname -> v:Value -> e:Expr
           -> { pf:_ | csubst th (subBV x v e) == subBV x (csubst th v) (csubst th e) } @-} 
lem_commute_csubst_subBV :: CSub -> Vname -> Expr -> Expr -> Proof
lem_commute_csubst_subBV (CEmpty)         x v e = () 
lem_commute_csubst_subBV (CCons y v_y th) x v e 
    = () ? lem_commute_subFV_subBV x v y v_y e
         ? lem_commute_csubst_subBV th x (subFV y v_y v) (subFV y v_y e)
lem_commute_csubst_subBV (CConsT a t_a th) x v e 
    = undefined

{-@ lem_commute_ctsubst_tsubBV :: th:CSub -> x:Vname -> v:Value -> t:Type
           -> { pf:_ | ctsubst th (tsubBV x v t) == tsubBV x (csubst th v) (ctsubst th t) } @-} 
lem_commute_ctsubst_tsubBV :: CSub -> Vname -> Expr -> Type -> Proof
lem_commute_ctsubst_tsubBV (CEmpty)         x v t = () 
lem_commute_ctsubst_tsubBV (CCons y v_y th) x v t 
    = () ? lem_commute_tsubFV_tsubBV x v y v_y t
         ? lem_commute_ctsubst_tsubBV th x (subFV y v_y v) (tsubFV y v_y t)
lem_commute_ctsubst_tsubBV (CConsT a t_a th) x v t 
    = undefined

{-@ lem_csubst_no_more_fv :: th:CSub -> { v_x:Value | Set_sub (fv v_x) (bindsC th) }
        -> { pf:_ | Set_emp (fv (csubst th v_x)) } @-}
lem_csubst_no_more_fv :: CSub -> Expr -> Proof
lem_csubst_no_more_fv CEmpty v_x           = ()
lem_csubst_no_more_fv (CCons y v_y th) v_x = () ? lem_csubst_no_more_fv th (subFV y v_y v_x)
lem_csubst_no_more_fv (CConsT a t_a th) v_x
    = undefined

{-@ lem_ctsubst_no_more_fv :: th:CSub -> { t:Type | Set_sub (free t) (bindsC th) }
        -> { pf:_ | Set_emp (free (ctsubst th t)) } @-}
lem_ctsubst_no_more_fv :: CSub -> Type -> Proof
lem_ctsubst_no_more_fv CEmpty           t = ()
lem_ctsubst_no_more_fv (CCons y v_y th) t = () ? lem_ctsubst_no_more_fv th (tsubFV y v_y t)
lem_ctsubst_no_more_fv (CConsT a t_a th) t 
    = undefined

{-@ lem_csubst_subFV :: th:CSub -> { x:Vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_sub (fv v_x) (bindsC th) } -> e:Expr
        -> { pf:_ | csubst th (subFV x v_x e) == csubst th (subFV x (csubst th v_x) e) } @-}
lem_csubst_subFV :: CSub -> Vname -> Expr -> Expr -> Proof
lem_csubst_subFV  CEmpty            x v_x e = ()
lem_csubst_subFV  (CCons y v_y th)  x v_x e 
  = undefined {- () ? toProof (-- case den_g_th of
  -- (DExt _ _ _ _ _ _ den_thty_vy) -> () ? toProof (
        csubst (CCons y v_y th) (subFV x (csubst (CCons y v_y th) v_x 
                                    ? lem_csubst_value (CCons y v_y th) v_x) e)-}
        ? lem_csubst_value (CCons y v_y th) v_x
--    === csubst th (subFV y v_y (subFV x (csubst (CCons y v_y th) v_x) e))
        ? lem_commute_subFV x (csubst (CCons y v_y th) v_x) y v_y e
        ? lem_subFV_value y v_y (csubst (CCons y v_y th) v_x)
--    === csubst th (subFV x (subFV y v_y (csubst (CCons y v_y th) v_x)) (subFV y v_y e))   
        ? lem_csubst_no_more_fv (CCons y v_y th) v_x
--    === csubst th (subFV x (csubst (CCons y v_y th) v_x) (subFV y v_y e))
        ? lem_csubst_value th (subFV y v_y v_x ? lem_subFV_value y v_y v_x)
--    === csubst th (subFV x (csubst th (subFV y v_y v_x)) (subFV y v_y e))
        ? lem_csubst_subFV th x (subFV y v_y v_x) (subFV y v_y e)
--    === csubst th (subFV x (subFV y v_y v_x) (subFV y v_y e))
        ? lem_commute_subFV x v_x y v_y e 
--    === csubst th (subFV y v_y (subFV x v_x e))
--    === csubst (CCons y v_y th) (subFV x v_x e) )
lem_csubst_subFV  (CConsT a t_a th) x v_x e
    = undefined
    
{-@ lem_ctsubst_tsubFV :: th:CSub -> { x:Vname | not (in_csubst x th) } 
        -> { v_x:Value | Set_sub (fv v_x) (bindsC th) } -> t:Type
        -> { pf:_ | ctsubst th (tsubFV x v_x t) == ctsubst th (tsubFV x (csubst th v_x) t) } @-}
lem_ctsubst_tsubFV :: CSub -> Vname -> Expr -> Type -> Proof
lem_ctsubst_tsubFV  CEmpty            x v_x t = ()
lem_ctsubst_tsubFV  (CCons y v_y th)  x v_x t 
  = undefined {-() ? toProof (-- case den_g_th of
  -- (DExt _ _ _ _ _ _ den_thty_vy) -> () ? toProof (
        ctsubst (CCons y v_y th) (tsubFV x (csubst (CCons y v_y th) v_x 
                                     ? lem_csubst_value (CCons y v_y th) v_x) t)-}
        ? lem_csubst_value (CCons y v_y th) v_x
--    === ctsubst th (tsubFV y v_y (tsubFV x (csubst (CCons y v_y th) v_x) t))
        ? lem_commute_tsubFV x (csubst (CCons y v_y th) v_x) y v_y t
        ? lem_subFV_value y v_y (csubst (CCons y v_y th) v_x)
--    === ctsubst th (tsubFV x (subFV y v_y (csubst (CCons y v_y th) v_x)) (tsubFV y v_y t))   
        ? lem_csubst_no_more_fv (CCons y v_y th) v_x
--    === ctsubst th (tsubFV x (csubst (CCons y v_y th) v_x) (tsubFV y v_y t))
        ? lem_csubst_value th (subFV y v_y v_x ? lem_subFV_value y v_y v_x)
--    === ctsubst th (tsubFV x (csubst th (subFV y v_y v_x)) (tsubFV y v_y t))
        ? lem_ctsubst_tsubFV th x (subFV y v_y v_x) (tsubFV y v_y t)
--    === ctsubst th (tsubFV x (subFV y v_y v_x) (tsubFV y v_y t))
        ? lem_commute_tsubFV x v_x y v_y t 
--    === ctsubst th (tsubFV y v_y (tsubFV x v_x t))
--    === ctsubst (CCons y v_y th) (tsubFV x v_x t) )
lem_ctsubst_tsubFV  (CConsT a t_a th) x v_x t 
    = undefined
   
{-@ lem_erase_ctsubst :: th:CSub -> t:Type 
               -> { pf:_ | erase (ctsubst th t) == erase t } @-}
lem_erase_ctsubst :: CSub -> Type -> Proof
lem_erase_ctsubst (CEmpty)       t = ()
lem_erase_ctsubst (CCons y v th) t = () {-toProof ( erase (ctsubst (CCons y v th) t)
                                           === erase (ctsubst th (tsubFV y v t))-}
                                             ? lem_erase_ctsubst th (tsubFV y v t)
{-                                           === erase (tsubFV y v t)-}
                                             ? lem_erase_tsubFV y v t
{-                                           === erase t )-}
lem_erase_ctsubst (CConsT a t_a th) t
    = undefined

  --- Closing Substitutions and Technical Operations



        -- -> { e:Expr | Set_sub (fv e) (bindsC th ) && ( x == y || not (Set_mem y (fv e))) }
{-@ lem_change_var_in_csubst :: th:CSub -> { x:Vname | v_in_csubst x th }
        -> { y:Vname  | y == x || not (in_csubst y th) }
        -> { e:Expr   | x == y || not (Set_mem y (fv e)) }
        -> { pf:Proof | csubst th e == csubst (change_varCS th x y) (subFV x (FV y) e) } @-}
lem_change_var_in_csubst :: CSub -> Vname -> Vname -> Expr -> Proof
lem_change_var_in_csubst (CCons z v_z th) x y e = case (x == z) of
  (True)  -> () {- toProof ( csubst (change_varCS (CCons z v_z th) x y) (subFV x (FV y) e)
                   === csubst (CCons y v_z th) (subFV x (FV y) e)
                   === csubst th (subFV y v_z (subFV x (FV y) e)) -}
                     ? lem_chain_subFV x y v_z e 
                {-   === csubst th (subFV x v_z e)	
                   === csubst (CCons z v_z th) e  ) -}
  (False) -> () {- toProof ( csubst (change_varCS (CCons z v_z th) x y) (subFV x (FV y) e)
                   === csubst (CCons z v_z (change_varCS th x y)) (subFV x (FV y) e)
                   === csubst (change_varCS th x y) (subFV z v_z (subFV x (FV y) e)) -}
                     ? lem_commute_subFV x (FV y) z v_z e
{-                   === csubst (change_varCS th x y) (subFV x (subFV z v_z (FV y)) (subFV z v_z e)) -}
                     ? lem_change_var_in_csubst th x y (subFV z v_z e) 
{-                   === csubst th (subFV z v_z e)
                   === csubst (CCons z v_z th) e )-}
lem_change_var_in_csubst (CConsT a t_a th) x y e
    = undefined

{-@ lem_change_tvar_in_csubst :: th:CSub -> { a:Vname | tv_in_csubst a th }
        -> { a':Vname | a == a' || not (in_csubst a' th) }
        -> { e:Expr   | a == a' || not (Set_mem a' (ftv e)) }
        -> { pf:Proof | csubst th e == csubst (change_tvarCS th a a') (chgFTV a a' e) } @-}
lem_change_tvar_in_csubst :: CSub -> Vname -> Vname -> Expr -> Proof
lem_change_tvar_in_csubst (CCons z v_z th) a a' e = undefined
lem_change_tvar_in_csubst (CConsT a1 t_a th) a a' e = undefined

        -- -> { t:Type | Set_sub (free t) (bindsC th ) && ( x == y || not (Set_mem y (free t))) }
{-@ lem_change_var_in_ctsubst :: th:CSub -> { x:Vname | v_in_csubst x th }
        -> { y:Vname  | y == x || not (in_csubst y th) }
        -> { t:Type   | x == y || not (Set_mem y (free t)) }
        -> { pf:Proof | ctsubst th t == ctsubst (change_varCS th x y) (tsubFV x (FV y) t) } @-}
lem_change_var_in_ctsubst :: CSub -> Vname -> Vname -> Type -> Proof
lem_change_var_in_ctsubst (CCons z v_z th) x y t = case (x == z) of
  (True)  -> () ? lem_chain_tsubFV x y v_z t 
  (False) -> () ? lem_commute_tsubFV x (FV y) z v_z t
                ? lem_change_var_in_ctsubst th x y (tsubFV z v_z t)
lem_change_var_in_ctsubst (CConsT a t_a th) x y t 
    = undefined

{-@ lem_change_tvar_in_ctsubst :: th:CSub -> { a:Vname | tv_in_csubst a th }
        -> { a':Vname | a == a' || not (in_csubst a' th) }
        -> { t:Type   | a == a' || not (Set_mem a' (freeTV t)) }
        -> { pf:Proof | ctsubst th t == ctsubst (change_tvarCS th a a') (tchgFTV a a' t) } @-}
lem_change_tvar_in_ctsubst :: CSub -> Vname -> Vname -> Type -> Proof
lem_change_tvar_in_ctsubst (CCons z v_z th) a a' t = undefined {-case (x == z) of
  (True)  -> () ? lem_chain_tsubFV x y v_z t 
  (False) -> () ? lem_commute_tsubFV x (FV y) z v_z t
                ? lem_change_var_in_ctsubst th x y (tsubFV z v_z t)-}
lem_change_tvar_in_ctsubst (CConsT a1 t_a th) a a' t = undefined

{-@ lem_change_var_back :: th:CSub -> { x:Vname | in_csubst x th }
        -> { y:Vname | (y == x || not (in_csubst y th)) } 
        -> { pf:Proof | change_varCS (change_varCS th x y) y x == th } @-}
lem_change_var_back :: CSub -> Vname -> Vname -> Proof
lem_change_var_back CEmpty           x y              = ()
lem_change_var_back (CCons z v_z th) x y | ( x == z ) = ()
                                         | otherwise  = () ? lem_change_var_back th x y
lem_change_var_back (CConsT a t_a th) x y
    = undefined

--        -> { e:Expr | Set_sub (fv e) (bindsC th) && not (Set_mem x (fv e)) }
{-@ lem_remove_csubst :: th:CSub -> { x:Vname | in_csubst x th}
        -> { e:Expr | not (Set_mem x (fv e)) }
        -> { pf:Proof | csubst th e == csubst (remove_fromCS th x) e } @-}
lem_remove_csubst :: CSub -> Vname -> Expr -> Proof
lem_remove_csubst (CCons z v_z th) x e = case ( x == z ) of
  (True)  -> () ? toProof ( csubst (remove_fromCS (CCons x v_z th) x) e
                   === csubst th e  
                   === csubst th (subFV x v_z e)
                   === csubst (CCons x v_z th) e)
  (False) -> () {- toProof ( csubst (remove_fromCS (CCons z v_z th) x) e
                   === csubst (CCons z v_z (remove_fromCS th x)) e-}
                     ? lem_remove_csubst th x (subFV z v_z e)
                {-   === csubst (CCons z v_z th) e )-}
lem_remove_csubst (CConsT a t_a th) x e 
    = undefined

{-@ lem_remove_ctsubst :: th:CSub -> { x:Vname | in_csubst x th}
        -> { t:Type | not (Set_mem x (free t)) }
        -> { pf:Proof | ctsubst th t == ctsubst (remove_fromCS th x) t } @-}
lem_remove_ctsubst :: CSub -> Vname -> Type -> Proof
lem_remove_ctsubst (CCons z v_z th) x t = case ( x == z ) of
  (True)  -> () ? toProof ( ctsubst (remove_fromCS (CCons x v_z th) x) t
                   === ctsubst th t  
                   === ctsubst th (tsubFV x v_z t)
                   === ctsubst (CCons x v_z th) t)
  (False) -> () {- toProof ( ctsubst (remove_fromCS (CCons z v_z th) x) t
                   === ctsubst (CCons z v_z (remove_fromCS th x)) t-}
                     ? lem_remove_ctsubst th x (tsubFV z v_z t)
                {-   === ctsubst (CCons z v_z th) t )-}
lem_remove_ctsubst (CConsT a t_a th) x t
    = undefined
