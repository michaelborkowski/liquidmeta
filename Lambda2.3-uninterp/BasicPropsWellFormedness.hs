{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicPropsWellFormedness where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import LocalClosure
import SystemFWellFormedness
import SystemFTyping
import BasicPropsSubstitution
import BasicPropsEnvironments
import WellFormedness

{-@ reflect foo21 @-}
foo21 :: a -> Maybe a
foo21 x = Just x

{-@ lem_btv_not_wf :: g:Env -> a:Vname -> ps:Preds -> k:Kind
                        -> ProofOf(WFType g (TRefn (BTV a) ps) k) -> { pf:_ | false } @-}
lem_btv_not_wf :: Env -> Vname -> Preds -> Kind -> WFType -> Proof
lem_btv_not_wf g a ps k (WFBase {}) = ()
lem_btv_not_wf g a ps k (WFRefn _ _ pf_g_b _ _ _) 
  = () ? lem_btv_not_wf g a PEmpty Base pf_g_b
lem_btv_not_wf g a ps k (WFVar1 {}) = ()
lem_btv_not_wf g a ps k (WFVar2 {}) = ()
lem_btv_not_wf g a ps k (WFVar3 {}) = ()
lem_btv_not_wf g a ps k (WFFunc {}) = ()
lem_btv_not_wf g a ps k (WFExis {}) = ()
lem_btv_not_wf g a ps k (WFPoly {}) = ()
lem_btv_not_wf g a ps k (WFKind _ _ pf_g_t_base) 
  = () ? lem_btv_not_wf g a ps Base pf_g_t_base

{-

{-@ lem_wf_refn_kind :: g:Env -> a:Vname -> z:RVname -> p:Pred -> k:Kind 
       -> ProofOf(WFType g (TRefn (FTV a) z p) k)
       -> { pf:_ | k == Star || kind_for_tv a g == Base } @-}
lem_wf_refn_kind :: Env -> Vname -> RVname -> Expr -> Kind -> WFType -> Proof
lem_wf_refn_kind g a z p k p_g_a = case k of 
  Base -> case p_g_a of
    (WFRefn _ _ _ tt' p'_g_a _ _ _) -> lem_wf_ftv_kind g  a tt' k p'_g_a
    (WFVar1 {})                 -> ()
    (WFVar2 g' _ _ _ p_g'_a _ _)  -> lem_wf_ftv_kind g' a p k p_g'_a
    (WFVar3 g' _ _ _ p_g'_a _ _)  -> lem_wf_ftv_kind g' a p k p_g'_a
  Star -> ()
-}

{-@ lem_wf_ftv_kind :: g:Env -> a:Vname -> k:Kind -> ProofOf(WFType g (TRefn (FTV a) PEmpty) k)
       -> { pf:_ | k == Star || kind_for_tv a g == Base } @-}
lem_wf_ftv_kind :: Env -> Vname -> Kind -> WFType -> Proof
lem_wf_ftv_kind g a k p_g_a = case k of 
  Base -> case p_g_a of
    (WFRefn _ _ p'_g_a _ _ _)  -> lem_wf_ftv_kind g  a k p'_g_a
    (WFVar1 {})                -> ()
    (WFVar2 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kind g' a k p_g'_a
    (WFVar3 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kind g' a k p_g'_a
  Star -> ()

{-@ lem_kind_for_tv ::  g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:Vname | not (in_env a g) && not (in_env a g') } -> k_a:Kind
        -> { pf:_ | kind_for_tv a (concatE (ConsT a k_a g) g') == k_a } @-} 
lem_kind_for_tv :: Env -> Env -> Vname -> Kind -> Proof
lem_kind_for_tv g Empty            a k_a = ()
lem_kind_for_tv g (Cons  x t_x g') a k_a = () ? lem_kind_for_tv g g' a k_a
lem_kind_for_tv g (ConsT a' k' g') a k_a = () ? lem_kind_for_tv g g' a k_a

{-@ lem_wf_ftv_kindF :: g:FEnv -> a:Vname -> k:Kind -> ProofOf(WFFT g (FTBasic (FTV a)) k)
       -> { pf:_ | k == Star || kind_for_tvF a g == Base } @-}
lem_wf_ftv_kindF :: FEnv -> Vname -> Kind -> WFFT -> Proof
lem_wf_ftv_kindF g a k p_g_a = case k of 
  Base -> case p_g_a of
    (WFFTBasic _ _)             -> ()
    (WFFTFV1 {})                -> ()
    (WFFTFV2 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kindF g' a k p_g'_a
    (WFFTFV3 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kindF g' a k p_g'_a
  Star -> ()

{-@ lem_kind_for_tvF :: g:FEnv -> { g':FEnv | Set_emp (Set_cap (bindsF g) (bindsF g')) } 
        -> { a:Vname | not (in_envF a g) && not (in_envF a g') } -> k_a:Kind
        -> { pf:_ | kind_for_tvF a (concatF (FConsT a k_a g) g') == k_a } @-} 
lem_kind_for_tvF :: FEnv -> FEnv -> Vname -> Kind -> Proof
lem_kind_for_tvF g FEmpty            a k_a = ()
lem_kind_for_tvF g (FCons  x t_x g') a k_a = () ? lem_kind_for_tvF g g' a k_a
lem_kind_for_tvF g (FConsT a' k' g') a k_a = () ? lem_kind_for_tvF g g' a k_a

{-
{-@ lem_ftyp_trivial_for_wf_trefn :: g:Env -> b:Basic -> x:RVname -> p:Pred -> k:Kind
        -> { p_g_t : WFType | propOf p_g_t  == WFType g (TRefn b x p) k }
        -> (Pred, WFType)<{\tt p_g_tt -> isTrivial tt && propOf p_g_tt == WFType g (TRefn b Z tt) k}> @-}
lem_ftyp_trivial_for_wf_trefn :: Env -> Basic -> RVname -> Expr -> Kind -> WFType -> (Expr, WFType)
lem_ftyp_trivial_for_wf_trefn g b x p k p_g_t@(WFBase _g _b tt) = (tt, p_g_t)
lem_ftyp_trivial_for_wf_trefn g b x p k p_g_t@(WFRefn _ _ _ tt p_g_tt _p y pf_yg_p_bl)    
      = (tt, p_g_tt)
lem_ftyp_trivial_for_wf_trefn g b x p k p_g_t@(WFVar1 g' a tt _k) = (tt, p_g_t)
lem_ftyp_trivial_for_wf_trefn g b x p k p_g_t@(WFVar2 _ _ tt _ p_g_a _ _) = (tt, p_g_t)
lem_ftyp_trivial_for_wf_trefn g b x p k p_g_t@(WFVar3 _ _ tt _ p_g_a _ _) = (tt, p_g_t)
lem_ftyp_trivial_for_wf_trefn g b x p k (WFKind _g _t p_g_t_base) 
      = (tt, WFKind g (TRefn b Z tt) p_g_tt)
          where
            (tt, p_g_tt) = lem_ftyp_trivial_for_wf_trefn g b x p Base p_g_t_base

{-@ lem_ftyp_for_wf_trefn :: g:Env -> b:Basic -> x:RVname -> p:Pred -> k:Kind
        -> { p_g_t : WFType | propOf p_g_t  == WFType g (TRefn b x p) k }
        -> (Vname,HasFType)<{\y pf_p_bl -> not (in_env y g) && not (Set_mem y (fv p)) && 
                                                               not (Set_mem y (ftv p)) &&
              propOf pf_p_bl == HasFType (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) (FTBasic TBool)}> @-}
lem_ftyp_for_wf_trefn :: Env -> Basic -> RVname -> Expr -> Kind -> WFType -> (Vname,HasFType)
lem_ftyp_for_wf_trefn g b x p k p_g_t@(WFBase _g _b tt) = (y, pf_yg_p_bl)
      where
        y          = fresh_var g
        g'         = FCons y (FTBasic b) (erase_env g)
        pf_yg_p_bl = makeHasFType g' (tt ? lem_trivial_nodefns  tt
                                         ? lem_trivial_check g' tt) (FTBasic TBool)
                                  ? lem_trivial_nofv tt
                                  ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)
lem_ftyp_for_wf_trefn g b x p k p_g_t@(WFRefn _ _ _ _ _ _p y pf_yg_p_bl)    
      = (y, pf_yg_p_bl)
lem_ftyp_for_wf_trefn g b x p k p_g_t@(WFVar1 g' a tt _k) = (y, pf_yg_p_bl)

      where
        y          = fresh_var g
        g'         = FCons y (FTBasic (FTV a)) (erase_env g)
        pf_yg_p_bl = makeHasFType g' (tt ? lem_trivial_nodefns  tt
                                         ? lem_trivial_check g' tt) (FTBasic TBool)
                                  ? lem_trivial_nofv tt
                                  ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)
lem_ftyp_for_wf_trefn g b x p k p_g_t@(WFVar2 _ _ tt _ p_g_a _ _) = (y, pf_yg_p_bl)
      where
        y          = fresh_var g
        g'         = FCons y (FTBasic b) (erase_env g)
        pf_yg_p_bl = makeHasFType g' (tt ? lem_trivial_nodefns  tt
                                         ? lem_trivial_check g' tt) (FTBasic TBool)
                                  ? lem_trivial_nofv tt
                                  ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)
lem_ftyp_for_wf_trefn g b x p k p_g_t@(WFVar3 _ _ tt _ p_g_a _ _) = (y, pf_yg_p_bl)
      where
        y          = fresh_var g
        g'         = FCons y (FTBasic b) (erase_env g)
        pf_yg_p_bl = makeHasFType g' (tt ? lem_trivial_nodefns  tt
                                         ? lem_trivial_check g' tt) (FTBasic TBool)
                                  ? lem_trivial_nofv tt
                                  ? lem_subBV_notin 0 (FV y) (tt ? lem_trivial_nobv tt)
lem_ftyp_for_wf_trefn g b x p k (WFKind _g _t p_g_t_base) 
      = lem_ftyp_for_wf_trefn g b x p Base p_g_t_base
-}

-- These lemmas allow us to directly invert the Well Formedness Judgments of certain types 
--     by allowing us to bypass the possibility of WFKind
{-@ lem_wffunc_for_wf_tfunc :: g:Env -> t_x:Type -> t:Type -> k:Kind 
        -> { p_g_txt : WFType | propOf p_g_txt  == WFType g (TFunc t_x t) k }
        -> { p_g_txt': WFType | propOf p_g_txt' == WFType g (TFunc t_x t) Star && isWFFunc p_g_txt' } @-}
lem_wffunc_for_wf_tfunc :: Env  -> Type -> Type -> Kind -> WFType -> WFType
lem_wffunc_for_wf_tfunc g t_x t k p_g_txt@(WFFunc {})           = case k of 
  Base -> impossible ("by lemma" ? lem_wf_tfunc_star g t_x t p_g_txt)
  Star -> p_g_txt
lem_wffunc_for_wf_tfunc g t_x t k (WFKind _g _ext p_g_txt_base) 
  = impossible ("by lemma" ? lem_wf_tfunc_star g t_x t p_g_txt_base)

{-@ lem_wf_tfunc_star :: g:Env -> t_x:Type -> t:Type
        -> ProofOf(WFType g (TFunc t_x t) Base) -> { pf:_ | false } @-}
lem_wf_tfunc_star :: Env ->  Type -> Type -> WFType -> Proof
lem_wf_tfunc_star g t_x t (WFBase {}) = ()
lem_wf_tfunc_star g t_x t (WFRefn {}) = ()
lem_wf_tfunc_star g t_x t (WFVar1 {}) = ()
lem_wf_tfunc_star g t_x t (WFVar2 {}) = ()
lem_wf_tfunc_star g t_x t (WFVar3 {}) = ()
lem_wf_tfunc_star g t_x t (WFFunc {}) = ()
lem_wf_tfunc_star g t_x t (WFExis {}) = ()
lem_wf_tfunc_star g t_x t (WFPoly {}) = ()
lem_wf_tfunc_star g t_x t (WFKind _g txt p_g_txt_base) = ()

{-
-- Given G |-w \exists x:t_x. t : k, we can produce a proof tree ending in WFExis
{-@ lem_wfexis_for_wf_texists :: g:Env -> x:Vname -> t_x:Type -> t:Type -> k:Kind
        -> { p_g_ex_t : WFType | propOf p_g_ex_t  == WFType g (TExists x t_x t) k }
        -> { p_g_ex_t': WFType | propOf p_g_ex_t' == WFType g (TExists x t_x t) k && isWFExis p_g_ex_t' } @-}
lem_wfexis_for_wf_texists :: Env -> Vname -> Type -> Type -> Kind -> WFType -> WFType
lem_wfexis_for_wf_texists g x t_x t k p_g_ex_t@(WFExis {})           = p_g_ex_t
lem_wfexis_for_wf_texists g x t_x t k (WFKind _g _ext p_g_ex_t_base) = p_g_ex_t_star
  where
    (WFExis _ _ _ k_x p_g_tx _ k_t y p_yg_t_kt) = p_g_ex_t_base
    {-@ p_yg_t_star :: { pf:WFType | propOf pf == WFType (Cons y t_x g) (unbindT x y t) Star } @-}
    p_yg_t_star = case k_t of 
      Base -> WFKind (Cons y t_x g) (unbindT x y t) p_yg_t_kt
      Star -> p_yg_t_kt
    p_g_ex_t_star = WFExis g x t_x k_x p_g_tx t Star y p_yg_t_star
-}
{-@ lem_wfpoly_for_wf_tpoly :: g:Env -> k:Kind -> t:Type 
      -> { p_g_at : WFType | propOf p_g_at  == WFType g (TPoly k t) Star }
      -> { p_g_at': WFType | propOf p_g_at' == WFType g (TPoly k t) Star && isWFPoly p_g_at' } @-}
lem_wfpoly_for_wf_tpoly :: Env -> Kind -> Type -> WFType -> WFType
lem_wfpoly_for_wf_tpoly g k t p_g_at@(WFPoly {})           = p_g_at
lem_wfpoly_for_wf_tpoly g k t (WFKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_tpoly_star g k t p_g_at_base)

{-@ lem_wf_tpoly_star :: g:Env -> k:Kind -> t:Type
        -> ProofOf(WFType g (TPoly k t) Base) -> { pf:_ | false } @-}
lem_wf_tpoly_star :: Env -> Kind -> Type -> WFType -> Proof
lem_wf_tpoly_star g k t (WFBase {}) = ()
lem_wf_tpoly_star g k t (WFRefn {}) = ()
lem_wf_tpoly_star g k t (WFVar1 {}) = ()
lem_wf_tpoly_star g k t (WFVar2 {}) = ()
lem_wf_tpoly_star g k t (WFVar3 {}) = ()
lem_wf_tpoly_star g k t (WFFunc {}) = ()
lem_wf_tpoly_star g k t (WFExis {}) = ()
lem_wf_tpoly_star g k t (WFPoly {}) = ()
lem_wf_tpoly_star g k t (WFKind {}) = ()

{-
{-@ lem_wf_usertype_base_trefn :: g:Env -> t_a:UserType -> ProofOf(WFType g t_a Base)
        -> { pf:_ | isTRefn t_a } @-}
lem_wf_usertype_base_trefn :: Env -> Type -> WFType -> Proof
lem_wf_usertype_base_trefn g t_a (WFBase {}) = ()
lem_wf_usertype_base_trefn g t_a (WFRefn {}) = ()
lem_wf_usertype_base_trefn g t_a (WFVar1 {}) = ()
lem_wf_usertype_base_trefn g t_a (WFVar2 {}) = ()
lem_wf_usertype_base_trefn g t_a (WFVar3 {}) = ()
lem_wf_usertype_base_trefn g t_a (WFFunc {}) = impossible ""
lem_wf_usertype_base_trefn g t_a (WFExis {}) = impossible ""
lem_wf_usertype_base_trefn g t_a (WFPoly {}) = impossible ""
lem_wf_usertype_base_trefn g t_a (WFKind {}) = impossible ""

{-@ lem_strengthen_tv_bound_in :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> a:Vname -> k:Kind -> { x:Vname | not (in_env x g) && not (in_env x g') } 
        -> { t_x:Type | tv_bound_in a k (concatE (Cons x t_x g) g') } 
        -> { pf:_ | tv_bound_in a k (concatE g g') } @-}
lem_strengthen_tv_bound_in :: Env -> Env -> Vname -> Kind -> Vname -> Type -> Proof
lem_strengthen_tv_bound_in g Empty            a k x t_x = ()
lem_strengthen_tv_bound_in g (Cons z t_z g')  a k x t_x 
              = () ? lem_strengthen_tv_bound_in g g' a k x t_x
lem_strengthen_tv_bound_in g (ConsT a' k' g') a k x t_x 
  | a == a'   = ()
  | otherwise = () ? lem_strengthen_tv_bound_in g g' a k x t_x

{-@ lem_strengthen_tv_tv_bound_in :: g:Env -> { g':Env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> a:Vname -> k:Kind -> { a':Vname | not (in_env a' g) && not (in_env a' g') && not (a == a')} 
        -> { k':Kind | tv_bound_in a k (concatE (ConsT a' k' g) g') } 
        -> { pf:_ | tv_bound_in a k (concatE g g') } @-}
lem_strengthen_tv_tv_bound_in :: Env -> Env -> Vname -> Kind -> Vname -> Kind -> Proof
lem_strengthen_tv_tv_bound_in g Empty            a k a' k' = ()
lem_strengthen_tv_tv_bound_in g (Cons z t_z g')  a k a' k' 
              = () ? lem_strengthen_tv_tv_bound_in g g' a k a' k'
lem_strengthen_tv_tv_bound_in g (ConsT a1 k1 g') a k a' k' 
  | a == a1   = ()
  | otherwise = () ? lem_strengthen_tv_tv_bound_in g g' a k a' k'

{-@ lem_kindfortv_tvboundin :: g:Env -> { a:Vname | Set_mem a (tvbinds g) } -> { k:Kind | kind_for_tv a g == k}
        -> { pf:_ | tv_bound_in a k g } @-}
lem_kindfortv_tvboundin :: Env -> Vname -> Kind -> Proof
lem_kindfortv_tvboundin Empty           a k = impossible ""
lem_kindfortv_tvboundin (Cons x t_x g)  a k 
  | a == x    = impossible ""
  | otherwise = () ? lem_kindfortv_tvboundin g a k
lem_kindfortv_tvboundin (ConsT a' k' g) a k
  | a == a'   = ()
  | otherwise = () ? lem_kindfortv_tvboundin g a k
-}
 -- SYSTEM F VERSIONS

{-@ lem_wfftfunc_for_wf_ftfunc :: g:FEnv -> t_x:FType -> t:FType -> k:Kind 
        -> { p_g_txt : WFFT | propOf p_g_txt  == WFFT g (FTFunc t_x t) k }
        -> { p_g_txt': WFFT | propOf p_g_txt' == WFFT g (FTFunc t_x t) Star && isWFFTFunc p_g_txt' } @-}
lem_wfftfunc_for_wf_ftfunc :: FEnv -> FType -> FType -> Kind -> WFFT -> WFFT
lem_wfftfunc_for_wf_ftfunc g t_x t k p_g_txt@(WFFTFunc {})           = case k of 
  Star -> p_g_txt
lem_wfftfunc_for_wf_ftfunc g t_x t k (WFFTKind _g _ext p_g_txt_base) 
  = impossible ("by lemma" ? lem_wf_ftfunc_star g t_x t p_g_txt_base)

{-@ lem_wf_ftfunc_star :: g:FEnv -> t_x:FType -> t:FType
        -> ProofOf(WFFT g (FTFunc t_x t) Base) -> { pf:_ | false } @-}
lem_wf_ftfunc_star :: FEnv -> FType -> FType -> WFFT -> Proof
lem_wf_ftfunc_star g t_x t (WFFTBasic {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFV1 {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFV2 {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFV3 {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFunc {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTPoly {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTKind _g txt p_g_txt_base) = ()

{-@ lem_wfftpoly_for_wf_ftpoly :: g:FEnv -> k:Kind -> t:FType 
        -> { p_g_at : WFFT | propOf p_g_at  == WFFT g (FTPoly k t) Star }
        -> { p_g_at': WFFT | propOf p_g_at' == WFFT g (FTPoly k t) Star && isWFFTPoly p_g_at' } @-}
lem_wfftpoly_for_wf_ftpoly :: FEnv -> Kind -> FType -> WFFT -> WFFT
lem_wfftpoly_for_wf_ftpoly g k t p_g_at@(WFFTPoly {})           = p_g_at
lem_wfftpoly_for_wf_ftpoly g k t (WFFTKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_ftpoly_star g k t p_g_at_base)

{-@ lem_wf_ftpoly_star :: g:FEnv -> k:Kind -> t:FType
        -> ProofOf(WFFT g (FTPoly k t) Base) -> { pf:_ | false } @-}
lem_wf_ftpoly_star :: FEnv -> Kind -> FType -> WFFT -> Proof
lem_wf_ftpoly_star g k t (WFFTBasic {}) = ()
lem_wf_ftpoly_star g k t (WFFTFV1 {}) = ()
lem_wf_ftpoly_star g k t (WFFTFV2 {}) = ()
lem_wf_ftpoly_star g k t (WFFTFV3 {}) = ()
lem_wf_ftpoly_star g k t (WFFTFunc {}) = ()
lem_wf_ftpoly_star g k t (WFFTPoly {}) = ()
lem_wf_ftpoly_star g k t (WFFTKind {}) = ()

------------------------------------------------------------------------------------------
-- | LEMMAS relating REFINEMENT ERASURE and WELL FORMEDNESS notions
------------------------------------------------------------------------------------------

{-@ lem_strengthen_wfft :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType 
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> t:FType -> k:Kind -> ProofOf(WFFT (concatF (FCons x t_x g) g') t k) 
        -> ProofOf(WFFT (concatF g g') t k) / [ftsize t, fenvsize g', ksize k] @-}
lem_strengthen_wfft :: FEnv -> Vname -> FType -> FEnv -> FType -> Kind -> WFFT -> WFFT
lem_strengthen_wfft g x t_x g' _ _ (WFFTBasic _ b) = WFFTBasic (concatF g g') b
lem_strengthen_wfft g x t_x g' _ _ (WFFTFV1 _ a k) 
  = case g' of 
      (FEmpty)            -> impossible ""
      (FCons z t_z g'')   -> impossible ""
      (FConsT _ _ g'')    -> WFFTFV1 (concatF g g'')
                                     (a ? lem_binds_cons_concatF g g'' x t_x) k 
lem_strengthen_wfft g x t_x g' _ _ (WFFTFV2 _ a k p_g_a y t) 
  = case g' of
      (FEmpty)            -> p_g_a
      (FCons z t_z g'')   -> WFFTFV2 (concatF g g'') a k 
                               (lem_strengthen_wfft g x t_x g'' (FTBasic (FTV a)) k p_g_a) 
                               (y ? lem_binds_cons_concatF g g'' x t_x) t
      (FConsT a' k' g'')  -> impossible ""
lem_strengthen_wfft g x t_x g' _ _ (WFFTFV3 _ a k p_g_a a' k') 
  = case g' of
      (FEmpty)            -> impossible ""
      (FCons z t_z g'')   -> impossible ""
      (FConsT a' k' g'')  -> WFFTFV3 (concatF g g'') a k
                               (lem_strengthen_wfft g x t_x g'' (FTBasic (FTV a)) k p_g_a) 
                               (a' ? lem_binds_cons_concatF g g'' x t_x) k'
lem_strengthen_wfft g x t_x g' _ _ (WFFTFunc _ t1 k1 p_xg_t1 t2 k2 p_xg_t2)
  = WFFTFunc (concatF g g') t1 k1 (lem_strengthen_wfft g x t_x g' t1 k1 p_xg_t1)
                            t2 k2 (lem_strengthen_wfft g x t_x g' t2 k2 p_xg_t2)
lem_strengthen_wfft g x t_x g' _ _ (WFFTPoly _ k t k_t nms mk_pf_a'g'xg_t)
  = WFFTPoly (concatF g g') k t k_t nms' mk_pf_a'g'g_t
      where
        {-@ mk_pf_a'g'g_t :: { a:Vname | NotElem a nms' } 
                                 -> ProofOf(WFFT (FConsT a k (concatF g g')) (unbindFT a t) k_t) @-}
        mk_pf_a'g'g_t a' = lem_strengthen_wfft g x t_x 
                                               (FConsT (a' ? lem_in_env_concatF g g' a') k g')
                                               (unbindFT a' t) k_t (mk_pf_a'g'xg_t a') 
        nms' = x:(unionFEnv nms (concatF g g'))
lem_strengthen_wfft g x t_x g' _ _ (WFFTKind _ t pf_t_base)
  = WFFTKind (concatF g g') t (lem_strengthen_wfft g x t_x g' t Base pf_t_base)

{-@ lem_erase_wftype :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
        -> ProofOf(WFFT (erase_env g) (erase t) k) / [tsize t, envsize g, ksize k] @-}
lem_erase_wftype :: Env -> Type -> Kind -> WFType -> WFFT
lem_erase_wftype _ _ _ (WFBase g b)                = WFFTBasic (erase_env g) b
lem_erase_wftype _ t k pf_g_t@(WFRefn g b pf_g_b p nms mk_pf_yg_p)  
  = case b of
      (FTV a)  -> lem_erase_wftype g (TRefn (FTV a) PEmpty) Base pf_g_b
      (BTV a)  -> impossible ("by lemma" ? lem_btv_not_wf g a p k pf_g_t)
      TBool    -> WFFTBasic (erase_env g) TBool
      TInt     -> WFFTBasic (erase_env g) TInt
lem_erase_wftype _ t _ (WFVar1 g a k)              = WFFTFV1 (erase_env g) a k
lem_erase_wftype _ t _ (WFVar2 g a k pf_g_a y t_y)
  = WFFTFV2 (erase_env g) a k (lem_erase_wftype g (TRefn (FTV a) PEmpty) k pf_g_a) y (erase t_y)
lem_erase_wftype _ t _ (WFVar3 g a k pf_g_a a' k')
  = WFFTFV3 (erase_env g) a k (lem_erase_wftype g (TRefn (FTV a) PEmpty) k pf_g_a) a' k'
lem_erase_wftype _ _ _ (WFFunc g t_x k_x pf_g_tx t k nms mk_pf_yg_t)
  = WFFTFunc (erase_env g) (erase t_x) k_x (lem_erase_wftype g t_x k_x pf_g_tx)
                           (erase t) k pf_erase_g_t
      where
        y             = fresh_var nms g
        pf_erase_yg_t = lem_erase_wftype (Cons y t_x g) (unbindT y t) k (mk_pf_yg_t y) 
        pf_erase_g_t  = lem_strengthen_wfft (erase_env g) y (erase t_x) FEmpty
                                            (erase t) k pf_erase_yg_t
lem_erase_wftype _ _ _ (WFExis g t_x k_x p_g_tx t k nms mk_pf_yg_t)
  = lem_strengthen_wfft (erase_env g) y (erase t_x) FEmpty (erase t) k pf_erase_yg_t
      where
        y             = fresh_var nms g
        pf_erase_yg_t = lem_erase_wftype (Cons y t_x g) (unbindT y t) k (mk_pf_yg_t y)
lem_erase_wftype _ _ _ (WFPoly g k t k_t nms mk_pf_ag_t)
  = WFFTPoly (erase_env g) k (erase t) k_t nms' mk_pf_ag_ert
      where 
        {-@ mk_pf_ag_ert :: { a:Vname | NotElem a nms' }
              -> ProofOf(WFFT (FConsT a k (erase_env g)) (unbindFT a (erase t)) k_t) @-}
        mk_pf_ag_ert a = lem_erase_wftype (ConsT a k g) (unbind_tvT a t ? lem_erase_unbind_tvT a t)
                                          k_t (mk_pf_ag_t a)
        nms'           = unionFEnv nms (erase_env g)
lem_erase_wftype _ _ _ (WFKind g t pf_t_base) 
  = WFFTKind (erase_env g) (erase t) (lem_erase_wftype g t Base pf_t_base)

{-@ lem_erase_env_wfenv :: g:Env -> ProofOf(WFEnv g) -> ProofOf(WFFE (erase_env g)) @-}
lem_erase_env_wfenv :: Env -> WFEnv -> WFFE
lem_erase_env_wfenv _ WFEEmpty                         = WFFEmpty
lem_erase_env_wfenv _ (WFEBind g pf_g_wf x t k p_g_t) 
  = WFFBind (erase_env g) (lem_erase_env_wfenv g pf_g_wf) 
            x (erase t) k (lem_erase_wftype g t k p_g_t)
lem_erase_env_wfenv _ (WFEBindT g pf_g_wf a k)
  = WFFBindT (erase_env g) (lem_erase_env_wfenv g pf_g_wf) a k
        
-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to FREE VARIABLES and WELL FORMEDNESS judgments
-------------------------------------------------------------------------------------------

{-@ lem_free_bound_in_env :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> { x:Vname | not (in_env x g) }
            -> { pf:_ | not (Set_mem x (free t)) && not (Set_mem x (freeTV t)) } 
             / [tsize t, envsize g, ksize k] @-}
lem_free_bound_in_env :: Env -> Type -> Kind -> WFType -> Vname -> Proof
lem_free_bound_in_env g t k (WFBase _ _) x = case t of 
  (TRefn b _) -> case b of
    TBool -> () 
    TInt  -> ()
lem_free_bound_in_env g t k (WFRefn _g b p_g_b p nms mk_p_z_p_bl) x = case t of
  (TRefn _ _) -> () ? lem_fvp_bound_in_fenv (FCons z (FTBasic b) (erase_env g))
                                            (unbindP z p) (mk_p_z_p_bl z) x
                    ? lem_free_bound_in_env g (TRefn b PEmpty) Base p_g_b x
      where
        z = fresh_var_excludingF nms (erase_env g) x 
lem_free_bound_in_env g t k (WFVar1 g' a  _k) x = case t of
  (TRefn b _) -> case b of
    (FTV _) -> () 
lem_free_bound_in_env g t k (WFVar2 g' a _k p_a_k y t') x = case t of 
  (TRefn b _) -> case b of
    (FTV _) -> () ? lem_free_bound_in_env g' t k p_a_k x
lem_free_bound_in_env g t k (WFVar3 g' a _k p_a_k a' k') x = case t of
  (TRefn b _) -> case b of
    (FTV _) -> () ? lem_free_bound_in_env g' t k p_a_k x
lem_free_bound_in_env g t k (WFFunc _g t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) x = case t of
  (TFunc _ _) -> () ? lem_free_bound_in_env g t_y k_y p_ty_wf x
                    ? lem_free_bound_in_env (Cons y t_y g) (unbindT y t') k' (mk_p_y_t'_wf y) x
      where
        y = fresh_var_excluding nms g x 
lem_free_bound_in_env g t k (WFExis _g t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) x = case t of
  (TExists _ _) -> () ? lem_free_bound_in_env g t_y k_y p_ty_wf x
                      ? lem_free_bound_in_env (Cons y t_y g) (unbindT y t') k' (mk_p_y_t'_wf y) x
      where
        y = fresh_var_excluding nms g x 
lem_free_bound_in_env g t k (WFPoly _g k' t' k_t' nms mk_p_a_t'_kt') x = case t of
  (TPoly _ _) -> () ? lem_free_bound_in_env (ConsT a k' g) (unbind_tvT a t') k_t' (mk_p_a_t'_kt' a) x
      where
        a = fresh_var_excluding nms g x 
lem_free_bound_in_env g t k (WFKind _g _t p_t_B) x = () ? lem_free_bound_in_env g t Base p_t_B x

{-@ lem_free_subset_binds :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
            -> { pf:_ | Set_sub (free t) (binds g) && Set_sub (freeTV t) (binds g) &&
                        Set_sub (free t) (vbinds g) && Set_sub (freeTV t) (tvbinds g) } 
             / [tsize t, envsize g, ksize k] @-}
lem_free_subset_binds :: Env -> Type -> Kind -> WFType -> Proof
lem_free_subset_binds g t k (WFBase _ _) = case t of
  (TRefn b _) -> case b of
    TBool -> () 
    TInt  -> () 
lem_free_subset_binds g t k p_t_k@(WFRefn _g b p_g_b p nms mk_p_z_p_bl) = case t of
  (TRefn _ _) -> () ? lem_fvp_subset_bindsF (FCons z (FTBasic b) (erase_env g))
                                            (unbindP z p) (mk_p_z_p_bl z)
                    ? lem_free_subset_binds g (TRefn b PEmpty) Base p_g_b
                    ? lem_free_bound_in_env g t k p_t_k z
    where
      z = fresh_varF nms (erase_env g)
lem_free_subset_binds g t k (WFVar1 g' a _k) = case t of
  (TRefn b _) -> case b of
    (FTV _) -> () 
lem_free_subset_binds g t k (WFVar2 g' a _k p_a_k y t')  
  = () ? lem_free_subset_binds g' t k p_a_k
lem_free_subset_binds g t k (WFVar3 g' a _k p_a_k a' k') 
  = () ? lem_free_subset_binds g' t k p_a_k
lem_free_subset_binds g t k p_t_k@(WFFunc _g t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) = case t of
  (TFunc _ _) -> () ? lem_free_subset_binds g t_y k_y p_ty_wf
                    ? lem_free_subset_binds (Cons y t_y g) (unbindT y t') k' (mk_p_y_t'_wf y)
                    ? lem_free_bound_in_env g t k p_t_k y
    where
      y = fresh_var nms g
lem_free_subset_binds g t k p_t_k@(WFExis _g t_y k_y p_ty_wf t' k' nms mk_p_y_t'_wf) = case t of
  (TExists _ _) -> () ? lem_free_subset_binds g t_y k_y p_ty_wf
                      ? lem_free_subset_binds (Cons y t_y g) (unbindT y t') k' (mk_p_y_t'_wf y)
                      ? lem_free_bound_in_env g t k p_t_k y
    where
      y = fresh_var nms g
lem_free_subset_binds g t k p_t_k@(WFPoly _g k' t' k_t' nms mk_p_a_t'_kt') = case t of
  (TPoly _ _) -> () ? lem_free_subset_binds (ConsT a k' g) (unbind_tvT a t') 
                                            k_t' (mk_p_a_t'_kt' a)
                    ? lem_free_bound_in_env g t k p_t_k a
    where
      a = fresh_var nms g
lem_free_subset_binds g t k (WFKind _g _t p_t_B) = () ? lem_free_subset_binds g t Base p_t_B

{-@ lem_closed_free_empty :: t:Type -> k:Kind -> ProofOf(WFType Empty t k)
            -> { pf:_ | Set_emp (free t) && Set_emp (freeTV t) } @-}
lem_closed_free_empty :: Type -> Kind -> WFType -> Proof
lem_closed_free_empty t k p_emp_t = lem_free_subset_binds Empty t k p_emp_t

-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to the abscence of dangling BOUND VARIABLES without a binder
-------------------------------------------------------------------------------------------

{-@ lem_ftyp_islc :: g:FEnv -> e:Expr -> t:FType -> ProofOf(HasFType g e t)
                              -> { pf:_ | isLC e } / [esize e] @-}
lem_ftyp_islc :: FEnv -> Expr ->  FType -> HasFType -> Proof 
lem_ftyp_islc g e t (FTBC _g b)    = case e of
  (Bc _) -> ()
lem_ftyp_islc g e t (FTIC _g n)    = case e of
  (Ic _) -> ()
lem_ftyp_islc g e t (FTVar1 _ x _) = case e of 
  (FV _) -> ()
lem_ftyp_islc g e t (FTVar2 g' x _ p_x_t y s) = case e of
  (FV _) -> () -- ? lem_ftyp_islc g' e t p_x_t
lem_ftyp_islc g e t (FTVar3 g' x _ p_x_t a k) = case e of
  (FV _) -> () -- ? lem_ftyp_islc g' e t p_x_t
lem_ftyp_islc g e t (FTPrm _g c)   = case e of
  (Prim _) -> ()
lem_ftyp_islc g e t (FTAbs _g t_x k_x p_g_tx e' t' nms mk_p_yg_e'_t') = case e of
  (Lambda _) -> () ? lem_islc_at_after_open_at 0 0 y 
                         (e' ? lem_ftyp_islc (FCons y t_x g) (unbind y e') t' (mk_p_yg_e'_t' y))
    where
      y = fresh_varF nms g
lem_ftyp_islc g e t (FTApp _g e' t_x t' p_e'_txt' e_x p_ex_tx) = case e of
  (App _ _) -> () ? lem_ftyp_islc g e' (FTFunc t_x t') p_e'_txt'
                  ? lem_ftyp_islc g e_x t_x p_ex_tx
lem_ftyp_islc g e t (FTAbsT _g k e' t' nms mk_p_e'_t') = case e of 
  (LambdaT {}) -> () ? lem_islc_at_after_open_tv_at 0 0 a
                           (e' ? lem_ftyp_islc (FConsT a k g) (unbind_tv a e') (unbindFT a t') (mk_p_e'_t' a))
    where
      a = fresh_varF nms g
lem_ftyp_islc g e t (FTAppT _g e' k t' p_e_at' liqt p_g_ert) = case e of
  (AppT _ _)   -> () ? lem_ftyp_islc g e' (FTPoly k t') p_e_at'
lem_ftyp_islc g e t (FTLet _g e_x t_x p_ex_tx e' t' nms mk_p_yg_e'_t') = case e of
  (Let {}) -> () ? lem_ftyp_islc g e_x t_x p_ex_tx
                 ? lem_islc_at_after_open_at 0 0 y 
                       (e' ? lem_ftyp_islc (FCons y t_x g) (unbind y e') t' (mk_p_yg_e'_t' y))
    where
      y = fresh_varF nms g
lem_ftyp_islc g e t (FTAnn _g e' _t t1 p_e'_t) = case e of
  (Annot _ _)  -> () ? lem_ftyp_islc g e' t p_e'_t

{-@ lem_pftyp_islcp :: g:FEnv -> ps:Preds -> ProofOf(PHasFType g ps)
                              -> { pf:_ | isLCP ps && isLCP_at 0 0 ps } / [predsize ps] @-}
lem_pftyp_islcp :: FEnv -> Preds -> PHasFType -> Proof 
lem_pftyp_islcp g ps (PFTEmp  _)                         = ()
lem_pftyp_islcp g ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl) 
    = () ? lem_pftyp_islcp g ps' pf_ps'_bl
         ? lem_ftyp_islc   g p (FTBasic TBool) pf_p_bl

{-@ lem_wfft_islcft :: g:FEnv -> t:FType -> k:Kind -> { p_g_t:WFFT | propOf p_g_t == WFFT g t k }
                              -> { pf:Proof | isLCFT t } / [ftsize t, ksize k] @-}
lem_wfft_islcft :: FEnv -> FType -> Kind -> WFFT -> Proof
lem_wfft_islcft g t k (WFFTBasic _g b) = () 
lem_wfft_islcft g t k (WFFTFV1 _ a _k) = ()
lem_wfft_islcft g t k (WFFTFV2 _ a _k _ _ _) = ()
lem_wfft_islcft g t k (WFFTFV3 _ a _k _ _ _) = ()
lem_wfft_islcft g t k (WFFTFunc _g t_x k_x p_g_tx t' k' p_g_t') 
  = () ? lem_wfft_islcft g t_x k_x p_g_tx 
       ? lem_wfft_islcft g t'  k'  p_g_t' 
lem_wfft_islcft g t k (WFFTPoly _g k_a t' k_t' nms mk_p_ag_t') 
  = () ? lem_islcft_at_after_openFT_at 0 a  
             (t' ? lem_wfft_islcft (FConsT a k_a g) (unbindFT a t') k_t' (mk_p_ag_t' a))
      where
        a = fresh_varF nms g
lem_wfft_islcft g t k (WFFTKind _g _t p_g_t_base) 
  = () ? lem_wfft_islcft g t Base p_g_t_base 

{-@ lem_wftype_islct :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k }
        -> { pf:Proof | isLCT t }  / [tsize t, ksize k] @-}
lem_wftype_islct :: Env -> Type -> Kind -> WFType -> Proof
lem_wftype_islct g t k (WFBase _g b)  = case t of 
  (TRefn _ _) -> {-() ?-} toProof ( isLCP_at 1 0 PEmpty {-=== True-} ) 
lem_wftype_islct g t k p_g_t@(WFRefn _g b p_g_b p nms mk_p_yg_p_bl) = case t of
  (TRefn _ _) -> case b of 
    (BTV a) -> impossible ("by lemma" ? lem_btv_not_wf g a p k p_g_t)
    _       -> () ? lem_islcp_at_after_unbindP 0 y
                        (p ? lem_pftyp_islcp (FCons y (FTBasic b) (erase_env g)) 
                                             (unbindP y p) (mk_p_yg_p_bl y))
      where
        y = fresh_varF nms (erase_env g)
lem_wftype_islct g t k p_g_t@(WFVar1 _ a _k) = case t of 
  (TRefn (FTV _) _) -> {-() ?-} toProof ( isLCP_at 1 0 PEmpty {-=== True-} ) 
lem_wftype_islct g t k p_g_t@(WFVar2 _ a _k _ _ _) = case t of 
  (TRefn (FTV _) _) -> {-() ?-} toProof ( isLCP_at 1 0 PEmpty {-=== True-} ) 
lem_wftype_islct g t k p_g_t@(WFVar3 _ a _k _ _ _) = case t of
  (TRefn (FTV _) _) -> {-() ?-} toProof ( isLCP_at 1 0 PEmpty {-=== True-} ) 
lem_wftype_islct g t k (WFFunc _g t_x k_x p_g_tx t' k' nms mk_p_yg_t')  = case t of
  (TFunc _ _) -> () 
        ? lem_wftype_islct g t_x k_x p_g_tx  
        ? lem_islct_at_after_openT_at 0 0 y 
              (t' ? lem_wftype_islct (Cons y t_x g) (unbindT y t') k' (mk_p_yg_t' y))
    where
      y = fresh_var nms g
lem_wftype_islct g t k (WFExis _g t_x k_x p_g_tx t' k' nms mk_p_yg_t')  = case t of
  (TExists _ _) -> () 
        ? lem_wftype_islct g t_x k_x p_g_tx 
        ? lem_islct_at_after_openT_at 0 0 y 
              (t' ? lem_wftype_islct (Cons y t_x g) (unbindT y t') k' (mk_p_yg_t' y))
    where
      y = fresh_var nms g
lem_wftype_islct g t k (WFPoly _g k_a t' k_t' nms mk_p_ag_t') = case t of 
  (TPoly _ _) -> () ? lem_islct_at_after_open_tvT_at 0 0 a
                        (t' ? lem_wftype_islct (ConsT a k_a g) (unbind_tvT a t') k_t' (mk_p_ag_t' a))
    where
      a = fresh_var nms g
lem_wftype_islct g t k (WFKind _g _t p_g_t_base) 
  = () ? lem_wftype_islct g t Base p_g_t_base 
