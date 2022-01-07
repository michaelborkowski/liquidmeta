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
import WellFormedness
import BasicPropsSubstitution
import BasicPropsEnvironments

{-@ reflect foo21 @-}
foo21 :: a -> Maybe a
foo21 x = Just x

{-

{-@ lem_btv_not_wf :: g:Env -> a:Vname -> x:RVname -> p:Pred -> k:Kind
                        -> ProofOf(WFType g (TRefn (BTV a) x p) k) -> { pf:_ | false } @-}
lem_btv_not_wf :: Env -> Vname -> RVname -> Expr -> Kind -> WFType -> Proof
lem_btv_not_wf g a x p k (WFBase {}) = ()
lem_btv_not_wf g a x p k (WFRefn _ _ _ tt pf_g_b _ _ _) 
  = () ? lem_btv_not_wf g a Z tt Base pf_g_b
lem_btv_not_wf g a x p k (WFVar1 {}) = ()
lem_btv_not_wf g a x p k (WFVar2 {}) = ()
lem_btv_not_wf g a x p k (WFVar3 {}) = ()
lem_btv_not_wf g a x p k (WFFunc {}) = ()
lem_btv_not_wf g a x p k (WFExis {}) = ()
lem_btv_not_wf g a x p k (WFPoly {}) = ()
lem_btv_not_wf g a x p k (WFKind _ _ pf_g_t_base) 
  = () ? lem_btv_not_wf g a x p Base pf_g_t_base

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

{-@ lem_wf_ftv_kind :: g:Env -> a:Vname -> { tt:Pred | isTrivial tt } -> k:Kind 
       -> ProofOf(WFType g (TRefn (FTV a) Z tt) k)
       -> { pf:_ | k == Star || kind_for_tv a g == Base } @-}
lem_wf_ftv_kind :: Env -> Vname -> Expr -> Kind -> WFType -> Proof
lem_wf_ftv_kind g a tt k p_g_a = case k of 
  Base -> case p_g_a of
    (WFRefn _ _ _ tt' p'_g_a _ _ _) -> lem_wf_ftv_kind g  a tt' k p'_g_a
    (WFVar1 {})                 -> ()
    (WFVar2 g' _ _ _ p_g'_a _ _)  -> lem_wf_ftv_kind g' a tt k p_g'_a
    (WFVar3 g' _ _ _ p_g'_a _ _)  -> lem_wf_ftv_kind g' a tt k p_g'_a
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

-- These lemmas allow us to directly invert the Well Formedness Judgments of certain types 
--     by allowing us to bypass the possibility of WFKind
{-@ lem_wffunc_for_wf_tfunc :: g:Env -> x:Vname -> t_x:Type -> t:Type -> k:Kind 
        -> { p_g_txt : WFType | propOf p_g_txt  == WFType g (TFunc x t_x t) k }
        -> { p_g_txt': WFType | propOf p_g_txt' == WFType g (TFunc x t_x t) Star && isWFFunc p_g_txt' } @-}
lem_wffunc_for_wf_tfunc :: Env -> Vname -> Type -> Type -> Kind -> WFType -> WFType
lem_wffunc_for_wf_tfunc g x t_x t k p_g_txt@(WFFunc {})           = case k of 
  Base -> impossible ("by lemma" ? lem_wf_tfunc_star g x t_x t p_g_txt)
  Star -> p_g_txt
lem_wffunc_for_wf_tfunc g x t_x t k (WFKind _g _ext p_g_txt_base) 
  = impossible ("by lemma" ? lem_wf_tfunc_star g x t_x t p_g_txt_base)

{-@ lem_wf_tfunc_star :: g:Env -> x:Vname -> t_x:Type -> t:Type
        -> ProofOf(WFType g (TFunc x t_x t) Base) -> { pf:_ | false } @-}
lem_wf_tfunc_star :: Env -> Vname -> Type -> Type -> WFType -> Proof
lem_wf_tfunc_star g x t_x t (WFBase {}) = ()
lem_wf_tfunc_star g x t_x t (WFRefn {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar1 {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar2 {}) = ()
lem_wf_tfunc_star g x t_x t (WFVar3 {}) = ()
lem_wf_tfunc_star g x t_x t (WFFunc {}) = ()
lem_wf_tfunc_star g x t_x t (WFExis {}) = ()
lem_wf_tfunc_star g x t_x t (WFPoly {}) = ()
lem_wf_tfunc_star g x t_x t (WFKind _g txt p_g_txt_base) = ()

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

{-@ lem_wfpoly_for_wf_tpoly :: g:Env -> a:Vname -> k:Kind -> t:Type 
        -> { p_g_at : WFType | propOf p_g_at  == WFType g (TPoly a k t) Star }
        -> { p_g_at': WFType | propOf p_g_at' == WFType g (TPoly a k t) Star && isWFPoly p_g_at' } @-}
lem_wfpoly_for_wf_tpoly :: Env -> Vname -> Kind -> Type -> WFType -> WFType
lem_wfpoly_for_wf_tpoly g a k t p_g_at@(WFPoly {})           = p_g_at
lem_wfpoly_for_wf_tpoly g a k t (WFKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_tpoly_star g a k t p_g_at_base)

{-@ lem_wf_tpoly_star :: g:Env -> a:Vname -> k:Kind -> t:Type
        -> ProofOf(WFType g (TPoly a k t) Base) -> { pf:_ | false } @-}
lem_wf_tpoly_star :: Env -> Vname -> Kind -> Type -> WFType -> Proof
lem_wf_tpoly_star g a k t (WFBase {}) = ()
lem_wf_tpoly_star g a k t (WFRefn {}) = ()
lem_wf_tpoly_star g a k t (WFVar1 {}) = ()
lem_wf_tpoly_star g a k t (WFVar2 {}) = ()
lem_wf_tpoly_star g a k t (WFVar3 {}) = ()
lem_wf_tpoly_star g a k t (WFFunc {}) = ()
lem_wf_tpoly_star g a k t (WFExis {}) = ()
lem_wf_tpoly_star g a k t (WFPoly {}) = ()
lem_wf_tpoly_star g a k t (WFKind {}) = ()

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

 -- SYSTEM F VERSIONS

{-@ lem_wfftfunc_for_wf_ftfunc :: g:FEnv -> t_x:FType -> t:FType -> k:Kind 
        -> { p_g_txt : WFFT | propOf p_g_txt  == WFFT g (FTFunc t_x t) k }
        -> { p_g_txt': WFFT | propOf p_g_txt' == WFFT g (FTFunc t_x t) Star && isWFFTFunc p_g_txt' } @-}
lem_wfftfunc_for_wf_ftfunc :: FEnv -> FType -> FType -> Kind -> WFFT -> WFFT
lem_wfftfunc_for_wf_ftfunc g t_x t k p_g_txt@(WFFTFunc {})           = case k of 
  Base -> impossible ("by lemma" ? lem_wf_ftfunc_star g t_x t p_g_txt)
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

{-@ lem_wfftpoly_for_wf_ftpoly :: g:FEnv -> a:Vname -> k:Kind -> t:FType 
        -> { p_g_at : WFFT | propOf p_g_at  == WFFT g (FTPoly a k t) Star }
        -> { p_g_at': WFFT | propOf p_g_at' == WFFT g (FTPoly a k t) Star && isWFFTPoly p_g_at' } @-}
lem_wfftpoly_for_wf_ftpoly :: FEnv -> Vname -> Kind -> FType -> WFFT -> WFFT
lem_wfftpoly_for_wf_ftpoly g a k t p_g_at@(WFFTPoly {})           = p_g_at
lem_wfftpoly_for_wf_ftpoly g a k t (WFFTKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_ftpoly_star g a k t p_g_at_base)

{-@ lem_wf_ftpoly_star :: g:FEnv -> a:Vname -> k:Kind -> t:FType
        -> ProofOf(WFFT g (FTPoly a k t) Base) -> { pf:_ | false } @-}
lem_wf_ftpoly_star :: FEnv -> Vname -> Kind -> FType -> WFFT -> Proof
lem_wf_ftpoly_star g a k t (WFFTBasic {}) = ()
lem_wf_ftpoly_star g a k t (WFFTFV1 {}) = ()
lem_wf_ftpoly_star g a k t (WFFTFV2 {}) = ()
lem_wf_ftpoly_star g a k t (WFFTFV3 {}) = ()
lem_wf_ftpoly_star g a k t (WFFTFunc {}) = ()
lem_wf_ftpoly_star g a k t (WFFTPoly {}) = ()
lem_wf_ftpoly_star g a k t (WFFTKind {}) = ()

-}

------------------------------------------------------------------------------------------
-- | LEMMAS relating REFINEMENT ERASURE and WELL FORMEDNESS notions
------------------------------------------------------------------------------------------

{-@ lem_strengthen_wffe :: g:FEnv -> { x:Vname | not (in_envF x g) } -> t_x:FType 
        -> { g':FEnv | not (in_envF x g') && Set_emp (Set_cap (bindsF g) (bindsF g')) }
        -> ProofOf(WFFE (concatF (FCons x t_x g) g')) -> ProofOf(WFFE (concatF g g')) @-}
lem_strengthen_wffe :: FEnv -> Vname -> FType -> FEnv -> WFFE -> WFFE
lem_strengthen_wffe g x t_x (FEmpty)          p_env_wf = p_g_wf
  where
    (WFFBind _g p_g_wf _ _ _ _) = p_env_wf
lem_strengthen_wffe g x t_x (FCons  z t_z g') p_env_wf = p_gg'z_wf
  where
    (WFFBind _env' p_env'_wf _ _ k_z p_env'_tz) = p_env_wf
    p_gg'_wf  = lem_strengthen_wffe g x t_x g' p_env'_wf
    p_gg'_tz  = lem_strengthen_wfft g x t_x g' t_z k_z p_env'_tz
    p_gg'z_wf = WFFBind (concatF g g') p_gg'_wf z t_z k_z p_gg'_tz
lem_strengthen_wffe g x t_x (FConsT a k_a g') p_env_wf = p_gg'a_wf
  where
    (WFFBindT _env' p_env'_wf  _ _) = p_env_wf
    p_gg'_wf  = lem_strengthen_wffe g x t_x g' p_env'_wf
    p_gg'a_wf = WFFBindT (concatF g g') p_gg'_wf a k_a

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
                               (lem_strengthen_wfft g x t_x g'' (FTBasic (FTV a)) k p_g_a) y t
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

{-
{-@ lem_erase_wftype :: g:Env -> t:Type -> k:Kind -> ProofOf(WFType g t k)
                              -> ProofOf(WFFT (erase_env g) (erase t) k) @-}
lem_erase_wftype :: Env -> Type -> Kind -> WFType -> WFFT
lem_erase_wftype _ _ _ (WFBase g b _)                = WFFTBasic (erase_env g) b
lem_erase_wftype _ t k pf_g_t@(WFRefn g x b tt pf_g_b p y pf_yg_p)  
  = case b of
      (FTV a)  -> lem_erase_wftype g (TRefn (FTV a) Z tt) Base pf_g_b
      (BTV a)  -> impossible ("by lemma" ? lem_btv_not_wf g a x p k pf_g_t)
      TBool    -> WFFTBasic (erase_env g) TBool
      TInt     -> WFFTBasic (erase_env g) TInt
lem_erase_wftype _ t _ (WFVar1 g a _ k)              = WFFTFV1 (erase_env g) a k
lem_erase_wftype _ t _ (WFVar2 g a tt k pf_g_a y t_y)
  = WFFTFV2 (erase_env g) a k (lem_erase_wftype g (TRefn (FTV a) Z tt) k pf_g_a) 
            y (erase t_y)
lem_erase_wftype _ t _ (WFVar3 g a tt k pf_g_a a' k')
  = WFFTFV3 (erase_env g) a k (lem_erase_wftype g (TRefn (FTV a) Z tt) k pf_g_a) a' k'
lem_erase_wftype _ _ _ (WFFunc g x t_x k_x pf_g_tx t k y pf_yg_t)
  = WFFTFunc (erase_env g) (erase t_x) k_x (lem_erase_wftype g t_x k_x pf_g_tx)
                           (erase t) k pf_erase_g_t
      where
        pf_erase_g_t  = lem_strengthen_wfft (erase_env g) y (erase t_x) FEmpty
                            (erase t) k (pf_erase_yg_t ? lem_erase_tsubBV x (FV y) t)
        pf_erase_yg_t = lem_erase_wftype (Cons y t_x g) (unbindT x y t) k 
                            pf_yg_t ? lem_erase_tsubBV x (FV y) t
lem_erase_wftype _ _ _ (WFExis g x t_x k_x p_g_tx t k y pf_yg_t)
  = lem_strengthen_wfft (erase_env g) y (erase t_x) FEmpty
                        (erase t ? lem_erase_tsubBV x (FV y) t) k pf_erase_yg_t
      where
        pf_erase_yg_t = lem_erase_wftype (Cons y t_x g) (unbindT x y t) k pf_yg_t
lem_erase_wftype _ _ _ (WFPoly g a k t k_t a' pf_a'g_t)
  = WFFTPoly (erase_env g) a k (erase t) k_t a' 
             (lem_erase_wftype (ConsT a' k g) 
                       (unbind_tvT a a' t ? lem_erase_unbind_tvT a a' t
                                          ? lem_erase_freeTV t) 
                       k_t pf_a'g_t)
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
        
-}   
-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to the abscence of dangling BOUND VARIABLES without a binder
-------------------------------------------------------------------------------------------

{-
{-@ lem_freeBTV_unbind_tv_empty :: a:Vname -> a':Vname 
        -> { e:Expr | Set_emp (freeBTV (unbind_tv a a' e)) && Set_emp (freeBV (unbind_tv a a' e)) }
        -> { pf:_ | (Set_emp (freeBTV e) || freeBTV e == Set_sng a) && Set_emp (freeBV e) } @-}
lem_freeBTV_unbind_tv_empty :: Vname -> Vname -> Expr -> Proof
lem_freeBTV_unbind_tv_empty a a' e = toProof ( S.empty === freeBTV (unbind_tv a a' e)
                                      === S.difference (freeBTV e) (S.singleton a) )

{-@ lem_tfreeBTV_unbind_tvT_empty :: a:Vname -> a':Vname 
        -> { t:Type | Set_emp (tfreeBTV (unbind_tvT a a' t)) && Set_emp (tfreeBV (unbind_tvT a a' t)) }
        -> { pf:_ | (Set_emp (tfreeBTV t) || tfreeBTV t == Set_sng a) && Set_emp (tfreeBV t) } @-}
lem_tfreeBTV_unbind_tvT_empty :: Vname -> Vname -> Type -> Proof
lem_tfreeBTV_unbind_tvT_empty a a' t = toProof ( S.empty === tfreeBTV (unbind_tvT a a' t)
                                      === S.difference (tfreeBTV t) (S.singleton a) )

{-@ lem_ffreeBV_unbindFT_empty :: a:Vname -> a':Vname 
        -> { t:FType | Set_emp (ffreeBV (unbindFT a a' t)) }
        -> { pf:_ | Set_emp (ffreeBV t) || ffreeBV t == Set_sng a } @-}
lem_ffreeBV_unbindFT_empty :: Vname -> Vname -> FType -> Proof
lem_ffreeBV_unbindFT_empty a a' t = toProof ( S.empty === ffreeBV (unbindFT a a' t)
                                      === S.difference (ffreeBV t) (S.singleton a) )
-}

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
  (Lambda _) -> () ? lem_islc_at_open_at 0 0 y 
                         (e' ? lem_ftyp_islc (FCons y t_x g) (unbind y e') t' (mk_p_yg_e'_t' y))
    where
      y = fresh_varF nms g
lem_ftyp_islc g e t (FTApp _g e' t_x t' p_e'_txt' e_x p_ex_tx) = case e of
  (App _ _) -> () ? lem_ftyp_islc g e' (FTFunc t_x t') p_e'_txt'
                  ? lem_ftyp_islc g e_x t_x p_ex_tx
lem_ftyp_islc g e t (FTAbsT _g k e' t' nms mk_p_e'_t') = case e of 
  (LambdaT {}) -> () ? lem_islc_at_open_tv_at 0 0 a
                           (e' ? lem_ftyp_islc (FConsT a k g) (unbind_tv a e') (unbindFT a t') (mk_p_e'_t' a))
    where
      a = fresh_varF nms g
lem_ftyp_islc g e t (FTAppT _g e' k t' p_e_at' liqt p_g_ert) = case e of
  (AppT _ _)   -> () ? lem_ftyp_islc g e' (FTPoly k t') p_e_at'
lem_ftyp_islc g e t (FTLet _g e_x t_x p_ex_tx e' t' nms mk_p_yg_e'_t') = case e of
  (Let {}) -> () ? lem_ftyp_islc g e_x t_x p_ex_tx
                 ? lem_islc_at_open_at 0 0 y 
                       (e' ? lem_ftyp_islc (FCons y t_x g) (unbind y e') t' (mk_p_yg_e'_t' y))
    where
      y = fresh_varF nms g
lem_ftyp_islc g e t (FTAnn _g e' _t t1 p_e'_t) = case e of
  (Annot _ _)  -> () ? lem_ftyp_islc g e' t p_e'_t

{-
{-@ lem_tfreeBV_empty :: g:Env -> t:Type -> k:Kind -> { p_g_t:WFType | propOf p_g_t == WFType g t k }
        -> { pf:Proof | Set_emp (tfreeBV t) && Set_emp (tfreeBTV t) } / [wftypSize p_g_t] @-}
lem_tfreeBV_empty :: Env -> Type -> Kind -> WFType {-> WFEnv-} -> Proof
lem_tfreeBV_empty g t k (WFBase _g b _) {-p_g_wf-} = case t of 
  (TRefn _ _ tt) -> () ? lem_trivial_nobv tt 
lem_tfreeBV_empty g t k p_g_t@(WFRefn _g x b tt p_g_b p y p_yg_p_bl) {-p_g_wf-} = case t of
  (TRefn _ _ _) -> case b of 
    (BTV a) -> impossible ("by lemma" ? lem_btv_not_wf g a x p k p_g_t)
    _       -> () ? lem_freeBV_unbind_empty 0 y (p ? pf_unbinds_empty)
      where
        {-@ pf_unbinds_empty :: { pf:_ | Set_emp (freeBV (unbind 0 y p)) 
                                      && Set_emp (freeBTV (unbind 0 y p)) } @-}
        pf_unbinds_empty = lem_ftyp_islc (FCons y (FTBasic b) (erase_env g)) (unbind 0 y p) 
                                             (FTBasic TBool) p_yg_p_bl
lem_tfreeBV_empty g t k p_g_t@(WFVar1 _ a _ _k) = case t of 
  (TRefn (FTV _) _ tt) -> () ? lem_trivial_nobv tt
lem_tfreeBV_empty g t k p_g_t@(WFVar2 _ a _ _k _ _ _) = case t of 
  (TRefn (FTV _) _ tt) -> () ? lem_trivial_nobv tt
lem_tfreeBV_empty g t k p_g_t@(WFVar3 _ a _ _k _ _ _) = case t of
  (TRefn (FTV _) _ tt) -> () ? lem_trivial_nobv tt
lem_tfreeBV_empty g t k (WFFunc _g x t_x k_x p_g_tx t' k' y p_yg_t')  = case t of
  (TFunc _ _ _) -> () 
        ? lem_tfreeBV_empty g t_x k_x p_g_tx  
        ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t') k'
                                                                p_yg_t' )
lem_tfreeBV_empty g t k (WFExis _g x t_x k_x p_g_tx t' k' y p_yg_t')  = case t of
  (TExists _ _ _) -> () 
        ? lem_tfreeBV_empty g t_x k_x p_g_tx 
        ? lem_tfreeBV_unbindT_empty x y (t' ? lem_tfreeBV_empty (Cons y t_x g) (unbindT x y t') k'
                                                                p_yg_t' )
lem_tfreeBV_empty g t k (WFPoly _g a k_a t' k_t' a' p_a'g_t') = case t of 
  (TPoly _ _ _) -> () ? lem_tfreeBTV_unbind_tvT_empty a a' (t' ? lem_tfreeBV_empty (ConsT a' k_a g) 
                                                                 (unbind_tvT a a' t') k_t' p_a'g_t')
lem_tfreeBV_empty g t k (WFKind _g _t p_g_t_base) 
  = () ? lem_tfreeBV_empty g t Base p_g_t_base 
-}

{-
{-@ lem_ffreeBV_empty :: g:FEnv -> t:FType -> k:Kind -> { p_g_t:WFFT | propOf p_g_t == WFFT g t k }
        -> { pf:Proof | Set_emp (ffreeBV t) } / [wfftypSize p_g_t] @-}
lem_ffreeBV_empty :: FEnv -> FType -> Kind -> WFFT -> Proof
lem_ffreeBV_empty g t k (WFFTBasic _g b) = () 
lem_ffreeBV_empty g t k p_g_t@(WFFTFV1 _ a _k) = ()
lem_ffreeBV_empty g t k p_g_t@(WFFTFV2 _ a _k _ _ _) = ()
lem_ffreeBV_empty g t k p_g_t@(WFFTFV3 _ a _k _ _ _) = ()
lem_ffreeBV_empty g t k (WFFTFunc _g t_x k_x p_g_tx t' k' p_g_t') 
  = ()  ? lem_ffreeBV_empty g t_x k_x p_g_tx 
        ? lem_ffreeBV_empty g t'  k'  p_g_t' 
lem_ffreeBV_empty g t k (WFFTPoly _g a k_a t' k_t' a' p_a'g_t') 
  = ()  ? lem_ffreeBV_unbindFT_empty a a' (t' ? lem_ffreeBV_empty (FConsT a' k_a g) 
                                                                 (unbindFT a a' t') k_t' p_a'g_t')
lem_ffreeBV_empty g t k (WFFTKind _g _t p_g_t_base) 
  = () ? lem_ffreeBV_empty g t Base p_g_t_base 
-}
