Require Import SystemRF.BasicDefinitions. (* originally 505 lines*)
Require Import SystemRF.Names.
Require Import SystemRF.LocalClosure.
Require Import SystemRF.SystemFWellFormedness.
Require Import SystemRF.SystemFTyping.
(*import BasicPropsSubstitution*)
Require Import SystemRF.BasicPropsEnvironments.
(*import WellFormedness*)

(*
{-@ lem_btv_not_wf :: g:env -> a:vname -> ps:preds -> k:kind
                        -> ProofOf(WFtype g (TRefn (BTV a) ps) k) -> { pf:_ | false } @-}
lem_btv_not_wf :: env -> vname -> preds -> kind -> WFtype -> Proof
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

{-@ lem_wf_ftv_kind :: g:env -> a:vname -> k:kind -> ProofOf(WFtype g (TRefn (FTV a) PEmpty) k)
       -> { pf:_ | k == Star || kind_for_tv a g == Base } @-}
lem_wf_ftv_kind :: env -> vname -> kind -> WFtype -> Proof
lem_wf_ftv_kind g a k p_g_a = case k of 
  Base -> case p_g_a of
    (WFRefn _ _ p'_g_a _ _ _)  -> lem_wf_ftv_kind g  a k p'_g_a
    (WFVar1 {})                -> ()
    (WFVar2 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kind g' a k p_g'_a
    (WFVar3 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kind g' a k p_g'_a
  Star -> ()

{-@ lem_kind_for_tv ::  g:env -> { g':env | Set_emp (Set_cap (binds g) (binds g')) } 
        -> { a:vname | not (in_env a g) && not (in_env a g') } -> k_a:kind
        -> { pf:_ | kind_for_tv a (concatE (ConsT a k_a g) g') == k_a } @-} 
lem_kind_for_tv :: env -> env -> vname -> kind -> Proof
lem_kind_for_tv g Empty            a k_a = ()
lem_kind_for_tv g (Cons  x t_x g') a k_a = () ? lem_kind_for_tv g g' a k_a
lem_kind_for_tv g (ConsT a' k' g') a k_a = () ? lem_kind_for_tv g g' a k_a

{-@ lem_wf_ftv_kindF :: g:fenv -> a:vname -> k:kind -> ProofOf(WFFT g (FTBasic (FTV a)) k)
       -> { pf:_ | k == Star || kind_for_tvF a g == Base } @-}
lem_wf_ftv_kindF :: fenv -> vname -> kind -> WFFT -> Proof
lem_wf_ftv_kindF g a k p_g_a = case k of 
  Base -> case p_g_a of
    (WFFTBasic _ _)             -> ()
    (WFFTFV1 {})                -> ()
    (WFFTFV2 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kindF g' a k p_g'_a
    (WFFTFV3 g' _ _ p_g'_a _ _) -> lem_wf_ftv_kindF g' a k p_g'_a
  Star -> ()

{-@ lem_kind_for_tvF :: g:fenv -> { g':fenv | Set_emp (Set_cap (bindsF g) (bindsF g')) } 
        -> { a:vname | not (in_envF a g) && not (in_envF a g') } -> k_a:kind
        -> { pf:_ | kind_for_tvF a (concatF (FConsT a k_a g) g') == k_a } @-} 
lem_kind_for_tvF :: fenv -> fenv -> vname -> kind -> Proof
lem_kind_for_tvF g FEmpty            a k_a = ()
lem_kind_for_tvF g (FCons  x t_x g') a k_a = () ? lem_kind_for_tvF g g' a k_a
lem_kind_for_tvF g (FConsT a' k' g') a k_a = () ? lem_kind_for_tvF g g' a k_a

{-@ lem_wf_pempty_for_wf_trefn :: g:env -> b:Basic -> ps:preds -> k:kind
        -> { p_g_t : WFtype | propOf p_g_t  == WFtype g (TRefn b ps) k }
        -> { p_g_t': WFtype | propOf p_g_t' == WFtype g (TRefn b PEmpty) k} @-}
lem_wf_pempty_for_wf_trefn :: env -> Basic -> preds -> kind -> WFtype -> WFtype
lem_wf_pempty_for_wf_trefn g b ps k p_g_t@(WFBase _g _b)              = p_g_t
lem_wf_pempty_for_wf_trefn g b ps k p_g_t@(WFRefn _ _ p_g_tt _p _ _)  = p_g_tt
lem_wf_pempty_for_wf_trefn g b ps k p_g_t@(WFVar1 g' a _k)            = p_g_t
lem_wf_pempty_for_wf_trefn g b ps k p_g_t@(WFVar2 _ _ _ p_g_a _ _)    = p_g_t
lem_wf_pempty_for_wf_trefn g b ps k p_g_t@(WFVar3 _ _ _ p_g_a _ _)    = p_g_t
lem_wf_pempty_for_wf_trefn g b ps k (WFKind _g _t p_g_t_base) 
    = WFKind g (TRefn b PEmpty) p_g_t'
          where
            p_g_t' = lem_wf_pempty_for_wf_trefn g b ps Base p_g_t_base

-- These lemmas allow us to directly invert the Well Formedness Judgments of certain types 
--     by allowing us to bypass the possibility of WFKind
{-@ lem_wffunc_for_wf_tfunc :: g:env -> t_x:type -> t:type -> k:kind 
        -> { p_g_txt : WFtype | propOf p_g_txt  == WFtype g (TFunc t_x t) k }
        -> { p_g_txt': WFtype | propOf p_g_txt' == WFtype g (TFunc t_x t) Star && isWFFunc p_g_txt' } @-}
lem_wffunc_for_wf_tfunc :: env  -> type -> type -> kind -> WFtype -> WFtype
lem_wffunc_for_wf_tfunc g t_x t k p_g_txt@(WFFunc {})           = case k of 
  Base -> impossible ("by lemma" ? lem_wf_tfunc_star g t_x t p_g_txt)
  Star -> p_g_txt
lem_wffunc_for_wf_tfunc g t_x t k (WFKind _g _ext p_g_txt_base) 
  = impossible ("by lemma" ? lem_wf_tfunc_star g t_x t p_g_txt_base)

{-@ lem_wf_tfunc_star :: g:env -> t_x:type -> t:type
        -> ProofOf(WFtype g (TFunc t_x t) Base) -> { pf:_ | false } @-}
lem_wf_tfunc_star :: env ->  type -> type -> WFtype -> Proof
lem_wf_tfunc_star g t_x t (WFBase {}) = ()
lem_wf_tfunc_star g t_x t (WFRefn {}) = ()
lem_wf_tfunc_star g t_x t (WFVar1 {}) = ()
lem_wf_tfunc_star g t_x t (WFVar2 {}) = ()
lem_wf_tfunc_star g t_x t (WFVar3 {}) = ()
lem_wf_tfunc_star g t_x t (WFFunc {}) = ()
lem_wf_tfunc_star g t_x t (WFExis {}) = ()
lem_wf_tfunc_star g t_x t (WFPoly {}) = ()
lem_wf_tfunc_star g t_x t (WFKind _g txt p_g_txt_base) = ()

-- Given G |-w \exists x:t_x. t : k, we can produce a proof tree ending in WFExis
{-@ lem_wfexis_for_wf_texists :: g:env -> t_x:type -> t:type -> k:kind
        -> { p_g_ex_t : WFtype | propOf p_g_ex_t  == WFtype g (TExists t_x t) k }
        -> { p_g_ex_t': WFtype | propOf p_g_ex_t' == WFtype g (TExists t_x t) k && isWFExis p_g_ex_t' } @-}
lem_wfexis_for_wf_texists :: env -> type -> type -> kind -> WFtype -> WFtype
lem_wfexis_for_wf_texists g t_x t k p_g_ex_t@(WFExis {})           = p_g_ex_t
lem_wfexis_for_wf_texists g t_x t k (WFKind _g _ext p_g_ex_t_base) 
  = WFExis g t_x k_x p_g_tx t Star nms' mk_p_yg_t_star
      where
        {-@ mk_p_yg_t_star :: { y:vname | NotElem y nms' }
              -> { pf:WFtype | propOf pf == WFtype (Cons y t_x g) (unbindT y t) Star } @-}
        mk_p_yg_t_star y = case k_t of 
            Base -> WFKind (Cons y t_x g) (unbindT y t) (mk_p_yg_t_kt y)
            Star -> mk_p_yg_t_kt y
        (WFExis _ _ k_x p_g_tx _ k_t nms mk_p_yg_t_kt) = p_g_ex_t_base
        nms'          = unionEnv nms g

{-@ lem_wfpoly_for_wf_tpoly :: g:env -> k:kind -> t:type 
      -> { p_g_at : WFtype | propOf p_g_at  == WFtype g (TPoly k t) Star }
      -> { p_g_at': WFtype | propOf p_g_at' == WFtype g (TPoly k t) Star && isWFPoly p_g_at' } @-}
lem_wfpoly_for_wf_tpoly :: env -> kind -> type -> WFtype -> WFtype
lem_wfpoly_for_wf_tpoly g k t p_g_at@(WFPoly {})           = p_g_at
lem_wfpoly_for_wf_tpoly g k t (WFKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_tpoly_star g k t p_g_at_base)

{-@ lem_wfpoly_for_wf_tpoly' :: g:env -> k:kind -> t:type -> k_t:kind
      -> { p_g_at : WFtype | propOf p_g_at  == WFtype g (TPoly k t) k_t }
      -> { p_g_at': WFtype | propOf p_g_at' == WFtype g (TPoly k t) Star && isWFPoly p_g_at' } @-}
lem_wfpoly_for_wf_tpoly' :: env -> kind -> type -> kind -> WFtype -> WFtype
lem_wfpoly_for_wf_tpoly' g k t k_t p_g_at@(WFPoly {})           = case k_t of 
  Star -> p_g_at
lem_wfpoly_for_wf_tpoly' g k t k_t (WFKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_tpoly_star g k t p_g_at_base)

{-@ lem_wf_tpoly_star :: g:env -> k:kind -> t:type
        -> ProofOf(WFtype g (TPoly k t) Base) -> { pf:_ | false } @-}
lem_wf_tpoly_star :: env -> kind -> type -> WFtype -> Proof
lem_wf_tpoly_star g k t (WFBase {}) = ()
lem_wf_tpoly_star g k t (WFRefn {}) = ()
lem_wf_tpoly_star g k t (WFVar1 {}) = ()
lem_wf_tpoly_star g k t (WFVar2 {}) = ()
lem_wf_tpoly_star g k t (WFVar3 {}) = ()
lem_wf_tpoly_star g k t (WFFunc {}) = ()
lem_wf_tpoly_star g k t (WFExis {}) = ()
lem_wf_tpoly_star g k t (WFPoly {}) = ()
lem_wf_tpoly_star g k t (WFKind {}) = ()

 -- SYSTEM F VERSIONS

{-@ lem_wfftfunc_for_wf_ftfunc :: g:fenv -> t_x:ftype -> t:ftype -> k:kind 
        -> { p_g_txt : WFFT | propOf p_g_txt  == WFFT g (FTFunc t_x t) k }
        -> { p_g_txt': WFFT | propOf p_g_txt' == WFFT g (FTFunc t_x t) Star && isWFFTFunc p_g_txt' } @-}
lem_wfftfunc_for_wf_ftfunc :: fenv -> ftype -> ftype -> kind -> WFFT -> WFFT
lem_wfftfunc_for_wf_ftfunc g t_x t k p_g_txt@(WFFTFunc {})           = case k of 
  Star -> p_g_txt
lem_wfftfunc_for_wf_ftfunc g t_x t k (WFFTKind _g _ext p_g_txt_base) 
  = impossible ("by lemma" ? lem_wf_ftfunc_star g t_x t p_g_txt_base)

{-@ lem_wf_ftfunc_star :: g:fenv -> t_x:ftype -> t:ftype
        -> ProofOf(WFFT g (FTFunc t_x t) Base) -> { pf:_ | false } @-}
lem_wf_ftfunc_star :: fenv -> ftype -> ftype -> WFFT -> Proof
lem_wf_ftfunc_star g t_x t (WFFTBasic {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFV1 {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFV2 {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFV3 {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTFunc {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTPoly {}) = ()
lem_wf_ftfunc_star g t_x t (WFFTKind _g txt p_g_txt_base) = ()

{-@ lem_wfftpoly_for_wf_ftpoly :: g:fenv -> k:kind -> t:ftype 
        -> { p_g_at : WFFT | propOf p_g_at  == WFFT g (FTPoly k t) Star }
        -> { p_g_at': WFFT | propOf p_g_at' == WFFT g (FTPoly k t) Star && isWFFTPoly p_g_at' } @-}
lem_wfftpoly_for_wf_ftpoly :: fenv -> kind -> ftype -> WFFT -> WFFT
lem_wfftpoly_for_wf_ftpoly g k t p_g_at@(WFFTPoly {})           = p_g_at
lem_wfftpoly_for_wf_ftpoly g k t (WFFTKind _g _at p_g_at_base) 
  = impossible ("by lemma" ? lem_wf_ftpoly_star g k t p_g_at_base)

{-@ lem_wf_ftpoly_star :: g:fenv -> k:kind -> t:ftype
        -> ProofOf(WFFT g (FTPoly k t) Base) -> { pf:_ | false } @-}
lem_wf_ftpoly_star :: fenv -> kind -> ftype -> WFFT -> Proof
lem_wf_ftpoly_star g k t (WFFTBasic {}) = ()
lem_wf_ftpoly_star g k t (WFFTFV1 {}) = ()
lem_wf_ftpoly_star g k t (WFFTFV2 {}) = ()
lem_wf_ftpoly_star g k t (WFFTFV3 {}) = ()
lem_wf_ftpoly_star g k t (WFFTFunc {}) = ()
lem_wf_ftpoly_star g k t (WFFTPoly {}) = ()
lem_wf_ftpoly_star g k t (WFFTKind {}) = () *)

(*------------------------------------------------------------------------------------------
-- | LEMMAS relating REFINEMENT ERASURE and WELL FORMEDNESS notions
------------------------------------------------------------------------------------------*)

Lemma lem_strengthen_wfft' : forall (g'xg : fenv) (t : ftype) (k : kind),
    WFFT g'xg t k -> ( forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv),
        g'xg = concatF (FCons x t_x g) g' 
                           -> uniqueF g -> uniqueF g'
                           -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> WFFT (concatF g g') t k ).
Proof. apply ( WFFT_ind 
  (fun (g'xg : fenv) (t : ftype) (k : kind) => 
      forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv),
          g'xg = concatF (FCons x t_x g) g' 
                          -> uniqueF g -> uniqueF g' 
                         -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> WFFT (concatF g g') t k  ));
  intro env; intros; subst env.
  - apply WFFTBasic; assumption.
  - (* WFFTFV *) apply WFFTFV;
    apply lem_tvboundinF_strengthen in H; assumption.
  - (* WFFTFunc *) apply WFFTFunc with k1 k2; 
    apply H0 with x t_x || apply H2 with x t_x; intuition.
  - (* WFFTPoly *) apply WFFTPoly with k_t (names_add x (union nms (bindsF (concatF g g'))));
    intros; apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concatF_elim in H8; destruct H8;
    assert (FConsT a k (concatF g g') = concatF g (FConsT a k g')) by reflexivity;
    rewrite H10; apply H0 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; 
    try (apply intersect_names_add_intro_r);
    try assumption; intuition.
  - (* WFFTKind *) apply WFFTKind; apply H0 with x t_x; intuition.
  Qed.

Lemma lem_strengthen_wfft : 
  forall (g:fenv) (x:vname) (t_x:ftype) (g':fenv) (t:ftype) (k:kind),
    WFFT (concatF (FCons x t_x g) g') t k -> uniqueF g -> uniqueF g'
                                          -> intersect (bindsF g) (bindsF g') = empty
                                          -> ~ (in_envF x g) -> ~ (in_envF x g') 
                                          -> WFFT (concatF g g') t k.
Proof. intros; apply lem_strengthen_wfft' with (concatF (FCons x t_x g) g') x t_x;
  intuition. Qed.

(*
{-@ lem_erase_wftype :: g:env -> t:type -> k:kind -> ProofOf(WFtype g t k)
        -> ProofOf(WFFT (erase_env g) (erase t) k) / [tsize t, envsize g, ksize k] @-}
lem_erase_wftype :: env -> type -> kind -> WFtype -> WFFT
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
        {-@ mk_pf_ag_ert :: { a:vname | NotElem a nms' }
              -> ProofOf(WFFT (FConsT a k (erase_env g)) (unbindFT a (erase t)) k_t) @-}
        mk_pf_ag_ert a = lem_erase_wftype (ConsT a k g) (unbind_tvT a t ? lem_erase_unbind_tvT a t)
                                          k_t (mk_pf_ag_t a)
        nms'           = unionFEnv nms (erase_env g)
lem_erase_wftype _ _ _ (WFKind g t pf_t_base) 
  = WFFTKind (erase_env g) (erase t) (lem_erase_wftype g t Base pf_t_base)

{-@ lem_erase_env_wfenv :: g:env -> ProofOf(WFEnv g) -> ProofOf(WFFE (erase_env g)) @-}
lem_erase_env_wfenv :: env -> WFEnv -> WFFE
lem_erase_env_wfenv _ WFEEmpty                         = WFFEmpty
lem_erase_env_wfenv _ (WFEBind g pf_g_wf x t k p_g_t) 
  = WFFBind (erase_env g) (lem_erase_env_wfenv g pf_g_wf) 
            x (erase t) k (lem_erase_wftype g t k p_g_t)
lem_erase_env_wfenv _ (WFEBindT g pf_g_wf a k)
  = WFFBindT (erase_env g) (lem_erase_env_wfenv g pf_g_wf) a k

{-@ lem_truncate_wfenv :: g:env -> { g':env | Set_emp (Set_cap (binds g) (binds g')) }
        -> ProofOf(WFEnv (concatE g g')) -> ProofOf(WFEnv g) @-}
lem_truncate_wfenv :: env -> env -> WFEnv -> WFEnv
lem_truncate_wfenv g Empty          p_g_wf    = p_g_wf          
lem_truncate_wfenv g (Cons x v g')  p_xg'g_wf = lem_truncate_wfenv g g' p_g'g_wf
  where
    (WFEBind _ p_g'g_wf _ _ _ _) = p_xg'g_wf 
lem_truncate_wfenv g (ConsT a k g') p_ag'g_wf = lem_truncate_wfenv g g' p_g'g_wf
  where
    (WFEBindT _ p_g'g_wf _ _) = p_ag'g_wf
        
-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to FREE VARIABLES and WELL FORMEDNESS judgments
-------------------------------------------------------------------------------------------*)

(*
{-@ lem_free_bound_in_env :: g:env -> t:type -> k:kind -> ProofOf(WFtype g t k)
            -> { x:vname | not (in_env x g) }
            -> { pf:_ | not (Set_mem x (free t)) && not (Set_mem x (freeTV t)) } 
             / [tsize t, envsize g, ksize k] @-}
lem_free_bound_in_env :: env -> type -> kind -> WFtype -> vname -> Proof
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

{-@ lem_free_subset_binds :: g:env -> t:type -> k:kind -> ProofOf(WFtype g t k)
            -> { pf:_ | Set_sub (free t) (binds g) && Set_sub (freeTV t) (binds g) &&
                        Set_sub (free t) (vbinds g) && Set_sub (freeTV t) (tvbinds g) } 
             / [tsize t, envsize g, ksize k] @-}
lem_free_subset_binds :: env -> type -> kind -> WFtype -> Proof
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

{-@ lem_closed_free_empty :: t:type -> k:kind -> ProofOf(WFtype Empty t k)
            -> { pf:_ | Set_emp (free t) && Set_emp (freeTV t) } @-}
lem_closed_free_empty :: type -> kind -> WFtype -> Proof
lem_closed_free_empty t k p_emp_t = lem_free_subset_binds Empty t k p_emp_t

-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to the abscence of dangling BOUND VARIABLES without a binder
-------------------------------------------------------------------------------------------*)

Lemma lem_ftyp_islc : forall (g:fenv) (e:expr) (t:ftype),
    HasFtype g e t -> isLC e.
Proof. intros; induction H; unfold isLC; simpl; intuition. 
  - (* FTAbs *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2.
    revert H2; unfold isLC.
    apply lem_islc_at_after_open_at.
  - (* FTAbsT *) pose proof (fresh_not_elem nms);
    set (a' := fresh nms) in H1; apply H0 in H1.
    revert H1; unfold isLC.
    apply lem_islc_at_after_open_tv_at.
  - (* FTLet *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2.
    revert H2; unfold isLC.
    apply lem_islc_at_after_open_at.
  Qed.

  
(*
{-@ lem_pftyp_islcp :: g:fenv -> ps:preds -> ProofOf(PHasFtype g ps)
                              -> { pf:_ | isLCP ps && isLCP_at 0 0 ps } / [predsize ps] @-}
lem_pftyp_islcp :: fenv -> preds -> PHasFtype -> Proof 
lem_pftyp_islcp g ps (PFTEmp  _)                         = ()
lem_pftyp_islcp g ps (PFTCons _ p pf_p_bl ps' pf_ps'_bl) 
    = () ? lem_pftyp_islcp g ps' pf_ps'_bl
         ? lem_ftyp_islc   g p (FTBasic TBool) pf_p_bl
*)

Lemma lem_wfft_islcft : forall (g:fenv) (t:ftype) (k:kind),
    WFFT g t k -> isLCFT t.
Proof. intros; induction H; unfold isLCFT; simpl; intuition.
  - (* WFFTBasic *) destruct b; simpl in H; intuition.
  - (* WFFTPoly  *) assert (1 = 0 + 1) by intuition; rewrite H1.
    pose proof (fresh_varF_not_elem nms g); destruct H2.
    apply lem_islcft_at_after_openFT_at with (fresh_varF nms g).
    apply H0; assumption.
  Qed.


  (*
{-@ lem_wftype_islct :: g:env -> t:type -> k:kind -> { p_g_t:WFtype | propOf p_g_t == WFtype g t k }
        -> { pf:Proof | isLCT t }  / [tsize t, ksize k] @-}
lem_wftype_islct :: env -> type -> kind -> WFtype -> Proof
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
*)