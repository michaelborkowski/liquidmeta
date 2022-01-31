{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesFTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics                        
import SystemFWellFormedness            --(WFFT(..),WFFE(..))
import SystemFTyping                    --(HasFType(..),erase_ty)--,firstBV,inType,ty',refn_pred,ty,erase_ty)

{-@ reflect foo08 @-}
foo08 :: a -> Maybe a
foo08 x = Just x

-- | Well Formedness of System F PRIMITIVES

{-@ lem_wfft_erase_ty :: g:FEnv -> c:Prim -> ProofOf(WFFT g (erase_ty c) Star) @-}
lem_wfft_erase_ty :: FEnv -> Prim -> WFFT
lem_wfft_erase_ty g And      = makeWFFT g (erase_ty And) Star
lem_wfft_erase_ty g Or       = makeWFFT g (erase_ty Or) Star
lem_wfft_erase_ty g Not      = makeWFFT g (erase_ty Not) Star
lem_wfft_erase_ty g Imp      = makeWFFT g (erase_ty Imp) Star
lem_wfft_erase_ty g Eqv      = makeWFFT g (erase_ty Eqv) Star
lem_wfft_erase_ty g Leq      = makeWFFT g (erase_ty Leq) Star
lem_wfft_erase_ty g (Leqn n) = makeWFFT g (erase_ty (Leqn n)) Star
lem_wfft_erase_ty g Eq       = makeWFFT g (erase_ty Eq) Star
lem_wfft_erase_ty g (Eqn n)  = makeWFFT g (erase_ty (Eqn n)) Star
lem_wfft_erase_ty g Leql     = makeWFFT g (erase_ty Leql) Star
lem_wfft_erase_ty g Eql      = makeWFFT g (erase_ty Eql) Star

-----------------------------------------------------------------------------
-- | (System F) TYPES of DELTA (of Applications of Primitives)
-----------------------------------------------------------------------------

{-@ lem_bool_values :: { v:Expr | isValue v } -> ProofOf(HasFType FEmpty v (FTBasic TBool))
        -> { pf:_ | v == Bc True || v = Bc False } @-}
lem_bool_values :: Expr -> HasFType -> Proof
lem_bool_values v (FTBC _ _) = ()

{-@ reflect isInt @-}
isInt :: Expr -> Bool
isInt (Ic _ ) = True
isInt _       = False

{-@ lem_int_values :: v:Value -> ProofOf(HasFType FEmpty v (FTBasic TInt))
        -> { pf:_ | isInt v } @-}
lem_int_values :: Expr -> HasFType -> Proof
lem_int_values v (FTIC _ _) = ()

{-@ reflect isLambda @-}
isLambda :: Expr -> Bool
isLambda (Lambda _) = True
isLambda _          = False

{-@ reflect isLambdaT @-}
isLambdaT :: Expr -> Bool
isLambdaT (LambdaT _ _) = True
isLambdaT _             = False

{-@ reflect isPrim @-}
isPrim :: Expr -> Bool
isPrim (Prim _) = True
isPrim _        = False

{-@ reflect isPoly @-}
isPoly :: Prim -> Bool
isPoly Eql     = True
isPoly Leql    = True
isPoly _       = False

{-@ lem_prim_compat_in_ftapp :: p:Prim -> v:Value -> t:FType
        -> ProofOf(HasFType FEmpty (App (Prim p) v) t)
        -> { pf:_ | isCompat p v } @-}
lem_prim_compat_in_ftapp :: Prim -> Expr -> FType -> HasFType -> Proof
lem_prim_compat_in_ftapp And      v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_bool_values v p_v_tx
lem_prim_compat_in_ftapp Or       v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_bool_values v p_v_tx
lem_prim_compat_in_ftapp Not      v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_bool_values v p_v_tx
lem_prim_compat_in_ftapp Imp      v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_bool_values v p_v_tx
lem_prim_compat_in_ftapp Eqv      v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_bool_values v p_v_tx
lem_prim_compat_in_ftapp Leq      v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_int_values v p_v_tx
lem_prim_compat_in_ftapp (Leqn _) v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_int_values v p_v_tx
lem_prim_compat_in_ftapp Eq       v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_int_values v p_v_tx
lem_prim_compat_in_ftapp (Eqn _)  v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> () ? lem_int_values v p_v_tx
lem_prim_compat_in_ftapp Leql     v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> impossible ""
lem_prim_compat_in_ftapp Eql      v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> impossible ""

{-@ lemma_function_values :: v:Value -> t:FType -> t':FType
        -> ProofOf(HasFType FEmpty v (FTFunc t t'))
        -> { pf:_ | isLambda v || isPrim v } @-}
lemma_function_values :: Expr -> FType -> FType -> HasFType -> Proof
lemma_function_values e t t' (FTPrm {})   = ()     
lemma_function_values e t t' (FTAbs {})   = ()    

{-@ lemma_tfunction_values :: v:Value -> k:Kind -> t:FType
        -> ProofOf(HasFType FEmpty v (FTPoly k t))
        -> { pf:_ | isLambdaT v || isPrim v } @-}
lemma_tfunction_values :: Expr -> Kind -> FType -> HasFType -> Proof
lemma_tfunction_values v k t (FTPrm  {})   = ()     
lemma_tfunction_values v k t (FTAbsT {})   = ()    

{-@ lem_delta_and_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim And) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta And v) t' } @-}
lem_delta_and_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_and_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty And) -> case v of
          (Bc True)  -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                              (BV 0) (FTBasic TBool) [] make_x_bl
              where
                make_x_bl  x = (FTVar1 FEmpty x (FTBasic TBool) ) 
          (Bc False) -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                              (Bc False) (FTBasic TBool) [] make_ff_bl
              where
                make_ff_bl x = (FTBC (FCons x (FTBasic TBool) FEmpty) False)  
          _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx) 

{-@ lem_delta_or_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Or) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Or v) t' } @-} 
lem_delta_or_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_or_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Or) -> case v of
      (Bc True)  -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (Bc True) (FTBasic TBool) [] make_tt_bl
          where
            make_tt_bl x = (FTBC (FCons x (FTBasic TBool) FEmpty) True)
      (Bc False) -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (BV 0) (FTBasic TBool) [] make_x_bl
          where
            make_x_bl  x = (FTVar1 FEmpty x (FTBasic TBool) )
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_not_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Not) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Not v) t' } @-} 
lem_delta_not_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_not_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Not) -> case v of
      (Bc True)  -> FTBC FEmpty False 
      (Bc False) -> FTBC FEmpty True  
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_eqv_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Eqv) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Eqv v) t' } @-} 
lem_delta_eqv_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eqv_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Eqv) -> case v of
      (Bc True)  -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (BV 0) (FTBasic TBool) [] make_x_bl
          where
            make_x_bl  x = (FTVar1 FEmpty x (FTBasic TBool) )
      (Bc False) -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          not_x  (FTBasic TBool) [] make_notx_bl
          where
            not_x          = App (Prim Not) (BV 0)
            make_notx_bl x = let g = (FCons x (FTBasic TBool) FEmpty)
                                in FTApp g (Prim Not) (FTBasic TBool) (FTBasic TBool) (FTPrm g Not)
                                         (FV x) (FTVar1 FEmpty x (FTBasic TBool))
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_imp_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Imp) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Imp v) t' } @-} 
lem_delta_imp_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_imp_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Imp) -> case v of
      (Bc True)  -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (BV 0) (FTBasic TBool) [] make_x_bl
          where
            make_x_bl  x = (FTVar1 FEmpty x (FTBasic TBool) )
      (Bc False) -> FTAbs FEmpty (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (Bc True) (FTBasic TBool) [] make_tt_bl
          where
            make_tt_bl x = (FTBC (FCons x (FTBasic TBool) FEmpty) True)
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_leq_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Leq) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Leq v) t' } @-} 
lem_delta_leq_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_leq_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Leq) -> case v of
      (Ic n) -> FTPrm FEmpty (Leqn n) 
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_leqn_ftyp :: n:Int -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim (Leqn n)) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta (Leqn n) v) t' } @-} 
lem_delta_leqn_ftyp :: Int -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_leqn_ftyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty (Leqn _n)) -> case v of
      (Ic m) -> FTBC FEmpty ( n <= m ) 
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eq_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Eq) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Eq v) t' } @-} 
lem_delta_eq_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eq_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Eq) -> case v of
      (Ic n) -> FTPrm FEmpty (Eqn n) 
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eqn_ftyp :: n:Int -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim (Eqn n)) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta (Eqn n) v) t' } @-} 
lem_delta_eqn_ftyp :: Int -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eqn_ftyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty (Eqn _n)) -> case v of
      (Ic m) -> FTBC FEmpty ( n == m ) 
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_prim_ftyp_ftfunc :: c:Prim -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTFunc t_x t')) -> { pf:_ | not (isPoly c) } @-}
lem_prim_ftyp_ftfunc :: Prim -> FType -> FType -> HasFType -> Proof
lem_prim_ftyp_ftfunc c t_x t' (FTPrm _ _c) = ()

{-@ lem_delta_ftyp :: c:Prim -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta c v) t' } @-} 
lem_delta_ftyp :: Prim -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_ftyp And      v t_x t' p_c_txt' p_v_tx = lem_delta_and_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Or       v t_x t' p_c_txt' p_v_tx = lem_delta_or_ftyp     v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Not      v t_x t' p_c_txt' p_v_tx = lem_delta_not_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eqv      v t_x t' p_c_txt' p_v_tx = lem_delta_eqv_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Imp      v t_x t' p_c_txt' p_v_tx = lem_delta_imp_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Leq      v t_x t' p_c_txt' p_v_tx = lem_delta_leq_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp (Leqn n) v t_x t' p_c_txt' p_v_tx = lem_delta_leqn_ftyp n v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eq       v t_x t' p_c_txt' p_v_tx = lem_delta_eq_ftyp     v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp (Eqn n)  v t_x t' p_c_txt' p_v_tx = lem_delta_eqn_ftyp  n v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eql      _ t_x t' p_c_txt' _      
  = impossible ("by lemma" ? lem_prim_ftyp_ftfunc Eql  t_x t' p_c_txt')
lem_delta_ftyp Leql     _ t_x t' p_c_txt' _     
  = impossible ("by lemma" ? lem_prim_ftyp_ftfunc Leql t_x t' p_c_txt')

{-@ lem_base_types :: t:FType -> ProofOf(WFFT FEmpty t Base)  
        -> { pf:_ | t == FTBasic TBool || t == FTBasic TInt } @-}
lem_base_types :: FType -> WFFT -> Proof
lem_base_types t (WFFTBasic _ _) = ()

{-@ lem_base_types_star :: b:Basic -> ProofOf(WFFT FEmpty (FTBasic b) Star)  
        -> { pf:_ | b == TBool || b == TInt } @-}
lem_base_types_star :: Basic -> WFFT -> Proof
lem_base_types_star b (WFFTKind FEmpty _ p_t_star) = lem_base_types (FTBasic b) p_t_star

{-@ lem_prim_compatT_in_ftappt :: p:Prim -> rt:Type -> t:FType
        -> ProofOf(HasFType FEmpty (AppT (Prim p) rt) t)
        -> { pf:_ | isCompatT p rt } @-}
lem_prim_compatT_in_ftappt :: Prim -> Type -> FType -> HasFType -> Proof
lem_prim_compatT_in_ftappt Leql    rt t (FTAppT _ _ k t' p_c_akt' _ p_emp_errt)
  = case p_c_akt' of
      (FTPrm {}) -> () ? lem_base_types (erase rt) p_emp_errt
lem_prim_compatT_in_ftappt Eql     rt t (FTAppT _ _ k t' p_c_akt' _ p_emp_errt)
  = case p_c_akt' of
      (FTPrm {}) -> () ? lem_base_types (erase rt) p_emp_errt
lem_prim_compatT_in_ftappt c       rt t (FTAppT _ _ k t' p_c_akt' _ p_emp_errt)
  = case p_c_akt' of
      (FTPrm {}) -> impossible ""

{-@ lem_deltaT_ftyp :: c:Prim -> k:Kind -> s:FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTPoly k s)) 
        -> t:Type -> ProofOf(WFFT FEmpty (erase t) k)
        -> { pf:_ | propOf pf == HasFType FEmpty (deltaT c t) (ftsubBV (erase t) s) } @-}
lem_deltaT_ftyp :: Prim -> Kind -> FType -> HasFType -> Type -> WFFT -> HasFType
lem_deltaT_ftyp c k s p_c_aks t p_emp_t = case p_c_aks of
  (FTPrm FEmpty _c) -> case c of 
    (Eql)            -> case (erase t) of 
      (FTBasic TBool) -> FTPrm FEmpty Eqv 
      (FTBasic TInt)  -> FTPrm FEmpty Eq  
      _               -> impossible ("by lemma" ? lem_base_types (erase t) p_emp_t)
    (Leql)           -> case (erase t) of
      (FTBasic TBool) -> FTPrm FEmpty Imp
      (FTBasic TInt)  -> FTPrm FEmpty Leq
      _               -> impossible ("by lemma" ? lem_base_types (erase t) p_emp_t)
