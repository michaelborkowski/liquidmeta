{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module PrimitivesFTyping where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import Basics
import Semantics                        --(delta,deltaT,deltaC,isCompat,isCompatT,isCompatC)
import SystemFWellFormedness           -- (WFFT(..))
import SystemFTyping                    --(HasFType(..),erase_ty)--,firstBV,inType,ty',refn_pred,ty,erase_ty)

{-@ reflect foo08 @-}
foo08 :: a -> Maybe a
foo08 x = Just x

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
isLambda (Lambda _ _ ) = True
isLambda _             = False

{-@ reflect isLambdaT @-}
isLambdaT :: Expr -> Bool
isLambdaT (LambdaT _ _ _) = True
isLambdaT _               = False

{-@ reflect isPrim @-}
isPrim :: Expr -> Bool
isPrim (Prim _) = True
isPrim _        = False

{-@ reflect isEql @-}
isEql :: Prim -> Bool
isEql Eql     = True
isEql _       = False

{-@ lem_conj_compat_in_ftconj :: v:Value -> v':Value
        -> ProofOf(HasFType FEmpty (Conj v v') (FTBasic TBool)) -> { pf:_ | isCompatC v v' } @-}
lem_conj_compat_in_ftconj :: Expr -> Expr -> HasFType -> Proof
lem_conj_compat_in_ftconj v v' (FTConj _ _v p_v_bl _v' p_v'_bl)
  = () ? lem_bool_values v p_v_bl ? lem_bool_values v' p_v'_bl

{-@ lem_deltaC_ftyp :: v:Value -> ProofOf(HasFType FEmpty v (FTBasic TBool)) 
        -> v':Value -> ProofOf(HasFType FEmpty v' (FTBasic TBool))
        -> { pf:_ | propOf pf == HasFType FEmpty (deltaC v v') (FTBasic TBool) } @-} 
lem_deltaC_ftyp :: Expr -> HasFType -> Expr -> HasFType -> HasFType 
lem_deltaC_ftyp v p_v_bl v' p_v'_bl = case v of
  (Bc _) -> case v' of 
    (Bc _) -> FTBC FEmpty b 
      where 
        (Bc b) = deltaC v v'
    _      -> impossible ("by lemma" ? lem_bool_values v' p_v'_bl)
  _      -> impossible ("by lemma" ? lem_bool_values v p_v_bl)

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
lem_prim_compat_in_ftapp Eql      v t (FTApp _ _ t_x _ p_p_txt _ p_v_tx)
  = case p_p_txt of
      (FTPrm {}) -> impossible ""

{-@ lemma_function_values :: v:Value -> t:FType -> t':FType
        -> ProofOf(HasFType FEmpty v (FTFunc t t'))
        -> { pf:_ | isLambda v || isPrim v } @-}
lemma_function_values :: Expr -> FType -> FType -> HasFType -> Proof
lemma_function_values e t t' (FTPrm {})   = ()     
lemma_function_values e t t' (FTAbs {})   = ()    

{-@ lemma_tfunction_values :: v:Value -> a:Vname -> k:Kind -> t:FType
        -> ProofOf(HasFType FEmpty v (FTPoly a k t))
        -> { pf:_ | isLambdaT v || isPrim v } @-}
lemma_tfunction_values :: Expr -> Vname -> Kind -> FType -> HasFType -> Proof
lemma_tfunction_values v a k t (FTPrm  {})   = ()     
lemma_tfunction_values v a k t (FTAbsT {})   = ()    

{-@ lem_delta_and_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim And) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta And v) t' } @-}
lem_delta_and_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_and_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty And) -> case v of
          (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                              (BV 1) (FTBasic TBool) 1 (FTVar1 FEmpty 1 (FTBasic TBool) ) 
          (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                              (Bc False) (FTBasic TBool) 
                              1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) False)  
          _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx) 

{-@ lem_delta_or_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Or) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Or v) t' } @-} 
lem_delta_or_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_or_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Or) -> case v of
      (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (Bc True) (FTBasic TBool)
                          1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) True)
      (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (BV 1)    (FTBasic TBool) 
                          1 (FTVar1 FEmpty 1 (FTBasic TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)


{-@ lem_delta_not_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Not) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Not v) t' } @-} 
lem_delta_not_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_not_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Not) -> case v of
      (Bc True)  -> FTBC FEmpty False --    ? toProof ( t' === FTBasic TBool )
      (Bc False) -> FTBC FEmpty True  --    ? toProof ( t' === FTBasic TBool )
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_eqv_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Eqv) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Eqv v) t' } @-} -- &&
lem_delta_eqv_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eqv_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Eqv) -> case v of
      (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          (BV 1) (FTBasic TBool)
                          1 (FTVar1 FEmpty 1 (FTBasic TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
      (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) Base (WFFTBasic FEmpty TBool) 
                          not_x  (FTBasic TBool) 1 p_notx_bl
        where
          not_x     = App (Prim Not) (BV 1)
          g         = (FCons 1 (FTBasic TBool) FEmpty)
          p_notx_bl = FTApp g (Prim Not) (FTBasic TBool) (FTBasic TBool)
                            (FTPrm g Not) (FV 1) (FTVar1 FEmpty 1 (FTBasic TBool))
      _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx)

{-@ lem_delta_leq_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Leq) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Leq v) t' } @-} 
lem_delta_leq_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_leq_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Leq) -> case v of
      (Ic n) -> FTPrm FEmpty (Leqn n) --   ? toProof ( t' === (FTFunc (FTBasic TInt) (FTBasic TBool)) )
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_leqn_ftyp :: n:Int -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim (Leqn n)) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta (Leqn n) v) t' } @-} 
lem_delta_leqn_ftyp :: Int -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_leqn_ftyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty (Leqn _n)) -> case v of
      (Ic m) -> FTBC FEmpty ( n <= m ) --    ? toProof ( t' === FTBasic TBool)
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eq_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Eq) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Eq v) t' } @-} -- &&
lem_delta_eq_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eq_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Eq) -> case v of
      (Ic n) -> FTPrm FEmpty (Eqn n) --    ? toProof ( t' === (FTFunc (FTBasic TInt) (FTBasic TBool)) )
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_delta_eqn_ftyp :: n:Int -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim (Eqn n)) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta (Eqn n) v) t' } @-} -- &&
lem_delta_eqn_ftyp :: Int -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_eqn_ftyp n v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty (Eqn _n)) -> case v of
      (Ic m) -> FTBC FEmpty ( n == m ) --    ? toProof ( t' === FTBasic TBool)
      _      -> impossible ("by lemma" ? lem_int_values v p_v_tx)

{-@ lem_prim_ftyp_ftfunc :: c:Prim -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTFunc t_x t')) -> { pf:_ | not (isEql c) } @-}
lem_prim_ftyp_ftfunc :: Prim -> FType -> FType -> HasFType -> Proof
lem_prim_ftyp_ftfunc c t_x t' (FTPrm _ _c) = ()

{-@ lem_delta_ftyp :: c:Prim -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta c v) t' } @-} -- && not ((delta c v) == Crash) 
lem_delta_ftyp :: Prim -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_ftyp And      v t_x t' p_c_txt' p_v_tx = lem_delta_and_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Or       v t_x t' p_c_txt' p_v_tx = lem_delta_or_ftyp     v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Not      v t_x t' p_c_txt' p_v_tx = lem_delta_not_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eqv      v t_x t' p_c_txt' p_v_tx = lem_delta_eqv_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Leq      v t_x t' p_c_txt' p_v_tx = lem_delta_leq_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp (Leqn n) v t_x t' p_c_txt' p_v_tx = lem_delta_leqn_ftyp n v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eq       v t_x t' p_c_txt' p_v_tx = lem_delta_eq_ftyp     v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp (Eqn n)  v t_x t' p_c_txt' p_v_tx = lem_delta_eqn_ftyp  n v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eql      _ t_x t' p_c_txt' _      
  = impossible ("by lemma" ? lem_prim_ftyp_ftfunc Eql t_x t' p_c_txt')

{-@ lem_base_types :: t:FType -> ProofOf(WFFT FEmpty t Base)  
        -> { pf:_ | t == FTBasic (TBool) || t == FTBasic TInt } @-}
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
lem_prim_compatT_in_ftappt Eql     rt t (FTAppT _ _ a k t' p_c_akt' _ p_emp_errt)
  = case p_c_akt' of
      (FTPrm {}) -> () ? lem_base_types (erase rt) p_emp_errt
lem_prim_compatT_in_ftappt c       rt t (FTAppT _ _ a k t' p_c_akt' _ p_emp_errt)
  = case p_c_akt' of
      (FTPrm {}) -> impossible ""

{-@ lem_deltaT_ftyp :: c:Prim -> a:Vname -> k:Kind -> s:FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTPoly a k s)) 
        -> t:Type -> ProofOf(WFFT FEmpty (erase t) k)
        -> { pf:_ | propOf pf == HasFType FEmpty (deltaT c t) (ftsubBV a (erase t) s) } @-}
lem_deltaT_ftyp :: Prim -> Vname -> Kind -> FType -> HasFType -> Type -> WFFT -> HasFType
lem_deltaT_ftyp c a k s p_c_aks t p_emp_t = case p_c_aks of
  (FTPrm FEmpty _c) -> case c of 
    (Eql)            -> case (erase t) of 
      (FTBasic TBool) -> FTPrm FEmpty Eqv ? toProof (
                             ftsubBV 1 (FTBasic TBool) (FTFunc (FTBasic (BTV 1)) 
                                     (FTFunc (FTBasic (BTV 1)) (FTBasic TBool)))
                         === (FTFunc (ftsubBV 1 (FTBasic TBool) (FTBasic (BTV 1)))
                               (ftsubBV 1 (FTBasic TBool) (FTFunc (FTBasic (BTV 1)) (FTBasic TBool))))
                         === (FTFunc (FTBasic TBool) 
                               (FTFunc (FTBasic TBool) (FTBasic TBool))) )
      (FTBasic TInt)  -> FTPrm FEmpty Eq  ? toProof (
                             ftsubBV 1 (FTBasic TInt) (FTFunc (FTBasic (BTV 1)) 
                                     (FTFunc (FTBasic (BTV 1)) (FTBasic TBool)))
                         === (FTFunc (ftsubBV 1 (FTBasic TInt) (FTBasic (BTV 1)))
                               (ftsubBV 1 (FTBasic TInt) (FTFunc (FTBasic (BTV 1)) (FTBasic TBool))))
                         === (FTFunc (FTBasic TInt) 
                               (FTFunc (FTBasic TInt) (FTBasic TBool))) )
      _               -> impossible ("by lemma" ? lem_base_types (erase t) p_emp_t)
