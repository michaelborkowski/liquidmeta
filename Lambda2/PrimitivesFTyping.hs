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
import SystemFTyping
import WellFormedness

{-@ reflect foo05 @-}
foo05 :: a -> Maybe a
foo05 x = Just x

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

{-@ reflect isPrim @-}
isPrim :: Expr -> Bool
isPrim (Prim _) = True
isPrim _        = False

{-@ lemma_function_values :: v:Value -> t:FType -> t':FType
        -> ProofOf(HasFType FEmpty v (FTFunc t t'))
        -> { pf:_ | isLambda v || isPrim v } @-}
lemma_function_values :: Expr -> FType -> FType -> HasFType -> Proof
lemma_function_values e t t' (FTPrm {})   = ()     
lemma_function_values e t t' (FTAbs {})   = ()    

{-@ lem_delta_and_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim And) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta And v) t' } @-} -- &&
lem_delta_and_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_and_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty And) -> case v of
          (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) (BV 1) (FTBasic TBool) 
                              1 (FTVar1 FEmpty 1 (FTBasic TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
          (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) (Bc False) (FTBasic TBool) 
                              1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) False)  
          _          -> impossible ("by lemma" ? lem_bool_values v p_v_tx) 


{-@ lem_delta_or_ftyp :: v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim Or) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta Or v) t' } @-} 
lem_delta_or_ftyp :: Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_or_ftyp v t_x t' p_c_txt' p_v_tx = case p_c_txt' of
  (FTPrm FEmpty Or) -> case v of
      (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) (Bc True) (FTBasic TBool)
                          1 (FTBC (FCons 1 (FTBasic TBool) FEmpty) True)
      (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) (BV 1)    (FTBasic TBool) 
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
      (Bc True)  -> FTAbs FEmpty 1 (FTBasic TBool) (BV 1) (FTBasic TBool)
                          1 (FTVar1 FEmpty 1 (FTBasic TBool) ) -- ? toProof ( unbind 1 1 (BV 1) === FV 1 ))
      (Bc False) -> FTAbs FEmpty 1 (FTBasic TBool) not_x  (FTBasic TBool) 1 p_notx_bl
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

{-@ lem_delta_ftyp :: c:Prim -> v:Value -> t_x:FType -> t':FType
        -> ProofOf(HasFType FEmpty (Prim c) (FTFunc t_x t')) -> ProofOf(HasFType FEmpty v t_x)
        -> { pf:_ | propOf pf == HasFType FEmpty (delta c v) t' } @-} -- &&
--                    not ((delta c v) == Crash) } @- }
lem_delta_ftyp :: Prim -> Expr -> FType -> FType -> HasFType -> HasFType -> HasFType
lem_delta_ftyp And      v t_x t' p_c_txt' p_v_tx = lem_delta_and_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Or       v t_x t' p_c_txt' p_v_tx = lem_delta_or_ftyp     v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Not      v t_x t' p_c_txt' p_v_tx = lem_delta_not_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eqv      v t_x t' p_c_txt' p_v_tx = lem_delta_eqv_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Leq      v t_x t' p_c_txt' p_v_tx = lem_delta_leq_ftyp    v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp (Leqn n) v t_x t' p_c_txt' p_v_tx = lem_delta_leqn_ftyp n v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp Eq       v t_x t' p_c_txt' p_v_tx = lem_delta_eq_ftyp     v t_x t' p_c_txt' p_v_tx
lem_delta_ftyp (Eqn n)  v t_x t' p_c_txt' p_v_tx = lem_delta_eqn_ftyp  n v t_x t' p_c_txt' p_v_tx
