{-@ reflect ty_dc @-}
ty_dc dcid tcid = ....

{-@ lem_erase_freeTV :: t:Type -> { pf:_ | Set_sub (ffreeTV (erase t)) (freeTV t) } @-}
lem_erase_freeTV :: Type -> Proof
lem_erase_freeTV (TRefn   b   p) = case b of
  (TData tc t)            -> lem_erase_freeTV t
  _                       -> ()
lem_erase_freeTV (TFunc   t_z t) =      lem_erase_freeTV t_z
                                      ? lem_erase_freeTV t
lem_erase_freeTV (TExists t_z t) =      lem_erase_freeTV t
lem_erase_freeTV (TPoly    k' t) =      lem_erase_freeTV t

---------------------------------------------------------------------------
----- | PROPOSITIONS
---------------------------------------------------------------------------

  --- the Type of all Propositions

data Proposition where

    -- System F Judgments
    HasFType  :: FEnv -> Defs -> Expr -> FType -> Proposition    --  G,D |- e : t
    AHasFType :: FEnv -> Defs -> Expr -> DDefns -> Alts 
                      -> FType -> Proposition                    --  G,D, e, dds |- als : t
    PHasFType :: FEnv -> Defs -> Preds -> Proposition            --  G,D |- ps : [FTBasic TBool]
                                                                 --  G,D | .... |- D -> e' : t
    -- System RF Judgments
    HasType   :: Env -> Defs -> Expr -> Type -> Proposition -- HasType G D e t means G,D |- e : t
    AHasType  :: Env -> Defs -> Expr -> DDefns -> Alts -> Type -> Proposition
    Subtype   :: Env -> Defs -> Type -> Type -> Proposition
    Implies   :: Env -> Defs -> Preds -> Preds -> Proposition   --  G |= p => q   ???
