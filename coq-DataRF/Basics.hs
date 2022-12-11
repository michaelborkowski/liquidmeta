{-@ measure fv @-} 
{-@ fv :: e:Expr -> S.Set Vname / [esize e] @-}
fv :: Expr -> S.Set Vname
fv (C  _)          = S.empty
fv (BV _)          = S.empty
fv (FV x)          = S.singleton x
fv (Lambda   e)    = fv e 
fv (App e e')      = S.union (fv e) (fv e')
fv (LambdaT   k e) = fv e
fv (AppT e t)      = S.union (fv e) (free t)
fv (Let   ex e)    = S.union (fv ex) (fv e)
fv (Annot e t)     = S.union (fv e) (free t) 
fv (Switch e cs)   = S.union (fv e) (fvA cs)

{-@ measure fvList @-} 
{-@ fvList :: e:Expr -> { xs:Names | listElts xs == fv e } / [esize e] @-}
fvList :: Expr -> Names
fvList (C  _)          = []
fvList (BV _)          = []
fvList (FV x)          = [x]
fvList (Lambda   e)    = fvList e 
fvList (App e e')      = union (fvList e) (fvList e')
fvList (LambdaT   k e) = fvList e
fvList (AppT e t)      = union (fvList e) (freeList t)
fvList (Let   ex e)    = union (fvList ex) (fvList e)
fvList (Annot e t)     = union (fvList e) (freeList t) 
fvList (Switch e cs)   = union (fvList e) (fvAList cs) 

{-@ measure ftv @-}
{-@ ftv :: e:Expr -> S.Set Vname / [esize e] @-}
ftv :: Expr -> S.Set Vname
ftv (C  _)          = S.empty
ftv (BV _)          = S.empty
ftv (FV x)          = S.empty -- differs from fv
ftv (Lambda   e)    = ftv e 
ftv (App e e')      = S.union (ftv e) (ftv e')
ftv (LambdaT   k e) = ftv e
ftv (AppT e t)      = S.union (ftv e) (freeTV t)
ftv (Let   ex e)    = S.union (ftv ex) (ftv e) 
ftv (Annot e t)     = S.union (ftv e) (freeTV t) -- fv e
ftv (Switch e cs)   = S.union (ftv e) (ftvA cs) 

  ---  Alternatives (Cases inside a Switch)

{-@ measure fvA @-}
{-@ fvA :: ps:Alts -> S.Set Vname / [asize ps] @-}
fvA :: Alts -> S.Set Vname
fvA AEmpty          = S.empty
fvA (ACons dc e as) = S.union (fv e) (fvA as)

{-@ measure fvAList @-}
{-@ fvAList :: ps:Alts -> { xs:Names | listElts xs == fvA ps } / [asize ps] @-}
fvAList :: Alts -> Names
fvAList AEmpty          = []
fvAList (ACons dc e as) = union (fvList e) (fvAList as)

{-@ measure ftvA @-}
{-@ ftvA :: ps:Alts -> S.Set Vname / [asize ps] @-}
ftvA :: Alts -> S.Set Vname
ftvA AEmpty          = S.empty
ftvA (ACons dc e as) = S.union (ftv e) (ftvA as)
  
  ---  Refinements

{-@ measure fvP @-}
{-@ fvP :: ps:Preds -> S.Set Vname / [predsize ps] @-}
fvP :: Preds -> S.Set Vname
fvP PEmpty       = S.empty
fvP (PCons p ps) = S.union (fv p) (fvP ps)

{-@ measure fvPList @-}
{-@ fvPList :: ps:Preds -> { xs:Names | listElts xs == fvP ps } / [predsize ps] @-}
fvPList :: Preds -> Names
fvPList PEmpty       = []
fvPList (PCons p ps) = union (fvList p) (fvPList ps)

{-@ measure ftvP @-}
{-@ ftvP :: ps:Preds -> S.Set Vname / [predsize ps] @-}
ftvP :: Preds -> S.Set Vname
ftvP PEmpty       = S.empty
ftvP (PCons p ps) = S.union (ftv p) (ftvP ps)

  ---   TYPES

{-@ measure free @-} -- free TERM variables
{-@ free :: t:Type -> S.Set Vname / [tsize t] @-}
free :: Type -> S.Set Vname
free (TRefn b   rs)     = case b of
  (TData tc t) -> S.union (free t) (fvP rs)
  _            -> fvP rs
free (TFunc   t_x t)    = S.union (free t_x) (free t) 
free (TExists   t_x t)  = S.union (free t_x) (free t) 
free (TPoly   k   t)    = free t

{-@ measure freeTV @-} -- free TYPE variables
{-@ freeTV :: t:Type -> S.Set Vname / [tsize t] @-}
freeTV :: Type -> S.Set Vname
freeTV (TRefn b   r)      = case b of 
  (TData tc t) -> S.union (freeTV t)      (ftvP r)
  (FTV a)      -> S.union (S.singleton a) (ftvP r)
  _            -> ftvP r
freeTV (TFunc   t_x t)    = S.union (freeTV t_x) (freeTV t) 
freeTV (TExists   t_x t)  = S.union (freeTV t_x) (freeTV t) 
freeTV (TPoly   k   t)    = freeTV t

---------------------------------------------------------------------------
----- | SYNTAX, continued
---------------------------------------------------------------------------


{-@ reflect isJust @-}
isJust :: Maybe a -> Bool
isJust Nothing  = False
isJust (Just _) = True

{-
{-@ reflect ty_dc @-}
ty_dc dcid tcid = ....

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty         = S.empty
binds (Cons x t g)  = S.union (S.singleton x) (binds g)
binds (ConsT a k g) = S.union (S.singleton a) (binds g)

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty         = S.empty
binds (Cons x t g)  = S.union (S.singleton x) (binds g)
binds (ConsT a k g) = S.union (S.singleton a) (binds g)
-}
  --- TYPING ENVIRONMENTS ---

data Env = Empty                         -- type Env = [(Vname, Type) or Vname]
         | Cons  Vname Type Env          
         | ConsT Vname Kind Env
--  deriving (Show)
{-@ data Env where 
        Empty :: Env 
        Cons  :: x:Vname -> t:Type -> { g:Env | not (in_env x g) } 
                         -> { g':Env | binds g'   == Set_cup (Set_sng x)  (binds g) &&
                                       vbinds g'  == Set_cup (Set_sng x) (vbinds g) &&
                                       tvbinds g' == tvbinds g &&
                                       Set_cup (vbinds g') (tvbinds g') == binds g' &&
                                       Set_emp (Set_cap (vbinds g') (tvbinds g')) } 
        ConsT :: a:Vname -> k:Kind -> { g:Env | not (in_env a g) } 
                         -> { g':Env | binds g'   == Set_cup (Set_sng a)   (binds g) &&
                                       vbinds g'  == vbinds g &&
                                       tvbinds g' == Set_cup (Set_sng a) (tvbinds g) &&
                                       Set_cup (vbinds g') (tvbinds g') == binds g' &&
                                       Set_emp (Set_cap (vbinds g') (tvbinds g')) }  @-}

{-@ measure envsize @-}
{-@ envsize :: Env -> { n:Int | n >= 0 } @-}
envsize :: Env -> Int
envsize Empty         = 0
envsize (Cons  _ _ g) = envsize g + 1
envsize (ConsT _ _ g) = envsize g + 1

{-@ reflect max @-}
max :: Int -> Int -> Int
max x y = if x >= y then x else y

{-@ reflect in_env @-}              -- any kind of variable
in_env :: Vname -> Env -> Bool
in_env x g = S.member x (binds g) 

{-@ reflect bound_in @-}            -- term variables only
bound_in :: Vname -> Type -> Env -> Bool
bound_in x t Empty                                 = False
bound_in x t (Cons y t' g) | (x == y)              = (t == t')
                           | otherwise             = bound_in x t g
bound_in x t (ConsT a k g) | (x == a)              = False
                           | otherwise             = bound_in x t g

{-@ reflect tv_bound_in @-}         -- type variables only
tv_bound_in :: Vname -> Kind -> Env -> Bool
tv_bound_in a k Empty                                   = False
tv_bound_in a k (Cons x t g)    | (a == x)              = False
                                | otherwise             = tv_bound_in a k g
tv_bound_in a k (ConsT a' k' g) | (a == a')             = (k == k')
                                | otherwise             = tv_bound_in a k g

{-@ reflect kind_for_tv @-}
{-@ kind_for_tv :: a:Vname -> { g:Env | Set_mem a (tvbinds g) } 
                           -> { k:Kind | tv_bound_in a k g } @-}
kind_for_tv :: Vname -> Env -> Kind
kind_for_tv a (Cons  x  t  g)             = kind_for_tv a g
kind_for_tv a (ConsT a' k' g) | (a == a') = k'
                              | otherwise = kind_for_tv a g

{-@ reflect binds @-}
binds :: Env -> S.Set Vname
binds Empty         = S.empty
binds (Cons x t g)  = S.union (S.singleton x) (binds g)
binds (ConsT a k g) = S.union (S.singleton a) (binds g)

{-@ reflect v_in_env @-}              -- (term) variables
v_in_env :: Vname -> Env -> Bool
v_in_env x g = S.member x (vbinds g) 

{-@ reflect vbinds @-}
{-@ vbinds :: g:Env -> { s:S.Set Vname | Set_sub s (binds g) } @-}
vbinds :: Env -> S.Set Vname
vbinds Empty         = S.empty
vbinds (Cons x t g)  = S.union (S.singleton x) (vbinds g)
vbinds (ConsT a k g) = vbinds g

{-@ reflect tv_in_env @-}              -- type variables
tv_in_env :: Vname -> Env -> Bool
tv_in_env x g = S.member x (tvbinds g) 

{-@ reflect tvbinds @-}
{-@ tvbinds :: g:Env -> { s:S.Set Vname | Set_sub s (binds g) } @-}
tvbinds :: Env -> S.Set Vname
tvbinds Empty         = S.empty
tvbinds (Cons x t g)  = tvbinds g
tvbinds (ConsT a k g) = S.union (S.singleton a) (tvbinds g)

{-@ lem_binds_invariants :: g:Env -> { pf:_ | Set_cup (vbinds g) (tvbinds g) == binds g &&
                                              Set_emp (Set_cap (vbinds g) (tvbinds g)) } @-}
lem_binds_invariants :: Env -> Proof
lem_binds_invariants Empty           = ()
lem_binds_invariants (Cons x t_x g)  = () ? lem_binds_invariants g
lem_binds_invariants (ConsT a k_a g) = () ? lem_binds_invariants g


  -- BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
  --    but all the refinements, dependent arrow binders, and existentials have been erased.
{-@ data FType where
         FTBasic :: { b:Basic | not (isData b) } -> FType
         FTData  :: TCons -> FType -> FType
         FTFunc  :: FType -> FType -> FType
         FTPoly  :: Kind  -> FType -> FType        @-}

data FType = FTBasic Basic          -- b: Bool, Int, FTV a, BTV a, but not TData...
           | FTData TCons FType
           | FTFunc FType FType     -- bt -> bt'
           | FTPoly Kind  FType     -- \forall a:k. bt 
  deriving Eq

{-@ measure ftsize @-}
{-@ ftsize :: t:FType -> { v:Int | v >= 0 } @-} 
ftsize :: FType -> Int
ftsize (FTBasic b)      = 1
ftsize (FTData tc    t) = (ftsize t)   + 1
ftsize (FTFunc t_x   t) = (ftsize t_x) + (ftsize t) + 1
ftsize (FTPoly    k  t) = (ftsize t)   + 1

{-@ measure arrowsF @-}
{-@ arrowsF :: t:FType -> { v:Int | v >= 0 } @-}
arrowsF :: FType -> Int
arrowsF (FTFunc t_x t) = (arrowsF t) + 1
arrowsF _              = 0

{-@ measure isFTData @-}
isFTData :: FType -> Bool
isFTData (FTData _ _) = True
isFTData _            = False

--{-@ measure isBaseF @-}
--isBaseF :: FType -> Bool
--isBaseF (FTBasic b)     = True
--isBaseF _               = False

{-@ reflect erase @-}
erase :: Type -> FType
erase (TRefn b r)     = case b of 
  TBool        -> FTBasic TBool
  TInt         -> FTBasic TInt
  (BTV i)      -> FTBasic (BTV i)
  (FTV a)      -> FTBasic (FTV a)
  (TData tc t) -> FTData tc (erase t)
erase (TFunc t_x t)   = FTFunc (erase t_x) (erase t)
erase (TExists t_x t) = (erase t)
erase (TPoly  k  t)   = FTPoly k (erase t)

-- there are no term vars in a Bare Type, only type ones
{-@ measure ffreeTV @-} 
{-@ ffreeTV :: t:FType -> S.Set Vname / [ftsize t] @-}
ffreeTV :: FType -> S.Set Vname
ffreeTV (FTBasic b)      = case b of
  (FTV a)                   -> S.singleton a
  _                         -> S.empty
ffreeTV (FTData tc t)    = ffreeTV t
ffreeTV (FTFunc t_x t)   = S.union (ffreeTV t_x) (ffreeTV t) 
ffreeTV (FTPoly   k t)   = ffreeTV t

{-@ measure ffreeTVList @-}
{-@ ffreeTVList :: t:FType -> { xs:Names | listElts xs == ffreeTV t } @-}
ffreeTVList :: FType -> Names
ffreeTVList (FTBasic b)     = case b of
  (FTV a)                      -> [a]
  _                            -> []
ffreeTVList (FTData tc t)   = ffreeTVList t
ffreeTVList (FTFunc t_x t)  = union (ffreeTVList t_x)  (ffreeTVList t)
ffreeTVList (FTPoly   k t)  = ffreeTVList t

{-@ reflect isLCFT @-}
isLCFT :: FType -> Bool
isLCFT t = isLCFT_at 0 t

{-@ reflect isLCFT_at @-} 
isLCFT_at :: Index -> FType -> Bool
isLCFT_at j (FTBasic b)      = case b of
  (BTV i)                   -> i < j
  _                         -> True
isLCFT_at j (FTData tc t)    = isLCFT_at j t
isLCFT_at j (FTFunc t_x t)   = isLCFT_at j t_x && isLCFT_at j t
isLCFT_at j (FTPoly   k t)   = isLCFT_at (j+1) t

{-@ reflect unbindFT @-}
{-@ unbindFT :: a':Vname -> t:FType 
                       -> { t':FType | Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       Set_sub (ffreeTV t) (ffreeTV t') &&
                                       ftsize t == ftsize t' } / [ftsize t] @-} 
unbindFT :: Vname -> FType -> FType
unbindFT a' t = openFT_at 0 a' t

{-@ reflect openFT_at @-}
{-@ openFT_at :: j:Index -> a':Vname -> t:FType
                       -> { t':FType | Set_sub (ffreeTV t') (Set_cup (Set_sng a') (ffreeTV t)) &&
                                       Set_sub (ffreeTV t) (ffreeTV t') &&
                                       ftsize t == ftsize t' } / [ftsize t] @-} 
openFT_at :: Index -> Vname -> FType -> FType
openFT_at j a' (FTBasic b)    = case b of
  (BTV i) | i == j  -> FTBasic (FTV a')
  _                 -> FTBasic b
openFT_at j a' (FTData tc  t) = FTData tc (openFT_at j a' t)
openFT_at j a' (FTFunc t_x t) = FTFunc (openFT_at j a' t_x) (openFT_at j a' t)
openFT_at j a' (FTPoly k   t) = FTPoly k (openFT_at (j+1) a' t)

-- System F substituion is simpler because there are no refinements to worry about, so we can just
--   do a single substitution instead of both a variable replacement t[a'/a] and a refinment-streng.
--   substitution t[a:=t_a]
{-@ reflect ftsubFV @-}
{-@ ftsubFV :: a:Vname -> t_a:FType -> t:FType  
         -> { t':FType | ( Set_mem a (ffreeTV t) || t == t' ) && 
                ( Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (Set_dif (ffreeTV t) (Set_sng a))) ) &&
                ( (not (Set_mem a (ffreeTV t_a))) => not (Set_mem a (ffreeTV t')) ) } / [ftsize t] @-}
ftsubFV :: Vname -> FType -> FType -> FType
ftsubFV a t_a (FTBasic b)           = case b of 
  (FTV a') | a == a'                    -> t_a
  _                                     -> FTBasic b
ftsubFV a t_a (FTData tc  t)        = FTData tc (ftsubFV a t_a t)
ftsubFV a t_a (FTFunc t_z t)        = FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
ftsubFV a t_a (FTPoly   k t)        = FTPoly k (ftsubFV a t_a t)

{-@ reflect ftsubBV @-} 
{-@ ftsubBV :: t_a:FType -> t:FType  
        -> { t':FType | Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) &&
                        ( ftsize t_a != 1 || ftsize t == ftsize t' ) } / [ftsize t] @-}
ftsubBV :: FType -> FType -> FType
ftsubBV t_a t = ftsubBV_at 0 t_a t

{-@ reflect ftsubBV_at @-} 
{-@ ftsubBV_at :: Index -> t_a:FType -> t:FType  
        -> { t':FType | Set_sub (ffreeTV t') (Set_cup (ffreeTV t_a) (ffreeTV t)) &&
                        ( ftsize t_a != 1 || ftsize t == ftsize t' ) } / [ftsize t] @-}
ftsubBV_at :: Index -> FType -> FType -> FType
ftsubBV_at j t_a (FTBasic   b)      = case b of 
  (BTV i) | i == j                    -> t_a
  _                                   -> FTBasic b
ftsubBV_at j t_a (FTData tc  t)     = FTData tc (ftsubBV_at j t_a t)
ftsubBV_at j t_a (FTFunc t_z t)     = FTFunc (ftsubBV_at j t_a t_z) (ftsubBV_at j t_a t)
ftsubBV_at j t_a (FTPoly  k  t)     = FTPoly k (ftsubBV_at (j+1) t_a t)
 

  --- BARE-TYPING ENVIRONMENTS

data FEnv = FEmpty                       -- type FEnv = [(Vname, FType) or Vname]
          | FCons  Vname FType FEnv
          | FConsT Vname Kind  FEnv
--  deriving (Show) 
{-@ data FEnv where
        FEmpty :: FEnv
        FCons  :: x:Vname -> t:FType -> { g:FEnv | not (in_envF x g) } 
                          -> { g':FEnv | bindsF g'   == Set_cup (Set_sng x)  (bindsF g) &&
                                         vbindsF g'  == Set_cup (Set_sng x) (vbindsF g) &&
                                         tvbindsF g' == tvbindsF g &&
                                         Set_cup (vbindsF g') (tvbindsF g') == bindsF g' &&
                                         Set_emp (Set_cap (vbindsF g') (tvbindsF g')) }
        FConsT :: a:Vname -> k:Kind  -> { g:FEnv | not (in_envF a g) } 
                          -> { g':FEnv | bindsF g'   == Set_cup (Set_sng a)   (bindsF g) &&
                                         vbindsF g'  == vbindsF g &&
                                         tvbindsF g' == Set_cup (Set_sng a) (tvbindsF g) &&
                                         Set_cup (vbindsF g') (tvbindsF g') == bindsF g' &&
                                         Set_emp (Set_cap (vbindsF g') (tvbindsF g')) } @-}

{-@ measure fenvsize @-}
{-@ fenvsize :: FEnv -> { n:Int | n >= 0 } @-}
fenvsize :: FEnv -> Int
fenvsize FEmpty         = 0
fenvsize (FCons  _ _ g) = fenvsize g + 1
fenvsize (FConsT _ _ g) = fenvsize g + 1

{-@ reflect in_envF @-}
in_envF :: Vname -> FEnv -> Bool
in_envF x g = S.member x (bindsF g) 

{-@ reflect lookupF @-}
{- @ lookupF :: x:Vname -> g:FEnv -> { mt:Maybe FType | (mt == Just t) => bound_inF x t g } @-}
lookupF :: Vname -> FEnv -> Maybe FType
lookupF x FEmpty                      = Nothing
lookupF x (FCons  y t g) | x == y     = Just t
                         | otherwise  = lookupF x g
lookupF x (FConsT a k g) | x == a     = Nothing
                         | otherwise  = lookupF x g

{-@ reflect bound_inF @-}
{- @ bound_inF :: x:Vname -> t:FType -> g:FEnv 
        -> { b:Bool | (not b || in_envF x g) && (lookupF x g == Just t => bound_inF x t g)} @-}
bound_inF :: Vname -> FType -> FEnv -> Bool
bound_inF x t FEmpty                                  = False
bound_inF x t (FCons  y t' g) | (x == y)              = (t == t')
                              | otherwise             = bound_inF x t g
bound_inF x t (FConsT a k  g) | (x == a)              = False
                              | otherwise             = bound_inF x t g

{-@ reflect tv_bound_inF @-}         -- type variables only
tv_bound_inF :: Vname -> Kind -> FEnv -> Bool
tv_bound_inF a k FEmpty                                   = False
tv_bound_inF a k (FCons x t g)    | (a == x)              = False
                                  | otherwise             = tv_bound_inF a k g
tv_bound_inF a k (FConsT a' k' g) | (a == a')             = (k == k')
                                  | otherwise             = tv_bound_inF a k g

{-@ reflect kind_for_tvF @-}
{-@ kind_for_tvF :: a:Vname -> { g:FEnv | Set_mem a (tvbindsF g) } 
                            -> { k:Kind | tv_bound_inF a k g } @-}
kind_for_tvF :: Vname -> FEnv -> Kind
kind_for_tvF a (FCons  x  t  g)             = kind_for_tvF a g
kind_for_tvF a (FConsT a' k' g) | (a == a') = k'
                                | otherwise = kind_for_tvF a g

{-@ lem_lookup_boundinF :: x:Vname -> t:FType -> { g:FEnv | lookupF x g == Just t }
        -> { pf:_ | bound_inF x t g } @-}
lem_lookup_boundinF :: Vname -> FType -> FEnv -> Proof
lem_lookup_boundinF x t (FCons  y s g) | x == y    = ()
                                       | otherwise = lem_lookup_boundinF x t g
lem_lookup_boundinF x t (FConsT a k g) | x == a    = impossible ""
                                       | otherwise = lem_lookup_boundinF x t g

{-@ lem_boundin_inenvF :: x:Vname -> t:FType -> { g:FEnv | bound_inF x t g}
        -> { pf:_ | in_envF x g } @-}
lem_boundin_inenvF :: Vname -> FType -> FEnv -> Proof
lem_boundin_inenvF x t (FCons y s g)  | x == y    = ()
                                      | otherwise = lem_boundin_inenvF x t g 
lem_boundin_inenvF x t (FConsT a k g) | x == a    = impossible ""
                                      | otherwise = lem_boundin_inenvF x t g 

{-@ lem_tvboundin_inenvF :: a:Vname -> k:Kind -> { g:FEnv | tv_bound_inF a k g}
        -> { pf:_ | in_envF a g } @-}
lem_tvboundin_inenvF :: Vname -> Kind -> FEnv -> Proof
lem_tvboundin_inenvF a k (FCons y s g)    | a == y    = impossible ""
                                          | otherwise = lem_tvboundin_inenvF a k g 
lem_tvboundin_inenvF a k (FConsT a' k' g) | a == a'   = ()
                                          | otherwise = lem_tvboundin_inenvF a k g 

{-@ reflect bindsF @-}
bindsF :: FEnv -> S.Set Vname
bindsF FEmpty         = S.empty
bindsF (FCons  x t g) = S.union (S.singleton x) (bindsF g)
bindsF (FConsT a k g) = S.union (S.singleton a) (bindsF g)

{-@ reflect vbindsF @-}
{-@ vbindsF :: g:FEnv -> { s:S.Set Vname | Set_sub s (bindsF g) } @-}
vbindsF :: FEnv -> S.Set Vname
vbindsF FEmpty         = S.empty
vbindsF (FCons x t g)  = S.union (S.singleton x) (vbindsF g)
vbindsF (FConsT a k g) = vbindsF g

{-@ reflect tvbindsF @-}
{-@ tvbindsF :: g:FEnv -> { s:S.Set Vname | Set_sub s (bindsF g) } @-}
tvbindsF :: FEnv -> S.Set Vname
tvbindsF FEmpty         = S.empty
tvbindsF (FCons x t g)  = tvbindsF g
tvbindsF (FConsT a k g) = S.union (S.singleton a) (tvbindsF g)

{-@ reflect erase_env @-}
{-@ erase_env :: g:Env -> { g':FEnv | binds g == bindsF g' && vbinds g == vbindsF g' 
                                                           && tvbinds g == tvbindsF g'} @-}
erase_env :: Env -> FEnv
erase_env Empty         = FEmpty
erase_env (Cons  x t g) = FCons  x (erase t) (erase_env g)
erase_env (ConsT a k g) = FConsT a k         (erase_env g)

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
----- | NAME SETS and FRESH NAMES
---------------------------------------------------------------------------

type Names = [Vname]   -- for cofinite quantification over free names

{-@ predicate IsCup     X Y Z  = listElts X = Set_cup (listElts Y) (listElts Z) @-}
{-@ predicate IsCupEnv  X Y Z  = listElts X = Set_cup (listElts Y) (binds Z)    @-}
{-@ predicate IsCupFEnv X Y Z  = listElts X = Set_cup (listElts Y) (bindsF Z)   @-}
{-@ predicate Elem  X Ys   = Set_mem X (listElts Ys)                            @-}
{-@ predicate NotElem X Ys = not (Elem X Ys)                                    @-}
{-@ predicate Disjoint  Xs Ys  = Set_emp (Set_cap (listElts Xs) (listElts Ys))  @-}

{-@ reflect union @-}
{-@ union :: ys:Names -> zs:Names -> { xs:Names | IsCup xs ys zs } @-}
union :: Names -> Names -> Names
union xs []         = xs
union xs (y:ys)     = y : (union xs ys)

{-@ unionEnv :: ys:Names -> zs:Env -> { xs:Names | IsCupEnv xs ys zs } @-}
unionEnv :: Names -> Env -> Names
unionEnv xs Empty         = xs
unionEnv xs (Cons  x t g) = x : (unionEnv xs g)
unionEnv xs (ConsT a k g) = a : (unionEnv xs g)

{-@ unionFEnv :: ys:Names -> zs:FEnv -> { xs:Names | IsCupFEnv xs ys zs } @-}
unionFEnv :: Names -> FEnv -> Names
unionFEnv xs FEmpty         = xs
unionFEnv xs (FCons  x t g) = x : (unionFEnv xs g)
unionFEnv xs (FConsT a k g) = a : (unionFEnv xs g)

{-@ fresh :: xs:Names -> { v:Vname | NotElem v xs } @-}
fresh :: Names -> Vname
fresh bs = n `withProof` lem_above_max_fresh n bs
  where
    n    = 1 + maxs bs

{-@ reflect maxs @-}
{-@ maxs :: xs:_ -> {v:_ | v = maxs xs && v >= 0} @-}
maxs :: Names -> Vname
maxs ([])   = 0
maxs (x:xs) = if (x > maxs xs) then x else (maxs xs)

{-@ lem_above_max_fresh :: x:Vname -> xs:{Names | x > maxs xs} -> { pf:_ | NotElem x xs} @-}
lem_above_max_fresh :: Vname -> Names -> Proof
lem_above_max_fresh _ []     = ()
lem_above_max_fresh x (_:ys) = lem_above_max_fresh x ys

{-@ fresh_var :: xs:Names -> g:Env -> { x:Vname | not (in_env x g) && NotElem x xs } @-}
fresh_var :: Names -> Env -> Vname
fresh_var xs g = n `withProof` lem_above_max_nms_env n xs g
  where
    n    = 1 + max_nms_env xs g

{-@ fresh_var_excluding :: xs:Names -> g:Env -> x:Vname 
                -> { y:Vname | not (in_env y g) && y != x && NotElem y xs } @-}
fresh_var_excluding :: Names -> Env -> Vname -> Vname
fresh_var_excluding xs g x = if in_env x g then fresh_var xs g
                                 else fresh_var xs (Cons x (TRefn TBool PEmpty) g)

{-@ reflect max_nms_env @-}
{-@ max_nms_env :: Names -> Env -> { x:Vname | x >= 0 } @-}
max_nms_env :: Names -> Env -> Vname 
max_nms_env ([])   Empty         = 0
max_nms_env ([])   (Cons  x t g) = if (x > max_nms_env [] g) then x else (max_nms_env [] g)
max_nms_env ([])   (ConsT a k g) = if (a > max_nms_env [] g) then a else (max_nms_env [] g)
max_nms_env (x:xs) g             = if (x > max_nms_env xs g) then x else (max_nms_env xs g)

{-@ lem_above_max_nms_env :: x:Vname -> xs:Names -> { g:Env | x > max_nms_env xs g } 
                                      -> { pf:_ | NotElem x xs && not (in_env x g) } @-}
lem_above_max_nms_env :: Vname -> Names -> Env -> Proof
lem_above_max_nms_env _ []     Empty         = ()
lem_above_max_nms_env x []     (Cons  y t g) = lem_above_max_nms_env x [] g
lem_above_max_nms_env x []     (ConsT a k g) = lem_above_max_nms_env x [] g
lem_above_max_nms_env x (_:ys) g             = lem_above_max_nms_env x ys g


{-@ fresh_varF :: xs:Names -> g:FEnv -> { x:Vname | not (in_envF x g) && NotElem x xs } @-}
fresh_varF :: Names -> FEnv -> Vname
fresh_varF xs g = n `withProof` lem_above_max_nms_fenv n xs g
  where
    n    = 1 + max_nms_fenv xs g

{-@ fresh_var_excludingF :: xs:Names -> g:FEnv -> x:Vname 
                -> { y:Vname | not (in_envF y g) && y != x && NotElem y xs } @-}
fresh_var_excludingF :: Names -> FEnv -> Vname -> Vname
fresh_var_excludingF xs g x = if in_envF x g then fresh_varF xs g
                                 else fresh_varF xs (FCons x (FTBasic TBool) g)

{-@ reflect max_nms_fenv @-}
{-@ max_nms_fenv :: Names -> FEnv -> { x:Vname | x >= 0 } @-}
max_nms_fenv :: Names -> FEnv -> Vname 
max_nms_fenv ([])   FEmpty         = 0
max_nms_fenv ([])   (FCons  x t g) = if (x > max_nms_fenv [] g) then x else (max_nms_fenv [] g)
max_nms_fenv ([])   (FConsT a k g) = if (a > max_nms_fenv [] g) then a else (max_nms_fenv [] g)
max_nms_fenv (x:xs) g              = if (x > max_nms_fenv xs g) then x else (max_nms_fenv xs g)

{-@ lem_above_max_nms_fenv :: x:Vname -> xs:Names -> { g:FEnv | x > max_nms_fenv xs g } 
                                      -> { pf:_ | NotElem x xs && not (in_envF x g) } @-}
lem_above_max_nms_fenv :: Vname -> Names -> FEnv -> Proof
lem_above_max_nms_fenv _ []     FEmpty         = ()
lem_above_max_nms_fenv x []     (FCons  y t g) = lem_above_max_nms_fenv x [] g
lem_above_max_nms_fenv x []     (FConsT a k g) = lem_above_max_nms_fenv x [] g
lem_above_max_nms_fenv x (_:ys) g              = lem_above_max_nms_fenv x ys g


{-@ fresh_varT :: xs:Names -> g:Env -> t:Type 
        -> { x:Vname | not (Set_mem x (free t)) && not (in_env x g) && NotElem x xs } @-}
fresh_varT :: Names -> Env -> Type -> Vname
fresh_varT xs g t
  = n `withProof` lem_above_max_nms_type n xs (freeList t) g
      where
        n    = 1 + max_nms_type xs (freeList t) g

{-@ reflect max_nms_type @-}
{-@ max_nms_type :: Names -> Names -> Env -> { x:Vname | x >= 0 } @-}
max_nms_type :: Names -> Names -> Env -> Vname 
max_nms_type ([])   ([])   Empty         = 0
max_nms_type ([])   ([])   (Cons  x t g) 
  = if (x > max_nms_type [] [] g) then x else (max_nms_type [] [] g)
max_nms_type ([])   ([])   (ConsT a k g)
  = if (a > max_nms_type [] [] g) then a else (max_nms_type [] [] g)
max_nms_type ([])   (y:ys) g 
  = if (y > max_nms_type [] ys g) then y else (max_nms_type [] ys g)
max_nms_type (x:xs) ys     g 
  = if (x > max_nms_type xs ys g) then x else (max_nms_type xs ys g)

{-@ lem_above_max_nms_type :: x:Vname -> xs:Names -> ys:Names
        -> { g:Env | x > max_nms_type xs ys g } 
        -> { pf:_ | NotElem x xs && NotElem x ys && not (in_env x g) } @-}
lem_above_max_nms_type :: Vname -> Names -> Names -> Env -> Proof
lem_above_max_nms_type _ []     []     Empty         = ()
lem_above_max_nms_type x []     []     (Cons  y t g) = lem_above_max_nms_type x [] [] g
lem_above_max_nms_type x []     []     (ConsT a k g) = lem_above_max_nms_type x [] [] g
lem_above_max_nms_type x []     (_:ys) g             = lem_above_max_nms_type x [] ys g
lem_above_max_nms_type x (_:xs) ys     g             = lem_above_max_nms_type x xs ys g

{-@ fresh_varFTs :: xs:Names -> g:Env -> t1:FType -> t2:FType 
        -> { x:Vname | not (Set_mem x (ffreeTV t1)) && not (Set_mem x (ffreeTV t2)) && 
                       not (in_env x g)             && NotElem x xs } @-}
fresh_varFTs :: Names -> Env -> FType -> FType -> Vname
fresh_varFTs xs g t1 t2 
  = n `withProof` lem_above_max_nms_ftypes n xs (ffreeTVList t1) (ffreeTVList t2) g
      where
        n    = 1 + max_nms_ftypes xs (ffreeTVList t1) (ffreeTVList t2) g

{-@ reflect max_nms_ftypes @-}
{-@ max_nms_ftypes :: Names -> Names -> Names -> Env -> { x:Vname | x >= 0 } @-}
max_nms_ftypes :: Names -> Names -> Names -> Env -> Vname 
max_nms_ftypes ([])   ([])   ([])   Empty         = 0
max_nms_ftypes ([])   ([])   ([])   (Cons  x t g) 
  = if (x > max_nms_ftypes [] [] [] g) then x else (max_nms_ftypes [] [] [] g)
max_nms_ftypes ([])   ([])   ([])   (ConsT a k g)
  = if (a > max_nms_ftypes [] [] [] g) then a else (max_nms_ftypes [] [] [] g)
max_nms_ftypes ([])   ([])   (z:zs) g 
  = if (z > max_nms_ftypes [] [] zs g) then z else (max_nms_ftypes [] [] zs g)
max_nms_ftypes ([])   (y:ys) zs     g 
  = if (y > max_nms_ftypes [] ys zs g) then y else (max_nms_ftypes [] ys zs g)
max_nms_ftypes (x:xs) ys     zs     g 
  = if (x > max_nms_ftypes xs ys zs g) then x else (max_nms_ftypes xs ys zs g)

{-@ lem_above_max_nms_ftypes :: x:Vname -> xs:Names -> ys:Names -> zs:Names
        -> { g:Env | x > max_nms_ftypes xs ys zs g } 
        -> { pf:_ | NotElem x xs && NotElem x ys && NotElem x zs && not (in_env x g) } @-}
lem_above_max_nms_ftypes :: Vname -> Names -> Names -> Names -> Env -> Proof
lem_above_max_nms_ftypes _ []     []     []     Empty         = ()
lem_above_max_nms_ftypes x []     []     []     (Cons  y t g) 
  = lem_above_max_nms_ftypes x [] [] [] g
lem_above_max_nms_ftypes x []     []     []     (ConsT a k g) 
  = lem_above_max_nms_ftypes x [] [] [] g
lem_above_max_nms_ftypes x []     []     (_:zs) g = lem_above_max_nms_ftypes x [] [] zs g
lem_above_max_nms_ftypes x []     (_:ys) zs     g = lem_above_max_nms_ftypes x [] ys zs g
lem_above_max_nms_ftypes x (_:xs) ys     zs     g = lem_above_max_nms_ftypes x xs ys zs g

---------------------------------------------------------------------------
----- | PROPOSITIONS
---------------------------------------------------------------------------

  --- the Type of all Propositions

data Proposition where

    -- System F Judgments
    WFFT      :: FEnv -> Defs -> FType -> Kind -> Proposition    --  G,D |- t : k
    WFFE      :: FEnv -> Defs -> Proposition                     --  D   |- G
    HasFType  :: FEnv -> Defs -> Expr -> FType -> Proposition    --  G,D |- e : t
    AHasFType :: FEnv -> Defs -> Expr -> DDefns -> Alts 
                      -> FType -> Proposition                    --  G,D, e, dds |- als : t
    PHasFType :: FEnv -> Defs -> Preds -> Proposition            --  G,D |- ps : [FTBasic TBool]
                                                                 --  G,D | .... |- D -> e' : t
    -- System RF Judgments
    WFType    :: Env -> Defs -> Type -> Kind -> Proposition
    WFEnv     :: Env -> Defs -> Proposition
    HasType   :: Env -> Defs -> Expr -> Type -> Proposition -- HasType G D e t means G,D |- e : t
    AHasType  :: Env -> Defs -> Expr -> DDefns -> Alts -> Type -> Proposition
    Subtype   :: Env -> Defs -> Type -> Type -> Proposition
    Implies   :: Env -> Defs -> Preds -> Preds -> Proposition   --  G |= p => q   ???
