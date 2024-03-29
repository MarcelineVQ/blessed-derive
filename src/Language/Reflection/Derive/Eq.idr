module Language.Reflection.Derive.Eq

import public Language.Reflection.Maps

import public Decidable.Equality

import public Data.Either -- partitionEithers

-- import Language.Reflection.Is

%language ElabReflection

%inline -- thank you ohad for this non-elab trick
||| MkDecEq isn't currently specificied in DecEq's definition, so we need to grab it ourselves.
MkDecEq : ((x : t) -> (y : t) -> Dec (x = y)) -> DecEq t
MkDecEq f = MkDecEq' {f}
  where %inline [MkDecEq'] {f : (x,y : t) -> Dec (x === y)} -> DecEq t where decEq = f
-- vs
MkDecEq' : ((x : t) -> (y : t) -> Dec (x = y)) -> DecEq t
MkDecEq' = %runElab do
  let decEqConName = `{Decidable.Equality.Core.DecEq} -- specific to reduce finding multiple DecEq
  [decEqCon] <- getCons decEqConName
    | _ => fail "Couldn't get DecEq constructor expected at \{show decEqConName}"
  check (var decEqCon)

-- Module is a mix of elab-util and Derive.Functor approaches.
-- I like elab-util's approach of generating the whole implementation and
-- constraints but I like Derive.Functor's approach of local declarations.
-- I'd like to find the best approach and then adopt that, removing my need
-- for elab-utils. It's very lovely library, I'd just like to reduce my
-- dependency footprint. Technically even contrib is probably too much given
-- how useful deriving is. Using SortedMap isn't really neccesary for fresh
-- vars, but it is prettty useful for renaming.

record ConstructorView where
  constructor MkConstructorView
  conName     : Name
  params      : List Name
  conArgTypes : List TTImp

record ArgView where
  constructor MkArgView
  name       : Maybe Name
  ty         : TTImp
  count      : Count
  isExplicit : Bool -- or should we just have the PiInfo and query with isExplicitArg?
-- %runElab deriveIs "PiInfo" Private


record ConstructorView' where
  constructor MkConstructorView'
  name    : Name
  params  : List Name
  conArgs : List ArgView

-- taken from gallais straightforward solution in Deriving.Functor
-- Note how he keeps the arg ttimps, useful for computing applications or pi content later
-- What's happening here is that we're walking along each arg in the constructor's type
-- `x -> ... -> end`
-- If it's implicit or auto we skip it, we add everything else as TTImp, when we get
-- to the end we examine the final type and extract its params. Note that this could
-- get quite interesting with indices involved.
-- I really like how { } is being used here as a function itself.
--------------------------------------------------
-- gallais is an endless source of useful code practices.
--------------------------------------------------
-- I would have done something dumb like:
-- (\(MkConstructorView n p c) => MkConstructorView n p (a :: c)) <$> explicits n b
-- which is already silly because I should write:
-- (\cv => { conArgTypes $= (a ::) } cv) <$> explicits n b
-- which is still more verbose than the nice:
-- { conArgTypes $= (a ::) } <$> explicits n b
export
explicits : Name -> TTImp -> Maybe ConstructorView
explicits n (IPi fc rig ExplicitArg x a b) = { conArgTypes $= (a ::) } <$> explicits n b
explicits n (IPi fc rig pinfo x a b) = explicits n b
explicits n f@(IApp _ _ _) = do
  MkAppView _ ts _ <- appView f
  let ps = flip mapMaybe ts $ \ t' => the (Maybe Name) $ case t' of
             Arg _ v@(IVar _ nm) => Just nm
             _ => Nothing
  pure (MkConstructorView n (ps <>> []) [])
explicits _ _ = Nothing

-- above, modified to handle explicit implicits.
-- We care about Count because a non-zero implicit is actually explicit.
-- Further we care about Count because a zero-explicit needs special handling during use.
-- flip confused the lambda type, so we've unflipped it
explicits' : Name -> TTImp -> Maybe ConstructorView'
explicits' n (IPi fc rig pi_info x a b) = case (rig,pi_info) of
  (M0, ExplicitArg) => { conArgs $= (MkArgView x a rig True ::) } <$> explicits' n b
  (M0, _) => explicits' n b
  (_, ExplicitArg) => { conArgs $= (MkArgView x a rig True ::) } <$> explicits' n b
  (_, ImplicitArg) => { conArgs $= (MkArgView x a rig False ::) } <$> explicits' n b
  _ => explicits' n b
explicits' n f@(IApp _ _ _) = do
  MkAppView _ ts _ <- appView f
  let ps = mapMaybe (\case (Arg _ v@(IVar _ nm)) => Just nm; _ => Nothing) ts
  pure (MkConstructorView' n (ps <>> []) [])
explicits' n f@(IVar _ _) = pure (MkConstructorView' n [] [])
explicits' _ _ = Nothing

patHead : String -> ConstructorView' -> TTImp
patHead varPre con = runFresh $ do
  args <- traverse (\a => pure (a, srcVarTo_Name' !(getNext varPre))) con.conArgs
  pure $ foldl (\acc,(a,n) => case a of
      MkArgView _ _ M0 _ => IApp EmptyFC acc `(_) -- explciit but M0
      MkArgView _ _ _ True => IApp EmptyFC acc (var n) -- explicit
      MkArgView n' _ _ False => INamedApp EmptyFC acc (fromMaybe "void" n') (var n)) -- explicit implicit
    (var con.name) args

patBod : String -> String -> (TTImp -> TTImp -> TTImp) -> ConstructorView' -> List TTImp
patBod varPre1 varPre2 fun con = runFresh $ do
  args1 <- traverse (\a => pure (a, srcVarTo_Name' !(getNext varPre1))) con.conArgs
  args2 <- traverse (\_ => pure (srcVarTo_Name' !(getNext varPre2))) con.conArgs
  pure $ foldr (\((a,n1),n2),acc => case a of
      MkArgView _ _ M0 _ => acc -- explciit but M0
      MkArgView _ _ _ _ => fun (var n1) (var n2) :: acc) -- explicit, or explicit implicit
    [] (zip args1 args2)

export
eqGen : Elab (Eq a)
eqGen = do
  Just (IApp _ (IVar fc `{Prelude.EqOrd.Eq}) t) <- goal
    | _ => fail "bad goal: expected form like, Eq a => Eq (Foo a)"
  Just appGoal <- pure $ appView t
    | _ => fail "goalNotAp"
  let paramSource = fromMaybe [] (params <$> (explicits (snd appGoal.head) t))
  consTT <- traverse lookupName !(getCons (snd appGoal.head))
  traverse_ (logTerm "" 1 "" . snd) consTT
  let consWithExplicits = fromMaybe [] $ traverse (uncurry explicits') consTT

  let implName' = "eqGenFun"
  let implName = var implName'

  -- differentiate params from indices, params will result in Type
  (params,indices) <- partitionEithers <$> (for paramSource $ \p => do
    (_,(IType _)) <- unPi <$> getLocalType p
      | _ => pure $ Right p
    pure $ Left p)
  -- traverse_ (logMsg "params" 1 . show) (the (List Name) params)
  -- traverse_ (logMsg "indices" 1 . show) (the (List Name) indices)

  let ty' = `( ~t -> ~t -> Bool)
  let ty = MkTy fc fc implName' $ piAllImplicit ty' indices

  -- pair each con with itself, if each used con argument is == then the pairing
  -- is True any other possibility is False
  let cls = (consWithExplicits <&> \c =>
        `(~implName ~(patHead "x" c) ~(patHead "y" c)) .=
          let apps@(_ :: _) = patBod "x" "y" (\x,y => `(~x == ~y)) c
            | _ => `(True) -- vacuously true if no args are used
          in foldr1 (\p,ps => `(~p && ~ps)) apps)
        ++ [`(~implName _ _) .= `(False)]
  logMsg "derive.eqGen.clauses" 1 $
    joinBy "\n" ("" :: ("  " ++ show ty)
                    :: map (("  " ++) . showClause InDecl) cls)

  check $ ILocal EmptyFC
    [ IClaim fc MW Private [] ty
    , IDef fc implName' cls
    ] `(MkEq {ty = ~(t)} (\x,y => ~implName x y) (\x,y => not (~implName x y)) )

data Bap : Type where
  MkBap : Int -> Bap
  MkBap2 : {b : Char} -> Int -> Bap

%hint
export
eqBap : Eq Bap
eqBap = %runElab eqGen

-- The assert_total is because idris thinks the tuples aren't covering
-- I'm not sure how they wouldn't be, so hopefully they're fine, as they avoid a ton of
-- nested cases here. Though I'm sure they're elaborated into them eventually.
conPairings : TTImp -> (ConstructorView, ConstructorView) -> Clause
conPairings implName (MkConstructorView n1 p1 ts1,MkConstructorView n2 p2 ts2) =
  if n1 == n2
    then runFresh $ do
      lvs <- traverse (\_ => var . srcVarTo_Name' <$> (getNext "x")) ts1
      rvs <- traverse (\_ => var . srcVarTo_Name' <$> (getNext "y")) ts1
      apps@(_ :: _) <- pure $ (zipWith (\l,r => `(~l `decEq` ~r)) lvs rvs)
        | _ => pure $ `(~implName ~(var n1) ~(var n1)) .= `(Yes Refl)
      pure $ `(~implName ~(appAll n1 lvs) ~(appAll n1 rvs)) .= `(assert_total) .$
        (iCase (foldr1 (\p,ps => `(MkPair ~p ~ps)) apps) implicitFalse $
          [ foldr1 (\p,ps => `(MkPair (Yes Refl) ~ps)) (map (const `(Yes Refl)) apps) .= `(Yes Refl)
          , foldr1 (\p,ps => `(MkPair ~p ~ps)) (`(No contra) :: drop 1 (map (const `(_)) apps)) .= `(No (\Refl => contra Refl))])
    else let lvs = map (const `(_)) ts1 -- no need for var names
             rvs = map (const `(_)) ts2
         in if (p1 == p2) -- if indices don't differ, use No
           then `(~implName ~(appAll n1 lvs) ~(appAll n2 rvs)) .= `(No (\case _ impossible))
           else impossibleClause `(~implName ~(appAll n1 lvs) ~(appAll n2 rvs))

export
decEqGen : Elab (DecEq a)
decEqGen = do
  Just (IApp _ (IVar fc `{Decidable.Equality.Core.DecEq}) t) <- goal
    | _ => fail "bad goal: expected form like, DecEq a => DecEq (Foo a)"
  Just appGoal <- pure $ appView t
    | _ => fail "goalNotAp"
  let paramSource = fromMaybe [] (params <$> (explicits (snd appGoal.head) t))
  consTT <- traverse lookupName !(getCons (snd appGoal.head))
  let consWithExplicits = fromMaybe [] $ traverse (uncurry explicits) consTT

  let implName' = "decEqGenFun"
  let implName = var implName'
  
  -- differentiate params from indices, params will result in Type
  (params,indices) <- partitionEithers <$> (for paramSource $ \p => do
    (_,(IType _)) <- unPi <$> getLocalType p
      | _ => pure $ Right p
    pure $ Left p)
  -- traverse_ (logMsg "params" 1 . show) (the (List Name) params)
  -- traverse_ (logMsg "indices" 1 . show) (the (List Name) indices)

  -- indices differ by case so we forall them so the sorrounding context doesn't affix them
  let ty' = `( (x : ~t) -> (y : ~t) -> Dec (x === y))
  let ty = MkTy fc fc implName' $ piAllImplicit ty' indices

  let cls = conPairings implName <$> [(x,y) | x <- consWithExplicits, y <- consWithExplicits]
  logMsg "derive.decEqGen.clauses" 1 $
    joinBy "\n" ("" :: ("  " ++ show ty)
                    :: map (("  " ++) . showClause InDecl) cls)

  check $ ILocal EmptyFC
    [ IClaim fc MW Private [] ty
    , IDef fc implName' cls
    ] `( MkDecEq {t = ~(t)} (\x,y => ~implName x y))

-- this tells me that further work is needed to determine 0 constructors with no
-- useable arguments for deceq
data Foo : Type -> (Type -> Type) -> Type -> Type where
  MkFoo1 : a -> Foo a f b
  MkFoo2 : b -> Foo a f b
  MkFoo3 : a -> b -> f a -> Foo a f b
  MkFoo4 : Foo a f b
  MkFoo5 : f a -> Foo a f b
  MkFoo6 : f (f b) -> Foo a f b
  MkFoo7 : (0 _ : f (f b)) -> Foo a f b -- TODO: not valid for DecEq :X What does this say about validity for Eq?
  MkFoo8 : {g : b} -> f (f b) -> Foo a f b -- TODO: not handled for DecEq yet
  MkFoo9 : {_ : b} -> f (f b) -> Foo a f b -- TODO: not handled for DecEq yet
  -- ^ how handle this? nvm, appearantly it's given a name in the compiler

%hint
eqImpTest : Eq a => Eq b => Eq (f a) => (Eq (f (f b))) => Eq (Foo a f b)
-- eqImpTest = %runElab eqGen

eqImpTest2 : Eq a => Eq (Vect n a)
-- eqImpTest2 = %runElab eqGen

-- this means we need to allow for Count annotation for instances as well
-- 0 decEq' : DecEq a => DecEq b => DecEq (f a) => (DecEq (f (f b))) => (x,y : Foo a f b) -> Dec (x = y)
-- decEq' (MkFoo7 x) (MkFoo7 y) = case decEq x y of
--   (Yes Refl) => Yes Refl
--   (No contra) => No $ \Refl => contra Refl
-- decEq' (MkFoo8 {g=g1} x) (MkFoo8 {g=g2} y) = case (decEq g1 g2, decEq x y) of
--   (Yes Refl,Yes Refl) => Yes Refl
--   (No contra,_) => No (\Refl => contra Refl)
-- decEq' (MkFoo7 x) (MkFoo8 y) = No (\case _ impossible)
-- decEq' (MkFoo8 x) (MkFoo7 y) = No (\case _ impossible)

-- [MkDecEq] {f : (x,y : a) -> Dec (x = y)} -> DecEq a where
--   decEq = f

-- %hint 0
-- ErasedDecEq : DecEq a => DecEq (FooA a)
-- ErasedDecEq = MkDecEq {f = decEq'}

-- {0 baf : DecEq (f (f b))} -> DecEq b => DecEq (Foo a f b) where
  -- decEq (MkFoo7 x) (MkFoo7 y) = Yes $ decEq @{baf} x y
  -- decEq (MkFoo8 {g=x0} x) (MkFoo8 {g=y0} y) = assert_total $ case (decEq x0 y0, decEq x y) of
  --   (Yes Refl,Yes Refl) => Yes Refl
  --   (No contra,_) => No (\Refl => contra Refl)
  -- decEq (MkFoo7 x) (MkFoo8 y) = No (\case _ impossible)
  -- decEq (MkFoo8 x) (MkFoo7 y) = No (\case _ impossible)

data FooA : Type -> Type where
  MkFooA1 : a -> FooA a
  MkFooA2 : (0 x : a) -> FooA a

0 decEq' : DecEq a => (x : FooA a) -> (y : FooA a) -> Dec (x === y)
decEq' (MkFooA1 x) (MkFooA1 y) = case decEq x y of Yes Refl => Yes Refl; No contra => No (\Refl => contra Refl)
decEq' (MkFooA2 x) (MkFooA2 y) = case decEq x y of Yes Refl => Yes Refl; No contra => No (\Refl => contra Refl)
decEq' (MkFooA1 x) (MkFooA2 y) = No (\case _ impossible)
decEq' (MkFooA2 x) (MkFooA1 y) = No (\case _ impossible)

%hint
0 ErasedDecEq : DecEq a => DecEq (FooA a)
ErasedDecEq = MkDecEq decEq'

DecEq a => DecEq (FooA a) where
  decEq (MkFooA1 x) (MkFooA1 y) = case decEq x y of Yes Refl => Yes Refl; No contra => No (\Refl => contra Refl)
  decEq (MkFooA2 x) (MkFooA2 y) = ?sdffd -- case decEq @{ErasedDecEq} x y of Yes Refl => Yes Refl; No contra => No (\Refl => contra Refl)
  decEq (MkFooA1 x) (MkFooA2 y) = No (\case _ impossible)
  decEq (MkFooA2 x) (MkFooA1 y) = No (\case _ impossible)


-- data FooA : Type -> Type where MkFooA : (0 x : a) -> FooA a

-- DecEq (FooA a) where
  -- decEq (MkFooA x) (MkFooA y) = Yes $ decEq' x y



%hint
decEqImpTest : DecEq a => DecEq b => DecEq (f a) => (DecEq (f (f b))) => DecEq (Foo a f b)
-- decEqImpTest = %runElab decEqGen

decEqImpTest2 : DecEq a => DecEq (Vect n a)
-- decEqImpTest2 = %runElab decEqGen

-- [eqvec]
-- DecEq a => DecEq (Vect n a) where
--   decEq x y =
--     let baffo : forall n,a. DecEq a => (x, y : Vect n a) -> Dec (x === y)
--         baffo [] [] = Yes Refl
--         baffo (_ :: _) [] impossible
--         baffo [] (_ :: _) impossible
--         baffo (x :: xs) (y :: ys) = assert_total $
--           case (decEq x y, decEq @{eqvec} xs ys) of
--             (Yes Refl,Yes Refl) => Yes Refl
--             (No contra,_)       => No (\Refl => contra Refl)
--     in  baffo x y


export
infoFoo : TypeInfo
infoFoo = getInfo "Foo"

data Faf : Type where
  Baf0 : Int -> Faf
  Baf1 : Char -> Int -> Faf
  Baf2 : Int -> Char -> Int -> Faf

Eq Faf where
  (Baf0 x1) == (Baf0 x2) = x1 == x2
  (Baf1 x1 y1) == (Baf1 x2 y2) = x1 == x2 && y1 == y2
  (Baf2 x1 y1 z1) == (Baf2 x2 y2 z2) = x1 == x2 && y1 == y2 && z1 == z2
  _ == _ = False

DecEq Faf where
  decEq (Baf0 x1) (Baf0 x2) = case decEq x1 x2 of
    Yes Refl => Yes Refl
    No contra => No (\Refl => contra Refl)
  decEq (Baf1 x1 y1) (Baf1 x2 y2) = assert_total $ case (decEq x1 x2,decEq y1 y2) of
    (Yes Refl,Yes Refl) => Yes Refl
    (No contra,_) => No (\Refl => contra Refl)
  decEq (Baf2 x1 y1 z1) (Baf2 x2 y2 z2) = assert_total $ case (MkPair (decEq x1 x2) (MkPair (decEq y1 y2) (decEq z1 z2))) of
    (Yes Refl,Yes Refl,Yes Refl) => Yes Refl
    (No contra,_,_) => No (\Refl => contra Refl)
  decEq (Baf0 _) (Baf1 _ _) = No (\case _ impossible)
  decEq (Baf0 _) (Baf2 _ _ _) = No (\case _ impossible)
  decEq (Baf1 _ _) (Baf0 _) = No (\case _ impossible)
  decEq (Baf1 _ _) (Baf2 _ _ _) = No (\case _ impossible)
  decEq (Baf2 __  _) (Baf0 _) = No (\case _ impossible)
  decEq (Baf2 __  _) (Baf1 _ _) = No (\case _ impossible)

-- %runElab deriveBlessed' "Foo" [Eq]
