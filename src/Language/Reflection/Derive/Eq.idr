module Language.Reflection.Derive.Eq

import public Language.Reflection.Maps

import Decidable.Equality

import Data.Either -- partitionEithers

%language ElabReflection

-- Module is a mix of elab-util and Derive.Functor approaches

record ConstructorView where
  constructor MkConstructorView
  conName : Name
  params      : List Name
  conArgTypes : List TTImp

-- taken from gallais straightforward solution in Deriving.Functor
-- Note how he keeps the arg ttimps, useful for computing applications or pi content later
-- What's happening here is that we're walking along each arg in the constructor's type
-- `x -> ... -> end`
-- If it's implicit or auto we skip it, we add everything else as TTImp, when we get
-- to the end we examine the final type and extract its params. Note that this could
-- get quite interesting with indices invovled
-- TODO: handle explcit implcits, iow: ImplicitArg that are MW
export
explicits : Name -> TTImp -> Maybe ConstructorView
-- explicits n (IPi fc MW ImplicitArg x a b) = { conArgTypes $= (a ::) } <$> explicits n b
explicits n (IPi fc rig ExplicitArg x a b) = { conArgTypes $= (a ::) } <$> explicits n b
explicits n (IPi fc rig pinfo x a b) = explicits n b
explicits n f@(IApp _ _ _) = do
  MkAppView _ ts _ <- appView f
  let ps = flip mapMaybe ts $ \ t' => the (Maybe Name) $ case t' of
             Arg _ v@(IVar _ nm) => Just nm
             _ => Nothing
  pure (MkConstructorView n (ps <>> []) [])
explicits _ _ = Nothing

eqGen : Elab (Eq a)
eqGen = do
  Just (IApp _ (IVar fc `{Prelude.EqOrd.Eq}) t) <- goal
    | _ => fail "bad goal: expected form like, Eq a => Eq (Foo a)"
  Just appGoal <- pure $ appView t
    | _ => fail "notAp"
  Just paramSource <- pure $ explicits (snd appGoal.head) t
    | _ => fail "notAp"
  consTT <- traverse lookupName !(getCons (snd appGoal.head))
  Just consWithExplicits <- pure $ traverse (uncurry explicits) consTT
    | Nothing => fail "Failed to get cons of \{show $ snd appGoal.head}"

  let implName' = "eqGenFun"
  let implName = var implName'

  -- differentiate params from indices, params will result in Type
  (params,indices) <- partitionEithers <$> (for paramSource.params $ \p => do
    (_,(IType _)) <- unPi <$> getLocalType p
      | _ => pure $ Right p
    pure $ Left p)
  -- traverse_ (logMsg "params" 1 . show) (the (List Name) params)
  -- traverse_ (logMsg "indices" 1 . show) (the (List Name) indices)

  let ty' = `( ~t -> ~t -> Bool)
  let ty = MkTy fc fc implName' $ piAllImplicit ty' indices

  -- pair each con with itself, if each con argument is == then the pairing is True
  -- any other possibility is False
  let cls = (consWithExplicits <&> \(MkConstructorView cName params cArgs) => runFresh $ do
        lvs <- traverse (\_ => var . srcVarTo_Name' <$> (getNext "x")) cArgs
        rvs <- traverse (\_ => var . srcVarTo_Name' <$> (getNext "y")) cArgs
        apps@(_ :: _) <- pure $ (zipWith (\l,r => `(~l == ~r)) lvs rvs)
          | _ => pure $ `(~implName ~(var cName) ~(var cName)) .= `(True)
        pure $ `(~implName ~(appAll cName lvs) ~(appAll cName rvs)) .=
          foldr1 (\p,ps => `(~p && ~ps)) apps)
        ++ [`(~implName _ _) .= `(False)]

  logMsg "derive.eqGen.clauses" 1 $
    joinBy "\n" ("" :: ("  " ++ show ty)
                    :: map (("  " ++) . showClause InDecl) cls)

  check $ ILocal EmptyFC
    [ IClaim fc MW Private [] ty
    , IDef fc implName' cls
    ] `(MkEq {ty = ~(t)} (\x,y => ~implName x y) (\x,y => not (~implName x y)) )

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
    else let lvs = map (const `(_)) ts1
             rvs = map (const `(_)) ts2
         in if (p1 == p2) -- if indices don't differ, use No
           then `(~implName ~(appAll n1 lvs) ~(appAll n2 rvs)) .= `(No (\case _ impossible))
           else impossibleClause `(~implName ~(appAll n1 lvs) ~(appAll n2 rvs)) -- .= `(No (\case _ impossible))

decEqGen : Elab (DecEq a)
decEqGen = do
  Just (IApp _ (IVar fc `{Decidable.Equality.Core.DecEq}) t) <- goal
    | _ => fail "bad goal: expected form like, DecEq a => DecEq (Foo a)"
  Just appGoal <- pure $ appView t
    | _ => fail "goalNotAp"
  Just paramSource <- pure $ explicits (snd appGoal.head) t
    | _ => fail "goalNotAp"
  consTT <- traverse lookupName !(getCons (snd appGoal.head))
  Just consWithExplicits <- pure $ traverse (uncurry explicits) consTT
    | Nothing => fail "Failed to get cons of \{show $ snd appGoal.head}"

  let implName' = "decEqGenFun"
  let implName = var implName'
  
  -- differentiate params from indices, params will result in Type
  (params,indices) <- partitionEithers <$> (for paramSource.params $ \p => do
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

  -- con not exposed by default
  let decEqConName = `{Decidable.Equality.Core.DecEq}
  [decEqCon] <- getCons decEqConName
    | _ => fail "Couldn't get DecEq constructor expected at \{show decEqConName}"
  check $ ILocal EmptyFC
    [ IClaim fc MW Private [] ty
    , IDef fc implName' cls
    ] `(~(var decEqCon) {t = ~(t)} (\x,y => ~implName x y))


public export
data Foo : Type -> (Type -> Type) -> Type -> Type where
  MkFoo1 : a -> Foo a f b
  MkFoo2 : b -> Foo a f b
  MkFoo2' : a -> b -> f a -> Foo a f b
  MkFoo3 : Foo a f b
  MkFoo4 : f a -> Foo a f b
  MkFoo5 : f (f b) -> Foo a f b
  -- MkFoo6 : {g : b} -> f (f b) -> Foo a f b -- explcit implicits not handled yet
  -- MkFoo6 : {g : b} -> f (f b) -> Foo a f b

export
%hint
eqImpTest : Eq a => Eq b => Eq (f a) => (Eq (f (f b))) => Eq (Foo a f b)
-- eqImpTest : Eq (Foo a f b)
eqImpTest = %runElab eqGen

export
eqImpTest2 : Eq a => Eq (Vect n a)
-- eqImpTest : Eq (Foo a f b)
eqImpTest2 = %runElab eqGen

export
%hint
decEqImpTest : DecEq a => DecEq b => DecEq (f a) => (DecEq (f (f b))) => DecEq (Foo a f b)
decEqImpTest = %runElab decEqGen

decEqImpTest2 : DecEq a => DecEq (Vect n a)
decEqImpTest2 = %runElab decEqGen

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

-- co pattern matching

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
