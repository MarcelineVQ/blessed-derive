module Language.Reflection.Derive.Bifunctor

import Language.Reflection.Derive.Functor

import public Util

import public Language.Reflection.Maps
import Language.Reflection.Derive.Derive
import public Language.Reflection.Derive.Types


import Control.Monad.State

import public Language.Reflection.Pretty

import public Language.Reflection.Derive
%language ElabReflection

twoHoleImplementationType : (l2name,l1name : Name) -> BFParamTypeInfo n -> DeriveUtil -> TTImp
twoHoleImplementationType l2name l1name fp g =
    let appIface = var l2name .$ fp.nHoleType
        -- l2Vars = filter isIVar . nub $ argTypesWithParamsAndApps 2 (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        l2Vars = nub $ argTypesWithParamsAndApps 2 (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        -- l1Vars = filter isIVar . nub $ argTypesWithParamsAndApps 1 (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        l1Vars = nub $ argTypesWithParamsAndApps 1 (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (var l1name .$) l1Vars ++ map (var l2name .$) l2Vars
        ty = piAllImplicit autoArgs (toList . map fst $ fp.params)
    in replaceNames (runFresh (nameParams fp.params)) ty

------------------------------------------------------------

genBimapTT : BFParamTypeInfo 2 -> TTImp
genBimapTT fp = makeFImpl fp False (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenMap : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenMap SkipT x = pure x
    ttGenMap (TargetT t) x = pure $ case t of Z => `(f1 ~x); _ => `(f2 ~x)
    ttGenMap (AppT 1 SkipT r) x = do -- map case
        n <- getNextAsName "y"
        pure `(map ~(lambdaArg n .=> !(ttGenMap r (var n))) ~x)
    ttGenMap (AppT n l r) x = do
        n <- getNextAsName "y"
        -- Strip off an app and get the last two params at once
        -- e.g: in `g a b c d` ~ `(((g a) b) c) d` this gets us bimap over c and d
        let l' = case l of AppT _ _ l' => l'; _ => l
        pure $ `(bimap ~(lambdaArg n .=> !(ttGenMap l' (var n))) ~(lambdaArg n .=> !(ttGenMap r (var n))) ~x)
    ttGenMap (TupleT {n} ts) x = do
        names <- map var <$> replicateA (S (S n)) (srcVarToName' <$> getNext "t")
        let lhs = foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip ts names
        rhs <- foldr1 (\l,r => `(MkPair ~l ~r)) <$> traverse (uncurry ttGenMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenMap (FunctionT _ l r) x = do
        n <- getNextAsName' "p"
        pure $ lambdaArg n .=> !(ttGenMap r (x .$ !(ttGenMap l (var n))))

    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => appAll pc.name (map (\(tag, arg) =>
      runFresh $ ttGenMap tag (var arg.name)) pc.args))


mkBifunctorImpl : BFParamTypeInfo 2 -> TTImp
mkBifunctorImpl fp = `(MkBifunctor (\f1,f2,implArg => ~(genBimapTT fp)) (\f1 => bimap f1 id) (\f2 => bimap id f2))

||| Derives a `Functor` implementation for the given data type
||| and visibility.
export
BifunctorVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
BifunctorVis vis g = do
    let iname = "Bifunctor"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeBFParamTypeInfo 2 g
      | _ => fail (holeFail 2 iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    when (any hasNegTargetTT allFields) $ fail (contraFail 2 iname dtName) -- reject contravariant uses of the hole type
    pure $ MkInterfaceImpl iname vis []
            (mkBifunctorImpl fp)
            (twoHoleImplementationType "Bifunctor" "Functor" fp g)

||| Alias for `FunctorVis Public`.
export
Bifunctor : DeriveUtil -> Elab InterfaceImpl
Bifunctor = BifunctorVis Public

{-
-- Functor isn't defined to be a superclass of Bifunctor but I don't understand why, observe:
Bifunctor f => Functor (f a) where
  map f x = mapSnd f x
-- A Functor can be defined in terms of Bifunctor, thus a Bifunctor _is_ a Functor
mapDefault : Bifunctor f => (a -> b) -> f e a -> f e b
-}

{-
-- Should endo be exported for defaultFoldr? Seems ok
[EndoS] Semigroup (a -> a) where
  f <+> g = \x => f (g x)

[Endo] Monoid (a -> a) using Bifunctor.EndoS where
  neutral = id

-- interface Bifoldable p where
--   constructor MkBifoldable
--   bifoldr : (a -> acc -> acc) -> (b -> acc -> acc) -> acc -> p a b -> acc

--   bifoldl : (acc -> a -> acc) -> (acc -> b -> acc) -> acc -> p a b -> acc
--   bifoldl f g z t = bifoldr (flip (.) . flip f) (flip (.) . flip g) id t z

--   binull : p a b -> Bool
--   binull t = bifoldr {acc = Lazy Bool} (\ _,_ => False) (\ _,_ => False) True t

defaultBifoldMap : Bifoldable p => Monoid m => (a -> m) -> (b -> m) -> p a b -> m
defaultBifoldMap f g xs = bifoldr ((<+>) . f) ((<+>) . g) neutral xs

genBifoldMapTT : BFParamTypeInfo 2 -> TTImp
genBifoldMapTT fp = makeFImpl fp True (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenBifoldMap : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenBifoldMap SkipT x = pure `(acc)
    ttGenBifoldMap (TargetT t) x = pure $ case t of Z => `(f1 ~x acc); _ => `(f2 ~x acc)
    ttGenBifoldMap (AppT 1 SkipT r) x = do -- foldMap case
        n <- getNextAsName' "y"
        pure `(Prelude.foldr ~(lambdaArg n .=> !(ttGenBifoldMap r (var n))) acc ~x)
    ttGenBifoldMap (AppT n l r) x = do
        n <- getNextAsName' "y"
        -- Strip off an app and get the last two params at once
        -- e.g: in `g a b c d` ~ `(((g a) b) c) d` this gets us bimap over c and d
        let l' = case l of AppT _ _ l' => l'; _ => l
        pure $ `(Prelude.bifoldr ~(lambdaArg n .=> !(ttGenBifoldMap l' (var n))) ~(lambdaArg n .=> !(ttGenBifoldMap r (var n))) acc ~x)
    ttGenBifoldMap (TupleT {n} ts) x = do
        names <- map var <$> replicateA (S (S n)) (srcVarToName' <$> getNext "t")
        let lhs = foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip ts names
        rhs <- foldl1 (\acc,x => `(~acc <+> ~x)) <$> traverse (uncurry ttGenBifoldMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenBifoldMap (FunctionT _ l r) x = pure $ `(cantHappen)

    -- ||| Stateful so that we can create unique variable names as we go
    -- ttGenBifoldMap : MonadState VarSrc m => (tt : TagTree') -> (var : TTImp) -> m TTImp
    -- ttGenBifoldMap SkipT' x = pure `(neutral)
    -- ttGenBifoldMap (TargetT' t) x = pure `(f ~x)
    -- ttGenBifoldMap (AppT l TargetT) x = pure `(foldMap f ~x)
    -- ttGenBifoldMap (AppT l r) x = do
    --     n <- srcVarToName' <$> getNext "y"
    --     pure $ `(foldMap ~(lambdaArg n .=> !(ttGenBifoldMap r (var n))) ~x)
    -- ttGenBifoldMap (TupleT (t1,t2,ts)) x = do
    --     names <- map var <$> replicateA (2 + length ts) (srcVarToName' <$> getNext "t")
    --     let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
    --         tts = zip (t1 :: t2 :: fromList ts) names
    --     rhs <- Vect.foldr1 (\acc,x => `(~acc <+> ~x)) <$> traverse (uncurry ttGenBifoldMap) tts
    --     pure `(case ~x of ~lhs => ~rhs)
    -- ttGenBifoldMap (FunctionT _ l r) x = pure `(Foldable_Derive_Error_Report_This) -- can't actually happen

    -- filter SkipF's entirely to avoid <+> on extraneous neutral's
    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => case filter (not . isSkipT . fst) pc.args of
        [] => `(neutral) -- foldl1 instead of foldl to avoid extra <+> on neutral
        cs@(_ :: _) => foldl1 (\acc,x => `(~acc <+> ~x))
          (map (\(tag, arg) => runFresh $ ttGenBifoldMap tag (var arg.name)) cs))

bifoldr' : Bifunctor p => (a -> acc -> acc) -> (b -> acc -> acc) -> acc -> p a b -> acc
bifoldr' f g acc xs =
  let bifoldMap : Monoid m => (a -> m) -> (b -> m) -> p a b -> m
      bifoldMap = ?genBifoldMapTT'
  in  bifoldMap @{Endo} f g xs acc

mkFoldableImpl : BFParamTypeInfo 2 -> TTImp
mkFoldableImpl fp = `(MkBifoldable
                    --  (\f1,f2,acc,implArg => ~(genBifoldMapTT fp))
                     (\f1,f2,acc,implArg => ?sdfsdffsd)
                     (\f,g,z,t => bifoldr (flip (.) . flip f) (flip (.) . flip g) id t z)
                     (\t => bifoldr {acc = Lazy Bool} (\ _,_ => False) (\ _,_ => False) True t)
                     )
  -- where
    -- bifoldMap : Bifoldable p => Monoid m => (a -> m) -> (b -> m) -> p a b -> m
    -- bifoldMap = \f1,f2,implArg => ~(genBifoldMapTT fp)
  -- (\f1',f2',acc,implArg' =>
                      --  let bifoldMap : Bifoldable p => Monoid m => (a -> m) -> (b -> m) -> p a b -> m
                          --  bifoldMap = \f1,f2,implArg => ~(genBifoldMapTT fp)
                      --  in  bifoldMap @{%search} @{Endo} f1' f2' implArg' acc)
-- 
||| Derives a `Foldable` implementation for the given data type
||| and visibility.
export
BifoldableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
BifoldableVis vis g = do
    let iname = "Bifoldable"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeBFParamTypeInfo 2 g
      | _ => fail (holeFail 2 iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    when (any hasFunctionT allFields) $ fail (piFail 2 iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkFoldableImpl fp)
             (twoHoleImplementationType "Bifoldable" "Foldable" fp g)

||| Alias for `FoldableVis Public`.
export
Bifoldable : DeriveUtil -> Elab InterfaceImpl
Bifoldable = BifoldableVis Public

export
data Travo : (Type -> Type -> Type) -> (Type -> Type -> Type) -> (Type -> Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  -- MkTravo1 : f (g Int a) b -> Travo r f g h a b
  -- MkTravo1' : a -> h a -> g (h a) b -> Travo r f g h a b
  MkTravo2 : b -> Travo r f g h a b
  MkTravo2' : h b -> Travo r f g h a b
  -- MkTravo3 : a -> g b a -> b -> Travo r f g h a b
  -- MkTravo4 : h (h b) -> h b -> Travo r f g h a b
  -- MkTravo4' : h b -> a -> h (h b) -> b -> h b -> Travo r f g h a b
  -- MkTravo5 : g a b -> f a b -> r (f a b) (g a b) -> h b -> b -> Travo r f g h a b
  -- MkTravo6 : r (f a b) (g a b) -> g a b -> f a b -> h a -> h b -> a -> b -> Travo r f g h a b
  -- MkTravo7 : r (f a b) (g a b) -> g a b -> (f a b,g a b) -> h a -> h b -> a -> b -> Travo r f g h a b
  -- -- MkTravo7' : r (f a b) (g (Int -> a) b) -> g a b -> (f a b,g a b) -> h a -> h b -> a -> b -> Travo r f g h a b
  -- MkTravo8 : Int -> Travo r f g h a b
  -- -- MkTravo9 : g (Int -> b) ((b -> Int) -> a) -> Travo r f g h a b
  -- MkTravo7'' : Travo r f g h a b -> Travo r f g h a b
%runElab deriveBlessed `{Travo} [Bifunctor,Bifoldable]
-- %runElab deriveBlessed `{Travo} [Bifoldable]

-- Bifoldable (Travo r f g h) where
  -- bifoldr f g acc (MkTravo2 b) = (g b) acc

-- %runElab BifunctorVis' `{Travo}

{-
genTraverseTT : FParamTypeInfo -> TTImp
genTraverseTT fp = makeFImpl fp False (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    export
    ttGenTraverse : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenTraverse SkipT x = pure `(pure ~x)
    ttGenTraverse TargetT x = pure `(f ~x)
    ttGenTraverse (AppT l TargetT) x = pure `(traverse f ~x)
    ttGenTraverse (AppT l r) x = do
        n <- srcVarToName' <$> getNext "y"
        pure $ `(traverse ~(lambdaArg n .=> !(ttGenTraverse r (var n))) ~x)
    ttGenTraverse (TupleT (t1,t2,ts)) x = do
        names <- map var <$> replicateA (2 + length ts) (srcVarToName' <$> getNext "t")
        let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip (t1 :: t2 :: fromList ts) names
        rhs <- Vect.foldr1 (\acc,x => `(~acc <*> ~x)) <$> traverse (uncurry ttGenTraverse) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenTraverse (FunctionT _ l r) x = pure `(Traverse_Derive_Error_Report_This) -- can't actually happen

    ||| Construct a function to lead the <*> chain
    ||| Saves on some redundant uses of pure and <*>, e.g.:
    ||| data Foo f a b c = MkFoo a (f b) (f c)
    |||    traverse (MkFoo a b c) = pure MkFoo <*> pure a <*> b <*> c
    ||| vs traverse (MkFoo a b c) = (\b',c' => MkFoo a b' c') <$> b <*> c
    export
    conFunc : MonadState VarSrc m => FParamCon -> m TTImp
    conFunc pc = do
        (body,names) <- foldlM (\(tt,ns),(tag,arg) => if isSkipT tag
                    then pure $ (tt .$ toBasicName' arg.name, ns)
                    else do n <- srcVarToName' <$> getNext "larg"
                            pure $ ((tt .$ var n), n :: ns)) (var pc.name,[]) pc.args
        pure $ foldl (\tt,sn => lambdaArg sn .=> tt) body (the (List Name) names)

    export
    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map $ \pc => runFresh $ do
        (a :: aps) <- traverse (\(tag, arg) =>
          ttGenTraverse tag (toBasicName' arg.name)) (filter (not . isSkipT . fst) pc.args)
                  -- reapply lhs under pure if all vars are SkipT
          | [] => pure $ `(pure) .$ appNames pc.name (toBasicName . name . snd <$> pc.args)
        rc <- conFunc pc
        pure $ foldl (\acc,x => `(~acc <*> ~x)) `(~rc <$> ~a) aps

mkTraversableImpl : FParamTypeInfo -> TTImp
mkTraversableImpl fp = `(MkTraversable (\f,implArg => ~(genTraverseTT fp )))

-- Checker for whether an implementation exists
-- This is pretty gross as it litters the namespace
-- Also sadly this won't work as elab-util:derive is written since generation of each
-- listed class occurs all at once despite declaration being separated into two phases.
checkHasImpl : (imp : String) -> (has : String) -> (typename : Name) -> (type : TTImp) -> Elab ()
checkHasImpl imp req n' tytt = do
    let n = fromString "__implSearch\{imp}\{req}\{nameStr n'}"
    declare $ [claim MW Private [] n tytt
              ,def n [var n .= ISearch EmptyFC 1000]]

||| Derives a `Traversable` implementation for the given data type
||| and visibility.
export
TraversableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
TraversableVis vis g = do
    let iname = "Traversable"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeFParamTypeInfo g
      | _ => fail (oneHoleFail iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    let depsFo = oneHoleImplementationType `(Foldable) [] fp g
    let depsFu = oneHoleImplementationType `(Functor) [] fp g
    () <- checkHasImpl "Traversable" "Foldable" fp.name depsFo
    () <- checkHasImpl "Traversable" "Functor" fp.name depsFu
    when (any hasFunctionT allFields) $ fail (piFail iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkTraversableImpl fp)
             (oneHoleImplementationType `(Traversable) [`{Functor},`{Foldable}] fp g)

||| Alias for `TraversableVis Public`.
export
Traversable : DeriveUtil -> Elab InterfaceImpl
Traversable = TraversableVis Public
-}