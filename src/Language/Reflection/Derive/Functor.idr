module Language.Reflection.Derive.Functor

import public Util

import public Language.Reflection.Maps
import Language.Reflection.Derive.Derive
import public Language.Reflection.Derive.Types


import Control.Monad.State

import public Language.Reflection.Pretty

import public Language.Reflection.Derive
%language ElabReflection

--------------------------------------------------
-- MkFC regex:
-- \(MkFC (.*?)(\)\))
-- \(MkFC (.*?)(\)\))(.*?)(\)\))
--------------------------------------------------

--------------------------------------------------
-- Known issues
--------------------------------------------------
{-
The largest issue with this as it stands is that there's no immediate warning for
overlapping instances if a user already wrote one and then derives.

This doesn't derive indexed types yet, but there's no reason it can't be made to
-}

deepestAp : TTImp -> TTImp
deepestAp (IApp fc s u) = deepestAp u
deepestAp tt = tt

-- alternatively could use calcArgTypesWithParams
iVarAnywhere : (name : TTImp) -> TTImp -> Bool
iVarAnywhere n na@(IVar _ _) = n == na
iVarAnywhere n (IApp fc s t) = iVarAnywhere n s || iVarAnywhere n t
iVarAnywhere _ _ = False

-- Special pi case since we can't just map them
findAp : (targ : TTImp) -> TTImp -> Maybe TTImp
findAp t (IApp fc s u@(IVar _ _)) = if u == t then Just s else Nothing
findAp t (IApp fc s pi@(IPi _ _ _ _ l r)) = if iVarAnywhere t l || iVarAnywhere t r then Just s else Nothing
findAp t (IApp fc s u) = IApp fc s <$> findAp t u
findAp t _ = Nothing

export
||| Filter used params for ones that are applied to our `l`ast param
||| and also supertypes of those. e.g. g (f a) (h l) implies Functor (g (f a)) and Functor h
argTypesWithParamsAndApps : (taget : TTImp) -> (params : List TTImp) -> List TTImp
argTypesWithParamsAndApps l ss = 
    let b = mapMaybe (findAp l) ss
        c = concatMap (\t => List.mapMaybe (findAp (deepestAp t)) b) b
    in map deepestAp b ++ c
-- ^ find apps that use l at the end:
-- e.g.  `h l --> h`  and  `g (f a) (h l) --> (g (f a)) h`
-- Then also find apps that use those apps:
-- e.g. (g (f a)) h = g (f a)

||| Turn any name into a Basic name
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

varStream : String -> Stream Name
varStream s = map (fromString . ("\{s}_" ++) . show) [the Int 1 ..]

toBasicName' : Name -> TTImp
toBasicName' = var . toBasicName

-- TODO: rework this entirely to be clean like you did for tree tagging
export
oneHoleImplementationType : (iface : TTImp) -> (reqImpls : List Name) -> FParamTypeInfo -> DeriveUtil -> TTImp
oneHoleImplementationType iface reqs fp g =
    let appIface = iface .$ fp.oneHoleType
        functorVars = nub $ argTypesWithParamsAndApps (snd fp.holeType) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (iface .$) functorVars ++ map (\n => app (var n) fp.oneHoleType) reqs
        ty = piAllImplicit autoArgs (toList . map fst $ init fp.params)
        cn = foldr (\(n,tt),acc => NameMap.insert n tt acc) NameMap.empty fp.params
    in replaceNames (runFresh (nameParams fp.params)) ty
    -- in ty

------------------------------------------------------------
-- Failure reporting
------------------------------------------------------------

failDerive : (where' : String) -> (why : String) -> String
failDerive where' why = "Failure deriving \{where'}: \{why}"

piFail : String -> (dtName : String) -> String
piFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its final parameter is used in a function type."

contraFail : (impl : String) -> (dtName : String) -> String
contraFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its final parameter is used in negative position of a function type."

nHoleFail : Nat -> (impl : String) -> (dtName : String) -> String
nHoleFail n s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its type does not end in \{nhole}Type."
  where
    nhole : String
    nhole = concat . List.replicate n $ "Type -> "

oneHoleFail : (impl : String) -> (dtName : String) -> String
oneHoleFail s dtName = nHoleFail 1 s dtName

------------------------------------------------------------

-- TODO: generate fresh vars for these instead
||| Peel out the names of fields of a constructor into a lhs pattern.
expandLhs : Vect cc FParamCon -> Vect cc TTImp
expandLhs = map (\pc => appNames pc.name (map (toBasicName . name . snd) pc.args))

-- TODO: revisit use of believe_me if it's causing issues with type resolution or repl evaluation
||| Bring together generated lhs/rhs patterns.
||| Handle cases of empty types or phantom types.
||| Foldable has a default value to result in so we don't use believe_me
makeFImpl : Foldable t => Zippable t => FParamTypeInfo -> (isFoldable: Bool) -> t TTImp -> t TTImp -> TTImp
makeFImpl fp isFold lhs rhs =
  case (isPhantom fp, null fp.cons, isFold) of
    (_   ,True,_    ) => iCase (var "z") implicitFalse $ [impossibleClause `(_)] -- No cons, impossible to proceed
    (True,_   ,False) => `(believe_me z) -- Var is phantom and not for Foldable, safely change type
    _                 => iCase (var "z") implicitFalse $ toList $ zipWith (.=) lhs rhs

genMapTT : FParamTypeInfo -> TTImp
genMapTT fp = makeFImpl fp False (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenMap : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenMap SkipT x = pure x
    ttGenMap TargetT x = pure `(f ~x)
    ttGenMap (AppT l TargetT) x = pure `(map f ~x)
    ttGenMap (AppT l r) x = do
        n <- getNextAsName' "y"
        pure $ `(map ~(lambdaArg n .=> !(ttGenMap r (var n))) ~x)
    ttGenMap (TupleT (t1,t2,ts)) x = do
        names <- map var <$> replicateA (2 + length ts) (getNextAsName' "t")
        let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip (t1 :: t2 :: fromList ts) names
        rhs <- Vect.foldr1 (\l,r => `(MkPair ~l ~r)) <$> traverse (uncurry ttGenMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenMap (FunctionT _ l r) x = do
        n <- getNextAsName' "p"
        pure $ lambdaArg n .=> !(ttGenMap r (x .$ !(ttGenMap l (var n))))

    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => appAll pc.name (map (\(tag, arg) => runFresh $ ttGenMap tag (toBasicName' arg.name)) pc.args))


mkFunctorImpl : FParamTypeInfo -> TTImp
mkFunctorImpl fp = `(MkFunctor $ \f,z => ~(genMapTT fp))

||| Derives a `Functor` implementation for the given data type
||| and visibility.
export
FunctorVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FunctorVis vis g = do
    let iname = "Functor"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeFParamTypeInfo g
      | _ => fail (oneHoleFail iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    when (any hasNegTargetTT allFields) $ fail (contraFail iname dtName) -- reject contravariant uses of the hole type
    pure $ MkInterfaceImpl iname vis []
            (mkFunctorImpl fp)
            (oneHoleImplementationType `(Functor) [] fp g)

||| Alias for `FunctorVis Public`.
export
Functor : DeriveUtil -> Elab InterfaceImpl
Functor = FunctorVis Public

-- Should endo be exported for defaultFoldr? Seems ok
[EndoS] Semigroup (a -> a) where
  f <+> g = \x => f (g x)

[Endo] Monoid (a -> a) using EndoS where
  neutral = id

public export %inline
defaultFoldr : Foldable t => (func : a -> b -> b) -> (init : b) -> (input : t a) -> b
defaultFoldr f acc xs = foldMap @{%search} @{Endo} f xs acc

genFoldMapTT : FParamTypeInfo -> TTImp
genFoldMapTT fp = makeFImpl fp True (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenFoldMap : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenFoldMap SkipT x = pure `(neutral)
    ttGenFoldMap TargetT x = pure `(f ~x)
    ttGenFoldMap (AppT l TargetT) x = pure `(foldMap f ~x)
    ttGenFoldMap (AppT l r) x = do
        n <- getNextAsName' "y"
        pure $ `(foldMap ~(lambdaArg n .=> !(ttGenFoldMap r (var n))) ~x)
    ttGenFoldMap (TupleT (t1,t2,ts)) x = do
        names <- map var <$> replicateA (2 + length ts) (getNextAsName' "t")
        let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip (t1 :: t2 :: fromList ts) names
        rhs <- Vect.foldl1 (\acc,x => `(~acc <+> ~x)) <$> traverse (uncurry ttGenFoldMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenFoldMap (FunctionT _ l r) x = pure `(Foldable_Derive_Error_Report_This) -- can't actually happen

    -- filter SkipF's entirely to avoid <+> on extraneous neutral's
    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => case filter (not . isSkipT . fst) pc.args of
        [] => `(neutral) -- foldl1 instead of foldl to avoid extra <+> on neutral
        cs@(_ :: _) => foldl1 (\acc,x => `(~acc <+> ~x))
          (map (\(tag, arg) => runFresh $ ttGenFoldMap tag (toBasicName' arg.name)) cs))

-- e.g :
public export
getBaseImplementation' : (x : Type) -> Elab x
getBaseImplementation' implTy = do
  tpe <- quote implTy
  let d = `( let x = %search in the ~tpe x )
  z <- check {expected=implTy} d
  pure z

-- Copied from base but this should actually quote a known Foldable somehow,
-- like above, and edit it via field-name to keep up-to-date automatically.
mkFoldableImpl : FParamTypeInfo -> TTImp
mkFoldableImpl fp = `(MkFoldable 
                     defaultFoldr
                     (\f,z,t => foldr (flip (.) . flip f) id t z)
                     (\xs => foldr {acc = Lazy Bool} (\ _,_ => False) True xs)
                     (\fm,a0 => foldl (\ma, b => ma >>= flip fm b) (pure a0))
                     (foldr (::) [])
                     (\f,z => ~(genFoldMapTT fp))
                     )

||| Derives a `Foldable` implementation for the given data type
||| and visibility.
export
FoldableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FoldableVis vis g = do
    let iname = "Foldable"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeFParamTypeInfo g
      | _ => fail (oneHoleFail iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    when (any hasFunctionT allFields) $ fail (piFail iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkFoldableImpl fp)
             (oneHoleImplementationType `(Foldable) [] fp g)

||| Alias for `FoldableVis Public`.
export
Foldable : DeriveUtil -> Elab InterfaceImpl
Foldable = FoldableVis Public

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
        n <- getNextAsName' "y"
        pure $ `(traverse ~(lambdaArg n .=> !(ttGenTraverse r (var n))) ~x)
    ttGenTraverse (TupleT (t1,t2,ts)) x = do
        names <- map var <$> replicateA (2 + length ts) (getNextAsName' "t")
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
                    else do n <- getNextAsName' "larg"
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
mkTraversableImpl fp = `(MkTraversable (\f,z => ~(genTraverseTT fp )))

-- Checker for whether an implementation exists
-- This is pretty gross as it litters the namespace
-- Also sadly this won't work as elab-util:derive is written since generation of each
-- listed class occurs all at once despite declaration being separated into two phases.
checkHasImpl : (imp : String) -> (has : String) -> (typename : Name) -> (type : TTImp) -> Elab ()
checkHasImpl imp req n' tytt = do
    let n = fromString "__implSearch\{imp}\{req}\{nameStr n'}"
    declare $ [claim MW Private [] n tytt
              ,def n [var n .= ISearch EmptyFC 1000]]
-- TODO, add these to functor and foldable too, to alert when deifned across module bounds

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
