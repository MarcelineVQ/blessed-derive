module Language.Reflection.Derive.Bifunctor

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

export
||| Filter used params for ones that are applied to our last `n` params
||| and also supertypes of those. e.g. g (f a) (h l) implies Functor (g (f a)) and Functor h
argTypesWithParamsAndApps : Nat -> (targets : List (Name,Nat)) -> (params : List TTImp) -> List TTImp
argTypesWithParamsAndApps n l ss =
    let q  = filter (hasTarget' . ttToTagTree' l) ss -- filter params that use our targets
        q' = filter ((>= n) . List.length . snd . unApp) q
    in map (iterf n stripLAp) q'
  where
    stripLAp : TTImp -> TTImp
    stripLAp (IApp fc s u) = s
    stripLAp tt = tt

||| Turn any name into a Basic name
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

toBasicName' : Name -> TTImp
toBasicName' = var . toBasicName

export
isIVar : TTImp -> Bool
isIVar (IVar _ _) = True
isIVar _ = False

-- TODO: rework this entirely to be clean like you did for tree tagging

-- Cute but this isn't `nHole` this is just Bifunctor. What we need is to have a list of reqImpls tagged with their respective `n`'s
||| `reqImpls` is a list of required implementation names paired with their number of needed holes
export
nHoleImplementationType : {n:_} -> (iface : TTImp) -> (reqImpls : List (Name,Nat)) -> BFParamTypeInfo n -> DeriveUtil -> TTImp
nHoleImplementationType iface reqs fp g =
    let appIface = iface .$ fp.nHoleType
        bifunctorVars = filter isIVar . nub $ argTypesWithParamsAndApps n (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        functorVars = filter isIVar . nub $ argTypesWithParamsAndApps (n `minus` 1) (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (var "Functor" .$) functorVars
                                     ++ map (iface .$) bifunctorVars
                                    --  ++ map ((`app`fp.nHoleType) . var) reqs
        ty = piAllImplicit autoArgs (toList . map fst $ fp.params)
        cn = foldr (\(n,tt),acc => NameMap.insert n tt acc) NameMap.empty fp.params
    in replaceNames (evalState fresh (nameParams fp.params)) ty
    -- in ty

export
twoHoleImplementationType : (l2name,l1name : Name) -> BFParamTypeInfo n -> DeriveUtil -> TTImp
twoHoleImplementationType l2name l1name fp g =
    let appIface = var l2name .$ fp.nHoleType
        l2Vars = filter isIVar . nub $ argTypesWithParamsAndApps 2 (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        l1Vars = filter isIVar . nub $ argTypesWithParamsAndApps 1 (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (var l1name .$) l1Vars ++ map (var l2name .$) l2Vars
        ty = piAllImplicit autoArgs (toList . map fst $ fp.params)
        cn = foldr (\(n,tt),acc => NameMap.insert n tt acc) NameMap.empty fp.params
    in replaceNames (evalState fresh (nameParams fp.params)) ty
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

-- TODO: generate fresh vars for these instead
||| Peel out the names of fields of a constructor into a lhs pattern.
expandLhs' : Vect cc FParamCon' -> Vect cc TTImp
expandLhs' = map (\pc => appNames pc.name (map (toBasicName . name . snd) pc.args))

fetchFreshVar : MonadState (Stream Nat) m => String -> m Name
fetchFreshVar s = pure $ UN (Basic $ s ++ show !fetchNext)

-- TODO: revisit use of believe_me if it's causing issues with type resolution or repl evaluation
||| Bring together generated lhs/rhs patterns.
||| Handle cases of empty types or phantom types.
||| Foldable has a default value to result in so we don't use believe_me
makeFImpl : Foldable t => Zippable t => FParamTypeInfo -> (isFoldable: Bool) -> t TTImp -> t TTImp -> TTImp
makeFImpl fp isFold lhs rhs = iCase (var "z") implicitFalse $
  case (isPhantom fp, null fp.cons, isFold) of
    (_   ,True,_    ) => [impossibleClause `(_)  ] -- No cons, impossible to proceed
    (True,_   ,False) => [`(_) .= `(believe_me z)] -- Var is phantom and not for Foldable, safely change type
    _                 => toList $ zipWith (.=) lhs rhs

makeFImpl' : Foldable t => Zippable t => BFParamTypeInfo n -> (isFoldable: Bool) -> t TTImp -> t TTImp -> TTImp
makeFImpl' fp isFold lhs rhs = 
  case (isPhantom' fp, null fp.cons, isFold) of
    (_   ,True,_    ) => iCase (var "z") implicitFalse [impossibleClause `(_)  ] -- No cons, impossible to proceed
    (True,_   ,False) => `(believe_me z) -- Var is phantom and not for Foldable, safely change type
    _                 => iCase (var "z") implicitFalse $ toList $ zipWith (.=) lhs rhs


genMapTT2 : BFParamTypeInfo 2 -> TTImp
genMapTT2 fp = makeFImpl' fp False (expandLhs' fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenMap : MonadState VarSrc m => (tt : TagTree') -> (var : TTImp) -> m TTImp
    ttGenMap SkipT' x = pure x
    ttGenMap (TargetT' t) x = case t of Z => pure `(f1 ~x); _ => pure `(f2 ~x)
    ttGenMap (AppT' (AppT' _ (TargetT' 0)) (TargetT' 1)) x = pure `(bimap f1 f2 ~x)
    ttGenMap (AppT' (AppT' _ (TargetT' 1)) (TargetT' 0)) x = pure `(bimap f2 f1 ~x)
    ttGenMap (AppT' SkipT' (TargetT' t)) x = case t of Z => pure `(Prelude.map f1 ~x); _ => pure `(Prelude.map f2 ~x)
    ttGenMap (AppT' l (TargetT' t)) x = do
        n <- getNextAsName' "y"
        pure $ `(bimap ~(lambdaArg n .=> !(ttGenMap l (var n))) f2 ~x)
    ttGenMap (AppT' l r) x = do
        n <- getNextAsName' "y"
        pure $ `(bimap ~(lambdaArg n .=> !(ttGenMap r (var n))) ~(lambdaArg n .=> !(ttGenMap r (var n))) ~x)
    ttGenMap (TupleT' (t1,t2,ts)) x = do
        names <- map var <$> replicateA (2 + length ts) (srcVarToName' <$> getNext "t")
        let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip (t1 :: t2 :: fromList ts) names
        rhs <- Vect.foldr1 (\l,r => `(MkPair ~l ~r)) <$> traverse (uncurry ttGenMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenMap (FunctionT' _ l r) x = do
        n <- getNextAsName' "p"
        pure $ lambdaArg n .=> !(ttGenMap r (x .$ !(ttGenMap l (var n))))

    rhss : Vect cc FParamCon' -> Vect cc TTImp
    rhss = map (\pc => appAll pc.name (map (\(tag, arg) => evalState fresh $ ttGenMap tag (toBasicName' arg.name)) pc.args))


mkBifunctorImpl : BFParamTypeInfo 2 -> TTImp
mkBifunctorImpl fp = `(MkBifunctor (\f1,f2,z => ~(genMapTT2 fp)) (\f1 => bimap f1 id) (\f2 => bimap id f2)) --(\f1,z => ~(genMapTT2 fp)) (\f2,z => ~(genMapTT2 fp)))

||| Derives a `Functor` implementation for the given data type
||| and visibility.
export
BifunctorVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
BifunctorVis vis g = do
    let iname = "Bifunctor"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeBFParamTypeInfo 2 g
      | _ => fail (nHoleFail 2 iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    when (any hasNegTargetTT' allFields) $ fail (contraFail iname dtName) -- reject contravariant uses of the hole type
    logMsg "" 0 $ show $ concatMap (map fst . args) fp.cons
    pure $ MkInterfaceImpl iname vis []
            (mkBifunctorImpl fp)
            (twoHoleImplementationType "Bifunctor" "Functor" fp g)

||| Alias for `FunctorVis Public`.
export
Bifunctor : DeriveUtil -> Elab InterfaceImpl
Bifunctor = BifunctorVis Public

export
data Travo : (Type -> Type -> Type) -> (Type -> Type -> Type) -> (Type -> Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  -- MkTravo1 : f (g Int a) b -> Travo r f g h a b
  MkTravo1' : a -> h a -> g (h a) b -> Travo r f g h a b
  MkTravo2 : b -> Travo r f g h a b
  MkTravo3 : a -> g b a -> b -> Travo r f g h a b
  -- MkTravo4 : h b -> a -> h (h b) -> b -> h b -> Travo r f g h a b
  -- MkTravo5 : g a b -> f a b -> r (f a b) (g a b) -> h b -> b -> Travo r f g h a b
  -- MkTravo6 : r (f a b) (g a b) -> g a b -> f a b -> h a -> h b -> a -> b -> Travo r f g h a b
  -- MkTravo7 : r (f a b) (g a b) -> g a b -> f a b -> h a -> h b -> a -> b -> Travo r f g h a b
  MkTravo8 : Int -> Travo r f g h a b
%runElab deriveBlessed `{Travo} [Bifunctor]

{-
-- Functor isn't defined to be a superclass of Bifunctor but I don't understand why, observe:
Bifunctor f => Functor (f a) where
  map f x = mapSnd f x
-- A Functor can be defined in terms of Bifunctor, thus a Bifunctor _is_ a Functor
mapDefault : Bifunctor f => (a -> b) -> f e a -> f e b
-}

-- Bifunctor f => Bifunctor (Travo r f g h) where
  -- bimap f g (MkTravo5 x) = MkTravo5 (bimap f g x)

{-

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
        n <- srcVarToName' <$> getNext "y"
        pure $ `(foldMap ~(lambdaArg n .=> !(ttGenFoldMap r (var n))) ~x)
    ttGenFoldMap (TupleT (t1,t2,ts)) x = do
        names <- map var <$> replicateA (2 + length ts) (srcVarToName' <$> getNext "t")
        let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip (t1 :: t2 :: fromList ts) names
        rhs <- Vect.foldr1 (\acc,x => `(~acc <+> ~x)) <$> traverse (uncurry ttGenFoldMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenFoldMap (FunctionT _ l r) x = pure `(Foldable_Derive_Error_Report_This) -- can't actually happen

    -- filter SkipF's entirely to avoid <+> on extraneous neutral's
    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => case filter (not . isSkipT . fst) pc.args of
        [] => `(neutral) -- foldl1 instead of foldl to avoid extra <+> on neutral
        cs@(_ :: _) => foldl1 (\acc,x => `(~acc <+> ~x))
          (map (\(tag, arg) => evalState fresh $ ttGenFoldMap tag (toBasicName' arg.name)) cs))

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
    rhss = map $ \pc => evalState fresh $ do
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