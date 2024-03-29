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

export
||| Filter used params for ones that are applied to our last `n` params
||| and also supertypes of those. e.g. g (f a) (h l) implies Functor (g (f a)) and Functor h
argTypesWithParamsAndApps : Nat -> (targets : List (Name,Nat)) -> (params : List TTImp) -> List TTImp
argTypesWithParamsAndApps n l ps = do
    p <- ps
    (h,t) <- maybeToList (stripLAp n p)
    guard $ not . hasTarget $ ttToTagTree l h -- no target in head n-args
    guard $ any (hasTarget . ttToTagTree l) t -- target in tail n-args
    let g = argTypesWithParamsAndApps n l t -- reapply to tail args, e.g. extract h from: g (f a) (h l)
    h :: g
where
  stripLAp : Nat -> TTImp -> Maybe (TTImp,List TTImp)
  stripLAp (S n) (IApp fc s u) = mapSnd (++ [u]) <$> stripLAp n s
  stripLAp (S n) tt = Nothing
  stripLAp Z tt = Just (tt,[])

export
oneHoleImplementationType : (l1name : Name) -> BFParamTypeInfo 1 -> DeriveUtil -> TTImp
oneHoleImplementationType l1name fp g =
    let appIface = var l1name .$ fp.nHoleType
        l1Vars = nub $ argTypesWithParamsAndApps 1 (numberedList (toList $ map fst fp.holeParams)) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (var l1name .$) l1Vars
        ty = piAllImplicit autoArgs (toList . map fst $ fp.params)
    in replaceNames (runFresh (nameParams fp.params)) ty

------------------------------------------------------------
-- Failure reporting
------------------------------------------------------------

------------------------------------------------------------
-- Failure reporting
------------------------------------------------------------

export
failDerive : (where' : String) -> (why : String) -> String
failDerive where' why = "Failure deriving \{where'}: \{why}"

export
piFail : (n : Nat) -> n `GT` 0 => (impl : String) -> (dtName : String) -> String
piFail 1 s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as it's final parameter is used in a function type."
piFail n s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as one of its final \{show n} parameters are used in a function type."

export
contraFail : (n : Nat) -> n `GT` 0 => (impl : String) -> (dtName : String) -> String
contraFail 1 s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its final parameter is used in negative position of a function type."
contraFail n s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as one of its final \{show n} parameters are used in negative position of a function type."

export
holeFail : (n : Nat) -> n `GT` 0 => (impl : String) -> (dtName : String) -> String
holeFail n s dtName = let nhole = concat . List.replicate n $ "Type -> "
                      in failDerive (s ++ " for \{dtName}") "Can't be derived as its type does not end in \{nhole}Type."
------------------------------------------------------------

-- TODO: generate fresh vars for these instead
||| Peel out the names of fields of a constructor into a lhs pattern.
export
expandLhs : Vect cc FParamCon -> Vect cc TTImp
expandLhs = map (\pc => appNames pc.name (map (name . snd) pc.args))

-- -- TODO: revisit use of believe_me if it's causing issues with type resolution or repl evaluation
-- ||| Bring together generated lhs/rhs patterns.
-- ||| Handle cases of empty types or phantom types.
-- ||| Foldable has a default value to result in so we don't use believe_me
-- makeFImpl : Foldable t => Zippable t => FParamTypeInfo -> (isFoldable: Bool) -> t TTImp -> t TTImp -> TTImp
-- makeFImpl fp isFold lhs rhs =
--   case (isPhantom fp, null fp.cons, isFold) of
--     (_   ,True,_    ) => iCase (var "z") implicitFalse $ [impossibleClause `(_)] -- No cons, impossible to proceed
--     (True,_   ,False) => `(believe_me z) -- Var is phantom and not for Foldable, safely change type
--     _                 => iCase (var "z") implicitFalse $ toList $ zipWith (.=) lhs rhs

-- TODO: revisit use of believe_me if it's causing issues with type resolution or repl evaluation
||| Bring together generated lhs/rhs patterns.
||| Handle cases of empty types or phantom types.
||| Foldable has a default value to result in so we don't use believe_me
||| Renames machine-named vars to be more basic
export
makeFImpl : Foldable t => Zippable t => BFParamTypeInfo n -> (isFoldable: Bool) -> t TTImp -> t TTImp -> TTImp
makeFImpl fp isFold lhs rhs =
  let vs = map String.singleton $ drop 23 $ cycle $ rangeFromTo 'a' 'z'
      clauses = zipWith (\l,r =>
        let name_map = mkMap $ zipWithStream MkPair (extractNames l) vs
        in (replaceNames name_map l, replaceNames name_map r)) (toList lhs) (toList rhs)
      (rn_lhs,rn_rhs) = unzip clauses
  in  case (isPhantom fp, null fp.cons, isFold) of
        (_   ,True,_    ) => iCase (var "implArg") implicitFalse [impossibleClause `(_)] -- No cons, impossible to proceed
        (True,_   ,False) => `(believe_me implArg) -- Var is phantom and not for Foldable, safely change type
        _                 => iCase (var "implArg") implicitFalse $ toList $ zipWith (.=) rn_lhs rn_rhs
  where
    extractNames : TTImp -> List Name
    extractNames = mapMaybe (\case IVar _ nm => Just nm; _ => Nothing) . snd . unApp

    mkMap : List (Name,String) -> NameMap Name
    mkMap xs = runFresh $ foldlM
      (\m,(n,v) => pure $ NameMap.insert n (srcVarTo_Name' !(getNext v)) m) NameMap.empty xs

genMapTT : BFParamTypeInfo 1 -> TTImp
genMapTT fp = makeFImpl fp False (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenMap : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenMap SkipT x = pure x
    ttGenMap (TargetT _) x = pure `(f ~x)
    ttGenMap (AppT _ l (TargetT _)) x = pure `(map f ~x)
    ttGenMap (AppT _ l r) x = do
        n <- getNextAsName' "y"
        pure $ `(map ~(lambdaArg n .=> !(ttGenMap r (var n))) ~x)
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
    rhss = map (\pc => appAll pc.name (map (\(tag, arg) => runFresh $ ttGenMap tag (var arg.name)) pc.args))


mkFunctorImpl : BFParamTypeInfo 1 -> TTImp
mkFunctorImpl fp = `(MkFunctor $ \f,implArg => ~(genMapTT fp))

||| Derives a `Functor` implementation for the given data type
||| and visibility.
export
FunctorVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FunctorVis vis g = do
    let iname = "Functor"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeBFParamTypeInfo 1 g
      | _ => fail (holeFail 1 iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    when (any hasNegTargetTT allFields) $ fail (contraFail 1 iname dtName) -- reject contravariant uses of the hole type
    pure $ MkInterfaceImpl iname vis []
            (mkFunctorImpl fp)
            (oneHoleImplementationType "Functor" fp g)

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

genFoldMapTT : BFParamTypeInfo 1 -> TTImp
genFoldMapTT fp = makeFImpl fp True (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenFoldMap : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenFoldMap SkipT x = pure `(neutral)
    ttGenFoldMap (TargetT _) x = pure `(f ~x)
    ttGenFoldMap (AppT _ l (TargetT _)) x = pure `(foldMap f ~x)
    ttGenFoldMap (AppT _ l r) x = do
        n <- getNextAsName' "y"
        pure $ `(foldMap ~(lambdaArg n .=> !(ttGenFoldMap r (var n))) ~x)
    ttGenFoldMap (TupleT {n} ts) x = do
        names <- map var <$> replicateA (S (S n)) (srcVarToName' <$> getNext "t")
        let lhs = foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip ts names
        rhs <- foldl1 (\acc,x => `(~acc <+> ~x)) <$> traverse (uncurry ttGenFoldMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenFoldMap (FunctionT _ l r) x = pure `(Foldable_Derive_Error_Report_This) -- can't actually happen

    -- filter SkipF's entirely to avoid <+> on extraneous neutral's
    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => case filter (not . isSkipT . fst) pc.args of
        [] => `(neutral) -- foldl1 instead of foldl to avoid extra <+> on neutral
        cs@(_ :: _) => foldl1 (\acc,x => `(~acc <+> ~x))
          (map (\(tag, arg) => runFresh $ ttGenFoldMap tag (var arg.name)) cs))

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
mkFoldableImpl : BFParamTypeInfo 1 -> TTImp
mkFoldableImpl fp = `(MkFoldable 
                     defaultFoldr
                     (\f,z,t => foldr (flip (.) . flip f) id t z)
                     (\xs => foldr {acc = Lazy Bool} (\ _,_ => False) True xs)
                     (\fm,a0 => foldl (\ma, b => ma >>= flip fm b) (pure a0))
                     (foldr (::) [])
                     (\f,implArg => ~(genFoldMapTT fp))
                     )

||| Derives a `Foldable` implementation for the given data type
||| and visibility.
export
FoldableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FoldableVis vis g = do
    let iname = "Foldable"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeBFParamTypeInfo 1 g
      | _ => fail (holeFail 1 iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    when (any hasFunctionT allFields) $ fail (piFail 1 iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkFoldableImpl fp)
             (oneHoleImplementationType "Foldable" fp g)

||| Alias for `FoldableVis Public`.
export
Foldable : DeriveUtil -> Elab InterfaceImpl
Foldable = FoldableVis Public

genTraverseTT : BFParamTypeInfo 1 -> TTImp
genTraverseTT fp = makeFImpl fp False (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    export
    ttGenTraverse : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenTraverse SkipT x = pure `(pure ~x)
    ttGenTraverse (TargetT _) x = pure `(f ~x)
    ttGenTraverse (AppT _ l (TargetT _)) x = pure `(traverse f ~x)
    ttGenTraverse (AppT _ l r) x = do
        n <- getNextAsName' "y"
        pure $ `(traverse ~(lambdaArg n .=> !(ttGenTraverse r (var n))) ~x)
    ttGenTraverse (TupleT {n} ts) x = do
        names <- map var <$> replicateA (S (S n)) (srcVarToName' <$> getNext "t")
        let lhs = foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip ts names
        rhs <- foldl1 (\acc,x => `(~acc <*> ~x)) <$> traverse (uncurry ttGenTraverse) tts
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
                    then pure $ (tt .$ var arg.name, ns)
                    else do n <- getNextAsName' "larg"
                            pure $ ((tt .$ var n), n :: ns)) (var pc.name,[]) pc.args
        pure $ foldl (\tt,sn => lambdaArg sn .=> tt) body (the (List Name) names)

    export
    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map $ \pc => runFresh $ do
        (a :: aps) <- traverse (\(tag, arg) =>
          ttGenTraverse tag (var arg.name)) (filter (not . isSkipT . fst) pc.args)
                  -- reapply lhs under pure if all vars are SkipT
          | [] => pure $ `(pure) .$ appNames pc.name (name . snd <$> pc.args)
        rc <- conFunc pc
        pure $ foldl (\acc,x => `(~acc <*> ~x)) `(~rc <$> ~a) aps

mkTraversableImpl : BFParamTypeInfo 1 -> TTImp
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
-- TODO, add these to functor and foldable too, to alert when deifned across module bounds

||| Derives a `Traversable` implementation for the given data type
||| and visibility.
export
TraversableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
TraversableVis vis g = do
    let iname = "Traversable"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeBFParamTypeInfo 1 g
      | _ => fail (holeFail 1 iname dtName)
    let allFields = concatMap (map fst . args) fp.cons
    let depsFo = oneHoleImplementationType "Foldable" fp g
    let depsFu = oneHoleImplementationType "Functor" fp g
    () <- checkHasImpl "Traversable" "Foldable" fp.name depsFo
    () <- checkHasImpl "Traversable" "Functor" fp.name depsFu
    when (any hasFunctionT allFields) $ fail (piFail 1 iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkTraversableImpl fp)
             (oneHoleImplementationType "Traversable" fp g)

||| Alias for `TraversableVis Public`.
export
Traversable : DeriveUtil -> Elab InterfaceImpl
Traversable = TraversableVis Public
