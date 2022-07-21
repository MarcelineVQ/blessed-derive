module Language.Reflection.Derive.Functor

import Language.Reflection.Derive.Derive
import public Language.Reflection.Maps

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

--------------------------------------------------
-- Utils
--------------------------------------------------
replicateA : Applicative m => (n : Nat) -> m a -> m (Vect n a)
replicateA Z act = pure []
replicateA (S k) act = [| act :: replicateA k act |]

--------------------------------------------------
-- Helper Types
--------------------------------------------------

||| Tag for how to treat the argument position polarity of a function.
||| Norm = negative -> positive
||| Flip = positive -> negative
||| A negative use of our target type can not have map derived for it.
public export
data Polarity = Norm | Flip

export
Show Polarity where
  show Norm = "Norm"
  show Flip = "Flip"

export
neg : Polarity -> Polarity
neg Norm = Flip
neg Flip = Norm

||| Workhorse of the module, convert a type signature into a tree of tags
||| telling us what fields we need to construct for each implementation.
||| Particularly special cases exists for tuple and function
||| Tuples are treated directly as a bundle of 2 or more fields.
||| Functions need to know their polaity for the purposes of determining whether
||| the target type is used contravariantly.
public export
data TagTree
  = SkipT -- field to be left alone, either being placed back in as-is (map) or skipped (foldMap)
  | TargetT -- field is our target type, typically we apply some `f` to it
  | AppT TagTree TagTree -- field involves application of `f` nested in map/foldMap/traverse
  | TupleT (TagTree,TagTree,List TagTree) -- fields of a tuple
  | FunctionT Polarity TagTree TagTree -- field is of a function type where polarity of arguments is tracked

export -- testing only
Show TagTree where
  show SkipT = "SkipT"
  show TargetT = "TargetT"
  show (AppT x y) = "AppT (" ++ show x ++ ") (" ++ show y ++ ")"
  show (TupleT (x,y,zs)) = "TupleT (" ++ show x ++ ", " ++ show y ++ ", " ++ concatMap (assert_total show) zs ++ ")"
  show (FunctionT p x y) = "FunctionT (" ++ show x ++ ") (" ++ show y ++ ")"

-- not all that useful, mostly just obscures the intent
public export
foldTagTree : b -> b -> (TagTree -> TagTree -> b)
          -> (TagTree -> TagTree -> List TagTree -> b)
          -> (Polarity -> TagTree -> TagTree -> b) -> TagTree -> b
foldTagTree skip target app tup func SkipT = skip
foldTagTree skip target app tup func TargetT = target
foldTagTree skip target app tup func (AppT x y) = app x y
foldTagTree skip target app tup func (TupleT (x,y,zs)) = tup x y zs
foldTagTree skip target app tup func (FunctionT p x y) = func p x y

-- not especially useful either, forgets Polarity and can't differentiate skip and target
export
foldMapTagTree : Monoid m => (TagTree -> m) -> TagTree -> m
foldMapTagTree f SkipT = neutral
foldMapTagTree f TargetT = neutral
foldMapTagTree f (AppT x y) = foldMapTagTree f x <+> foldMapTagTree f y
foldMapTagTree f (TupleT (x,y,zs)) = concatMap (foldMapTagTree f) (x :: y :: zs)
foldMapTagTree f (FunctionT p x y) = foldMapTagTree f x <+> foldMapTagTree f y

||| Compute a TagTree from a type TTImp, tracking nestings of pi argument polarity
export
ttToTagTree : (targetType : TTImp) -> (typeSig : TTImp) -> TagTree
ttToTagTree t v@(IVar fc nm) = if v == t then TargetT else SkipT
ttToTagTree t pi@(IPi fc rig pinfo mnm argTy retTy) = mkpi Norm pi
  where
    mkpi : Polarity -> TTImp -> TagTree
    mkpi p (IPi _ _ _ _ argTy retTy) = FunctionT p (mkpi (neg p) argTy) (mkpi p retTy)
    mkpi p tt = ttToTagTree t tt
ttToTagTree t a@(IApp _ l r) = case unPair a of
    (x :: y :: zs) => TupleT (ttToTagTree t x, ttToTagTree t y, ttToTagTree t <$> zs)
    _             => AppT (ttToTagTree t l) (ttToTagTree t r)
  where
    unPair : TTImp -> List TTImp -- TODO: can %pair pragma affect this?
    unPair (IApp _ `(Builtin.Pair ~l) r) = l :: unPair r; unPair tt = [tt]
ttToTagTree t _ = SkipT

hasTarget : TagTree -> Bool
hasTarget SkipT = False
hasTarget TargetT = True
hasTarget (AppT x y) = hasTarget x || hasTarget y
hasTarget (TupleT (x,y,zs)) = any hasTarget (x :: y :: zs)
hasTarget (FunctionT p x y) = hasTarget x || hasTarget y

mutual
  ||| Is the `t`arget type used in a negative argument position?
  ||| e.g. (t -> a) or ((b -> t) -> a)
  ||| Note that nesting to the left continously flips the polarity.
  ||| (neg -> pos) to the left of -> becomes (pos -> neg).
  ||| In effect ((a -> b) -> c) is not contravariant in a, even though (a -> b) is.
  export
  hasNegTargetTT : TagTree -> Bool
  hasNegTargetTT SkipT = False
  hasNegTargetTT TargetT = False
  hasNegTargetTT (AppT x y) = hasNegTargetTT x || hasNegTargetTT y
  hasNegTargetTT (TupleT (x,y,zs)) = any hasNegTargetTT (x :: y :: zs)
  hasNegTargetTT (FunctionT Norm l r) = hasTarget' l || hasNegTargetTT r
  hasNegTargetTT (FunctionT Flip l r) = hasTarget' r || hasNegTargetTT l

  private
  hasTarget' : TagTree -> Bool
  hasTarget' = foldTagTree False True (\x,y => hasTarget' x || hasTarget' y)
    (\x,y,zs => any hasTarget' (x :: y :: zs)) (\p,l,r => hasNegTargetTT (FunctionT p l r))

-- fafo3 : hasNegTargetTT (ttToTagTree `(b) `(((((b -> a) -> a) -> a) -> f (g b) -> g a -> f b))) = True -- odd -> = neg
-- fafo3 = Refl

hasFunctionT : TagTree -> Bool
hasFunctionT = foldTagTree False False (\x,y => hasFunctionT x || hasFunctionT y)
                 (\x,y,zs => any hasFunctionT (x :: y :: zs)) (\_,l,r => hasTarget' l || hasTarget' r)

isSkipT : TagTree -> Bool
isSkipT SkipT = True
isSkipT _ = False

||| Prune any TagTree branches without TargetT somewhere
||| This prevents wasteful things like casing on tuples or creating lambdas
||| without values we care about
pruneSkipped : TagTree -> TagTree
pruneSkipped SkipT = SkipT
pruneSkipped TargetT = TargetT
pruneSkipped (AppT x y) = case (pruneSkipped x, pruneSkipped y) of
    (SkipT,SkipT) => SkipT
    (l,r)         => AppT l r
pruneSkipped (TupleT (x,y,zs)) =
    let (x',y',zs') = (pruneSkipped x,pruneSkipped y, map pruneSkipped zs)
    in  case (x',y', all isSkipT zs') of
          (SkipT,SkipT,True) => SkipT
          _                  => TupleT (x',y',zs')
pruneSkipped (FunctionT p x y) = case (pruneSkipped x, pruneSkipped y) of
    (SkipT,SkipT) => SkipT
    (l,r)         => FunctionT p l r

-- TODO rename args to fields
||| A data constructor from our type we're deriving for
public export
record FParamCon  where
  constructor MkFParamCon
  name : Name
  args : List (TagTree, ExplicitArg)

||| Helper type collecting information we might need during deriving
public export
record FParamTypeInfo where
  constructor MkFParamTypeInfo
  name   : Name
  params : Vect (S paramCountMinusOne) (Name,TTImp)
  appliedTy : TTImp -- fully applied type
  oneHoleType : TTImp -- applied type minus hole
  holeType :  (Name,TTImp) -- the hole param
  cons : Vect conCount FParamCon

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

||| Is our target parameter in the datatype itself but not any constructor fields
isPhantom : FParamTypeInfo -> Bool
isPhantom fp = all (not . hasTarget) $ concatMap (map fst . args) fp.cons

||| Compute TagTree and pair with ExplicitArg
||| Prune any branches that don't use our target type
makeFParamCon : (holeType : Name) -> ParamCon -> FParamCon
makeFParamCon t (MkParamCon name explicitArgs) =
  MkFParamCon name $ map (\r => (pruneSkipped $ ttToTagTree (var t) r.tpe, r)) explicitArgs

-- Failure implies its not a `Type -> Type` type
export
makeFParamTypeInfo : DeriveUtil -> Maybe FParamTypeInfo
makeFParamTypeInfo g = do
    tiParams@(_ :: _)       <- pure g.typeInfo.params | _ => Nothing
    let params = Vect.fromList tiParams
    (holeTypeName, IType _) <- pure $ last params     | _ => Nothing
    let (oneHoleTT,holeTypeTT) = splitLastVar g.appliedType
        fpcons = fromList $ makeFParamCon holeTypeName <$> g.typeInfo.cons
    pure $ MkFParamTypeInfo g.typeInfo.name params g.appliedType oneHoleTT (holeTypeName,holeTypeTT) fpcons
  where
    -- we've already rejected types without proper params so this should be safe
    splitLastVar : TTImp -> (TTImp,TTImp)
    splitLastVar (IApp _ y l) = (y,l)
    splitLastVar tt = (tt,tt)

-- private
-- Ord Name where
--   compare x y = nameStr x `compare` nameStr y

-- TODO: rework this entirely to be clean like you did for tree tagging
export
oneHoleImplementationType : (iface : TTImp) -> (reqImpls : List Name) -> FParamTypeInfo -> DeriveUtil -> TTImp
oneHoleImplementationType iface reqs fp g =
    let appIface = iface .$ fp.oneHoleType
        functorVars = nub $ argTypesWithParamsAndApps (snd fp.holeType) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (iface .$) functorVars ++ map (\n => app (var n) fp.oneHoleType) reqs
        ty = piAllImplicit autoArgs (toList . map fst $ init fp.params)
        cn = foldr (\(n,tt),acc => NameMap.insert n tt acc) NameMap.empty fp.params
    in replaceNames (evalState VarSrc.empty (nameParams fp.params)) ty
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

oneHoleFail : (impl : String) -> (dtName : String) -> String
oneHoleFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its type does not end in Type -> Type."

------------------------------------------------------------

-- TODO: generate fresh vars for these instead
||| Peel out the names of fields of a constructor into a lhs pattern.
expandLhs : Vect cc FParamCon -> Vect cc TTImp
expandLhs = map (\pc => appNames pc.name (map (toBasicName . name . snd) pc.args))

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

genMapTT : FParamTypeInfo -> TTImp
genMapTT fp = makeFImpl fp False (expandLhs fp.cons) (rhss fp.cons)
  where
    ||| Stateful so that we can create unique variable names as we go
    ttGenMap : MonadState VarSrc m => (tt : TagTree) -> (var : TTImp) -> m TTImp
    ttGenMap SkipT x = pure x
    ttGenMap TargetT x = pure `(f ~x)
    ttGenMap (AppT l TargetT) x = pure `(map f ~x)
    ttGenMap (AppT l r) x = do
        n <- srcVarToName' <$> getNext "y"
        pure $ `(map ~(lambdaArg n .=> !(ttGenMap r (var n))) ~x)
    ttGenMap (TupleT (t1,t2,ts)) x = do
        names <- map var <$> replicateA (2 + length ts) (srcVarToName' <$> getNext "t")
        let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
            tts = zip (t1 :: t2 :: fromList ts) names
        rhs <- Vect.foldr1 (\l,r => `(MkPair ~l ~r)) <$> traverse (uncurry ttGenMap) tts
        pure `(case ~x of ~lhs => ~rhs)
    ttGenMap (FunctionT _ l r) x = do
        n <- srcVarToName' <$> getNext "p"
        pure $ lambdaArg n .=> !(ttGenMap r (x .$ !(ttGenMap l (var n))))

    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => appAll pc.name (map (\(tag, arg) => evalState VarSrc.empty $ ttGenMap tag (toBasicName' arg.name)) pc.args))


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
          (map (\(tag, arg) => evalState VarSrc.empty $ ttGenFoldMap tag (toBasicName' arg.name)) cs))

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
    rhss = map $ \pc => evalState VarSrc.empty $ do
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
checkHasImpl : String -> String -> Name -> TTImp -> Elab ()
checkHasImpl imp req n' tytt = do
    let n = fromString "implSearch\{imp}\{req}\{nameStr n'}"
    declare $ [claim MW Private [] n tytt
              , def n [ var n .= ISearch EmptyFC 1000]]

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
