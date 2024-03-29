module Language.Reflection.Derive.Types

import Util

import Data.Vect
import Language.Reflection.Derive

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
||| the target type is used contravariantly. It's useful to track the arity of apps
public export
data TagTree : Type where
  SkipT : TagTree -- field to be left alone, either being placed back in as-is (map) or skipped (foldMap)
  TargetT : Nat -> TagTree -- field is our target type and position, typically we apply some `f` to it
  AppT : (arity : Nat) -> TagTree -> TagTree -> TagTree -- field involves application of `f` nested in map/foldMap/traverse
  TupleT : {n:_} -> Vect (S (S n)) TagTree -> TagTree -- fields of a tuple
  FunctionT : Polarity -> TagTree ->  TagTree -> TagTree-- field is of a function type where polarity of arguments is tracked

-- not all that useful, mostly just obscures the intent
public export
foldTagTree : b -> (Nat -> b) -> (Nat -> TagTree -> TagTree -> b)
          -> (forall n. Vect (S (S n)) TagTree -> b)
          -> (Polarity -> TagTree -> TagTree -> b) -> TagTree -> b
foldTagTree skip target app tup func SkipT = skip
foldTagTree skip target app tup func (TargetT k) = target k
foldTagTree skip target app tup func (AppT n x y) = app n x y
foldTagTree skip target app tup func (TupleT xs) = tup xs
foldTagTree skip target app tup func (FunctionT p x y) = func p x y

mutual
  ||| Is the `t`arget type used in a negative argument position?
  ||| e.g. (t -> a) or ((b -> t) -> a)
  ||| Note that nesting to the left continously flips the polarity.
  ||| (neg -> pos) to the left of -> becomes (pos -> neg).
  ||| In effect ((a -> b) -> c) is not contravariant in a, even though (a -> b) is.
  export
  hasNegTargetTT : TagTree -> Bool
  hasNegTargetTT SkipT = False
  hasNegTargetTT (TargetT _) = False
  hasNegTargetTT (AppT _ x y) = hasNegTargetTT x || hasNegTargetTT y
  hasNegTargetTT (TupleT xs) = any hasNegTargetTT xs
  hasNegTargetTT (FunctionT Norm l r) = NegTarget.hasTarget' l || hasNegTargetTT r
  hasNegTargetTT (FunctionT Flip l r) = NegTarget.hasTarget' r || hasNegTargetTT l

  namespace NegTarget
    export
    hasTarget' : TagTree -> Bool
    hasTarget' = foldTagTree False (\_ => True) (\n,x,y => NegTarget.hasTarget' x || NegTarget.hasTarget' y)
      (\xs => any NegTarget.hasTarget' xs) (\p,l,r => hasNegTargetTT (FunctionT p l r))

||| A data constructor from our type we're deriving for
public export
record FParamCon  where
  constructor MkFParamCon
  name : Name
  args : List (TagTree, ExplicitArg)

||| Helper type collecting information we might need during deriving
||| `h` is the number of `h`oles of `Type` at the end of the type signature.
public export
record BFParamTypeInfo (h : Nat) where
  constructor MkBFParamTypeInfo
  name   : Name
  params : Vect paramCount (Name,TTImp)
  holeParams : Vect h (Name,TTImp) -- the hole param names
  appliedTy : TTImp -- fully applied type
  nHoleType : TTImp -- applied type minus hole
  cons : Vect conCount FParamCon

||| Compute a TagTree, from a type TTImp, tracking nestings of pi argument polarity
export
ttToTagTree : (targetType : List (Name,Nat)) -> (typeSig : TTImp) -> TagTree
ttToTagTree t v@(IVar fc nm) = maybe SkipT TargetT (lookup nm t)
ttToTagTree t pi@(IPi fc rig pinfo mnm argTy retTy) = mkpi Norm pi
  where
    mkpi : Polarity -> TTImp -> TagTree
    mkpi p (IPi _ _ _ _ argTy retTy) = FunctionT p (mkpi (neg p) argTy) (mkpi p retTy)
    mkpi p tt = ttToTagTree t tt
ttToTagTree t a@(IApp _ l r) = case unPair a of
    (S (S k) ** xs) => TupleT (map (ttToTagTree t) xs)
    _               => case ttToTagTree t l of
                         l'@(AppT d _ _) => AppT (S d) l' (ttToTagTree t r)
                         l' => AppT 1 l' (ttToTagTree t r)
  where
    unPair : TTImp -> (n ** Vect n TTImp) -- TODO: can %pair pragma affect this?
    unPair (IApp _ `(Builtin.Pair ~l) r) = let (k ** xs) = unPair r in (S k ** l :: xs); unPair tt = (1 ** [tt])
ttToTagTree t _ = SkipT

export
isSkipT : TagTree -> Bool
isSkipT SkipT = True
isSkipT _ = False

||| Prune any TagTree branches without TargetT somewhere
||| This prevents wasteful things like casing on tuples or creating lambdas
||| without values we care about
export
pruneSkipped : TagTree -> TagTree
pruneSkipped SkipT = SkipT
pruneSkipped (TargetT k) = TargetT k
pruneSkipped (AppT n x y) = case (pruneSkipped x, pruneSkipped y) of
    (SkipT,SkipT) => SkipT
    (l,r)         => AppT n l r
pruneSkipped (TupleT xs) =
    let xs' = map pruneSkipped xs
    in  case all isSkipT xs' of
          True => SkipT
          _    => TupleT xs'
pruneSkipped (FunctionT p x y) = case (pruneSkipped x, pruneSkipped y) of
    (SkipT,SkipT) => SkipT
    (l,r)         => FunctionT p l r

||| Compute TagTree and pair with ExplicitArg
||| Prune any branches that don't use our target types
export
makeFParamCon : (holeTypes : List Name) -> ParamCon -> FParamCon
makeFParamCon ts (MkParamCon name explicitArgs) =
  MkFParamCon name $ map (\r => (pruneSkipped $ ttToTagTree (numberedList ts) r.tpe, r)) explicitArgs

-- Failure implies its not a `Type -> ... -> Type` type
-- TODO var renaming should be done here!
export
makeBFParamTypeInfo : (n : Nat) -> DeriveUtil -> Maybe (BFParamTypeInfo n)
makeBFParamTypeInfo n g = do
    -- Applied type in elab-util:genericUtil simply appNames the param names to
    -- generate the appliedType so it's safe to treat params as properly ordered.
    let name = g.typeInfo.name
    -- count off how many params come before our hole params
    (plen ** q) <- overLength n (Vect.fromList g.typeInfo.params)
    -- split them apart
    let (partType,holes) = Vect.splitAt plen q
    -- check holes for being bare IType
    guard $ all isIType (map snd holes)
    let holeNames = holes
    pure $ MkBFParamTypeInfo -- {paramRest = plen}
      name
      -- (rewrite plusCommutative n plen in q)
      partType
      holeNames
      g.appliedType
      (appNames name (toList $ map fst partType))
      (Vect.fromList $ makeFParamCon (toList (map fst holeNames)) <$> g.typeInfo.cons)
  where
    isIType : TTImp -> Bool
    isIType (IType _) = True
    isIType _ = False

export
hasTarget : TagTree -> Bool
hasTarget SkipT = False
hasTarget (TargetT _) = True
hasTarget (AppT _ x y) = hasTarget x || hasTarget y
hasTarget (TupleT xs) = any hasTarget xs
hasTarget (FunctionT p x y) = hasTarget x || hasTarget y

export
hasFunctionT : TagTree -> Bool
hasFunctionT SkipT = False
hasFunctionT (TargetT k) = False
hasFunctionT (AppT arity x y) = hasFunctionT x || hasFunctionT y
hasFunctionT (TupleT xs) = any hasFunctionT xs
hasFunctionT (FunctionT _ x y) = hasTarget x || hasTarget y

||| Is our target parameter in the datatype itself but not any constructor fields
export
isPhantom : BFParamTypeInfo n -> Bool
isPhantom fp = all (not . hasTarget) $ concatMap (map fst . args) fp.cons

export -- testing only
Show TagTree where
  show SkipT = "SkipT"
  show (TargetT n) = "TargetT \{show n}"
  show (AppT n x y) = "AppT \{show n} (" ++ show x ++ ") (" ++ show y ++ ")"
  show (TupleT xs) = "TupleT " ++ assert_total (show xs)
  show (FunctionT p x y) = "FunctionT (" ++ show x ++ ") (" ++ show y ++ ")"
