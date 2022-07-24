module Language.Reflection.Test

import Language.Reflection.Blessed
import Language.Reflection.Derive.Bifunctor

%language ElabReflection

data Foffer a b = MkFoffer a b
data Foffer2 a b = MkFoffer2 a
data Foffer3 : Type -> Type -> Type where

data Foffer4 : (Type -> Type) -> Type -> Type -> Type where
  MkFoffer4 : f b -> a -> Foffer4 f a b

data Foffer4' : (Type -> Type) -> Type -> Type -> Type where
  MkFoffer4' : (f a -> a) -> b -> Foffer4' f a b

data Foffer5 : (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  MkFoffer5 : (((((((b -> a)) -> a) -> a) -> a) -> g a) -> f (a -> b)) -> Foffer5 f g a b

data Foffer5' : (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  MkFoffer5' : (g b, b, f a) -> ((((b -> a) -> a) -> a) -> ((f (g b) -> a) -> g a -> f b)) -> Foffer5' f g a b

-- Functor f => Functor (Foffer5 f a) where
--   map f (MkFoffer5 g) = MkFoffer5 $ \p0 => map (\y0,y1 => f (y0 y1)) (g (\p1 => p0 (\p2 => p1 (\p3 => p2 (\p4 => p3 (\p5 => p4 (f p5)))))))


%runElab deriveBlessed "Foffer"  [Functor,Foldable,Traversable]
%runElab deriveBlessed "Foffer2" [Functor,Foldable,Traversable]
%runElab deriveBlessed "Foffer3" [Functor,Foldable,Traversable]
%runElab deriveBlessed "Foffer4" [Functor,Foldable,Traversable]
%runElab deriveBlessed "Foffer4'" [Functor,Foldable]
%runElab deriveBlessed "Foffer5'" [Functor]


getStuff : Name -> Elab ()
getStuff n = do
  -- tyinfo <- getInfo' n
  eff <- getParamInfo' n
  let g = genericUtil eff
  Just fp <- pure $ makeFParamTypeInfo g
    | _ => fail "no"
  r2 <- FunctorVis Public g
  -- r2 <- FoldableVis Public g
  -- r2 <- TraversableVis Public g
  -- logTerm "functorType" 0 "impl" $ impl r1
  -- logTerm "functorType" 0 "type" $ r1.type
  logMsg "wew1" 0 $ show $ map snd fp.params
  -- logMsg "tags" 0 $ show $ map (map fst . args) fp.cons
  -- logMsg "wew3" 0 $ show $ (argTypesWithParamsAndApps (snd fp.holeType) g.argTypesWithParams)
  logMsg "wewLad" 0 $ show $ fp.params
  logMsg "wew2" 0 $ show $ g.argTypesWithParams
  logTerm "wew4" 0 "impl" $ r2.impl
  logTerm "wew4" 0 "type" $ r2.type
  logTerm "wew4" 0 "www" $ g.appliedType
  logMsg "wew4" 0 $ show g.typeInfo.params
--   let rhss = map (\pc => appAll pc.name (map (\(tag, arg) => evalState nats $ ttGenMap tag (toBasicName' arg.name)) pc.args)) fp.cons
--       b = toList rhss
--   traverse_ (logTerm "wew5" 0 "") b
--   let d = (concatMap (map (tpe . snd) . args) fp.cons)
--   let e = map (ttToTagTree (var $ fst fp.holeType)) d
--   traverse_ (logTerm "wew5" 0 "") d
--   traverse_ (logMsg "wew5" 0) $ map show e

  pure ()

-- %runElab getStuff `{Foffer}
-- %runElab deriveBlessed "Foffer" [Functor,Foldable,Traversable]

data Forf a = MkForf (a -> a)
Functor Forf where
  map f (MkForf g) = MkForf $ \x => ?dsfsdf_0 -- contra

data Foo = MkFoo

data FooEnum = FooEnum1 | FooEnum2 | FooEnum3

data FooA a = MkFooA a
-- %runElab getStuff `{FooA}
%runElab deriveBlessed `{FooA} [Functor]

-- tFooA : let t = (MkFooA 'a') in map Prelude.id t = t
-- tFooA = Refl
data FooA' : (x : Type) -> Type where
  MkFooA' : a -> FooA' a
%runElab deriveBlessed `{FooA'} [Functor]
tFooA' : let t = (MkFooA' 'a') in map Prelude.id t = t
tFooA' = Refl

data FooA2 a = MkFooA2 | MkFooA2' a

%runElab deriveBlessed `{FooA2} [Functor]
tFooA2 : let t = (MkFooA2' 'c') in map Prelude.id t = t
tFooA2 = Refl

data FooA3 a = MkFooA3 | MkFooA3' a | MkFooA3'' (FooA3 a)

%runElab deriveBlessed `{FooA3} [Functor]
tFooA3 : let t = (MkFooA3'' (MkFooA3' 'c')) in map Prelude.id t = t
tFooA3 = Refl

data FooAF : (Type -> Type) -> Type -> Type where
  MkFooAF : a -> FooAF f a
  MkFooAF' : f a -> FooAF f a
  MkFooAF'' : FooAF f a -> FooAF f a

%runElab deriveBlessed `{FooAF} [Functor]
tFooAF : let t = (MkFooAF' {f=Maybe} (Just 'c')) in map Prelude.id t = t
tFooAF = ?sdffd

data FooA4 a = MkFooA4 | MkFooA4' a | MkFooA4'' (FooA3 a) | MkFooA4''' (Either Int (FooA4 a))

%runElab deriveBlessed `{FooA4} [Functor]
tFooA4 : let t = (MkFooA4''' (Right $ MkFooA4'' (MkFooA3' 'c'))) in map Prelude.id t = t
tFooA4 = Refl

public export
data FooAK a = MkFooAK

%runElab deriveBlessed `{FooAK} [Functor,Foldable]
tFooAK : let t = MkFooAK in map Prelude.id t = t
tFooAK = Refl

public export
data FooAK2 a b c = MkFooAK2 b

public export
data FooAKG2 : Type -> Type -> Type -> Type where
  MkFooAKG2 : b -> FooAKG2 a b c

public export
record FooAKR2 (a : Type) b (c : Type) where
  constructor MkFooAKR2
  faffo : b
--------------------------------------------------

-- No reason to case, phantoms can merely be treated as the new type
-- A var is phantom if it isn't used anywhere in the constructors
-- export
-- Functor FooAK where
  -- map _ = believe_me

-- export
-- Foldable FooAK where
--   foldr _ = believe_me

export
Functor (FooAK2 a b) where
  map _ = believe_me 

export
Functor (FooAKR2 a b) where
  map _ = believe_me

export
Functor (FooAKG2 a b) where
  map _ = believe_me

-- similarily for void
-- A var is void when there aren't any constructors to use it
data VoidFoo : Type -> Type where

Functor VoidFoo where
  map _ _ impossible

export
foof : (a -> b) -> VoidFoo a -> VoidFoo b
foof = \f,x => case x of _ impossible

data Foo2 a = MkFoo2 a a

data Tree1 a = Leaf1 | Branch1 (Tree1 a) a (Tree1 a)
data Tree1' a = Leaf1' | Branch1' (Tree1' a) a (Tree1' a)

-- the default generated Foldable for Tree is depth first, as opposed to this which is breadth-first
export
[off] Foldable Tree1 where
  foldr f acc Leaf1 = acc
  foldr f acc (Branch1 x y z) = f y (foldr f (foldr f acc z) x)


data Tree2 a = Leaf2 a | Branch2 (Tree2 a) (Tree2 a)

data Tree3 a = Leaf3 | Branch3 (Tree1 a) a (Tree2 a)

data F1 a b = MkF1 (a -> b)

data F1' a b c = MkF1' (a -> b -> c)

Functor (F1' a b) where
  map f (MkF1' g) = MkF1' $ \q,r => f (g q r)

public export
data F2 a b c = EmptyF2 | PureF2 a | MkF2 c (a -> b)

data F2' : Type -> Type -> Nat -> Type -> Type where
  EmptyF2' : F2' a b 0 c
  PureF2' : a -> F2' a b 1 c
  MkF2' : c -> (a -> b) -> F2' a b 2 c

data F2'' : Type -> Type -> Type -> Type where
  EmptyF2'' : F2'' a b c
  PureF2'' : a -> F2'' a b c
  MkF2'' : c -> Either Char (b -> c) -> F2'' a b c

data F3 : Type -> (Type -> Type) -> Type -> Type where
  MkF3 : (a -> f b) -> F3 a f b

data F4 a b = MkF4 (b -> a)
data F5 : (f : Type -> Type) -> Type -> Type -> Type where
  MkF5 : (b -> f a) -> (a -> f b) -> F5 f a b

-- Functor Tree1 where
--   map f Leaf1 = Leaf1
--   map f (Branch1 x y z) = Branch1 (map f x) (f y) (map f z)

-- Functor Tree2 where
--   map f (Leaf2 x) = Leaf2 (f x)
--   map f (Branch2 x z) = Branch2 (map f x) (map f z)

-- Functor Tree3 where
--   map f Leaf3 = Leaf3
--   map f (Branch3 x y z) = Branch3 (map f x) (f y) (map f z)

Functor (F2 a b) where
  map f EmptyF2 = EmptyF2
  map f (PureF2 x) = PureF2 x
  map f (MkF2 x g) = MkF2 (f x) g

Functor (F1 a) where
  map f (MkF1 g) = MkF1 $ f . g

-- I need to determine if any parameters guard the use of the final param, in which case they also need Functor, e.g.:
Functor f' => Functor (F3 a f') where
  map f (MkF3 g) = MkF3 $ map f . g
-- In the above case idris will be unable to locate an instance for f, if we don't do this
-- This is distinct from if it was, say, (a -> Either a b), since idris can search directly to see if (Either a) has a Functor instance

Functor (F4 a) where
  map f (MkF4 g) = MkF4 $ \b => ?sdfds -- let r = contramap g?dsffsd ?sdfd b

data Foo' : (Type -> Type -> Type) -> Type -> (Type -> Type) -> Type -> Type where
  MkFoo' : g (f b) a -> f a -> a -> Foo' g b f a

Functor f => Functor (g (f b)) => Functor (Foo' g b f) where
  map h (MkFoo' x y z) = MkFoo' (map h x) (map h y) (h z)


-- Foldable FooA where
--   foldr = defaultFoldr
--   foldMap f (MkFooA x) = f x

-- F2 demonstrates that if `c` is used nowhere then we are forced to use neutral
-- It also shows that g isn't possible to use, so we don't
-- Foldable (F2 a b) where
--   foldr = defaultFoldr
--   foldMap f EmptyF2 = neutral
--   foldMap f (PureF2 x) = neutral
--   foldMap f (MkF2 x g) = f x

-- Traversable (F2 a b) where
--   traverse f EmptyF2 = pure EmptyF2
--   traverse f (PureF2 x) = pure $ PureF2 x
--   traverse f (MkF2 x g) = (\r => MkF2 r g) <$> f x

export
infoF2 : TypeInfo
infoF2 = getInfo "F2"

export
infoF3 : TypeInfo
infoF3 = getInfo "F3"

export
infoF4 : ParamTypeInfo
infoF4 = getParamInfo "F4"

export
infoF4F : FParamTypeInfo
infoF4F = case makeFParamTypeInfo (genericUtil infoF4) of
            Just x => x
            Nothing => believe_me 0

data FooTup a = MkFooTup (Int,a,Char)

data FooTup2 a b = MkFooTup2 (Int,a,b,Char)

export
infoFooTup : ParamTypeInfo
infoFooTup = getParamInfo "FooTup"

export
infoFooTup2 : ParamTypeInfo
infoFooTup2 = getParamInfo "FooTup2"


export
infoFooTup2F : FParamTypeInfo
infoFooTup2F = case makeFParamTypeInfo (genericUtil infoFooTup2) of
            Just x => x
            Nothing => believe_me 0

export
infoFooTupF : FParamTypeInfo
infoFooTupF = case makeFParamTypeInfo (genericUtil infoFooTup) of
            Just x => x
            Nothing => believe_me 0

data Raf : Type -> Type -> Type where
  -- MkRaf : a -> b -> Maybe b -> (a,b) -> (a -> a -> b) -> Raf a b
  -- MkRaf : (a,b) -> Raf a b
  -- MkRaf : a -> b -> Maybe b -> (a,b) -> Raf a b
  MkRaf : a -> b -> Maybe b -> (a -> b) -> (a,b,a,Char) -> (Int -> Bool -> Char) -> Raf a b

export
infoRaf : ParamTypeInfo
infoRaf = getParamInfo "Raf"

export
infoRafF : FParamTypeInfo
infoRafF = case makeFParamTypeInfo (genericUtil infoRaf) of
            Just x => x
            Nothing => believe_me 0

-- %runElab getStuff `{Raf}
%runElab deriveBlessed `{Raf} [Functor]

borb' : let t = (MkRaf 'a' Z (Just Z) (const Z) ('a',Z,'a','c') (\_,_ => 'f')) in map Prelude.id t = t
borb' = Refl

export
infoFooA4p : ParamTypeInfo
infoFooA4p = getParamInfo "FooA4"

export
infoFooAF : ParamTypeInfo
infoFooAF = getParamInfo "FooAF"

export
infoVoidFoo : ParamTypeInfo
infoVoidFoo = getParamInfo "VoidFoo"

-- %runElab getStuff `{VoidFoo}

data T a = T1 Int a | T2 (T a)
data S a b = S1 (List b) | S2 (a, b, b)
data H : Type -> Type -> Type where
  H1 :  (List b) -> H a b
  H1' : (0 r : b) -> (List b) -> H a b
  H2 : (a, b, b) -> H a b

export
infoT : ParamTypeInfo
infoT = getParamInfo "T"

export
infoS : ParamTypeInfo
infoS = getParamInfo "S"

export
infoH : ParamTypeInfo
infoH = getParamInfo "H"

%runElab deriveBlessed `{T} [Functor]
%runElab deriveBlessed `{S} [Functor]

-- instance Functor (S a) where
--   fmap f (S1 bs)    = S1 (fmap f bs)
--   fmap f (S2 (p,q)) = S2 (a, fmap f q)



data Fraf : (Type -> Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  MkFraf : (gorp : g (f a) (h b)) -> Fraf g f h a b
%runElab deriveBlessed `{Fraf} [Functor]
tFraf1 : let t = (MkFraf (Right $ Just 'c'))
         in  map {f=Fraf Either Maybe Maybe Bool} Prelude.id t = t
tFraf1 = Refl
tFraf2 : let t = (MkFraf (Left (Nothing {ty = Bool})))
         in  map {f=Fraf Either Maybe Maybe Bool} Prelude.id t = t
tFraf2 = Refl

export
infoFraf : ParamTypeInfo
infoFraf = getParamInfo "Fraf"

export
infoFrafF : FParamTypeInfo
infoFrafF = case makeFParamTypeInfo (genericUtil infoFraf) of
            Just x => x
            Nothing => believe_me 0
-- %runElab getStuff `{Fraf}


data FooAZ : Type -> Type -> (Type -> Type) -> Type where
  MkFooAZ : a -> FooAZ a b f

-- %runElab deriveBlessed `{F1} [Functor,Foldable] -- function type
-- %runElab deriveBlessed `{F4} [Functor] -- contra
-- %runElab deriveBlessed `{FooAZ} [Functor] -- not (Type -> Type)


%runElab deriveBlessed `{FooA} [Foldable,Traversable]
%runElab deriveBlessed `{FooA'} [Foldable]
%runElab deriveBlessed `{FooA2} [Foldable]
%runElab deriveBlessed `{FooA3} [Foldable]
%runElab deriveBlessed `{FooAF} [Foldable]
%runElab deriveBlessed `{F2} [Foldable]

-- next type to explore, one pi is applied recheck the rules
data Bobo : (Type -> Type) -> Type -> Type -> Type where
  MkBobo : (a -> f b) -> Bobo f a b

-- next type to explore, one pi is applied recheck the rules
data BoboT : (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  MkBoboT : (f b, b, d a) -> BoboT d f a b

-- %runElab getStuff `{Bobo}
-- %runElab deriveBlessed `{Bobo} [Functor,Foldable,Traversable]
%runElab deriveBlessed `{Bobo} [Functor]

-- %runElab getStuff `{BoboT}
%runElab deriveBlessed `{BoboT} [Foldable]

{-
-- This works in haskell, though it's a pain to test!
-- it's just a long-winded way to map f b and f (a -> b)
dd = MkDD (\i1 i2 -> (i1,Just 'c', (\i3 vc -> (Just chr))))
MkDD vc = fmap @(DD Maybe Int) toUpper dd
(x,y,z) = vc 1 2
y = Just 'C'
Just g = z 1 'd'
g 105 = 'I'
g 73 = 'I'
-}

-- This is looping during FunctorVis for some reason. fp is fine
data DooDad : (Type -> Type) -> Type -> Type -> Type where
  -- MkDooDad : f (a -> b) -> DooDad f a b
  MkDooDad : f b -> DooDad f a b

data DooDad2 : (Type -> Type -> Type) -> (Type -> Type)-> (Type -> Type) -> Type -> Type -> Type where
  MkDooDad2 : (g (f a) (h (a -> b))) -> DooDad2 g f h a b

%runElab getStuff `{DooDad2}

-- Functor h => Functor (g (f a)) => Functor (DooDad2 g f h a) where
  -- map f (MkDooDad2 x) = MkDooDad2 $ map (\y => map (\y',b => f (y' b)) y) x

data ContraDad : Type -> Type -> Type where
  -- MkContraDad : (Int -> a) -> ContraDad a
  -- MkContraDad : ((Int -> Int) -> a) -> ContraDad a b
  MkContraDad : ((Char -> Int) -> a) -> ContraDad b a
  -- MkContraDad : ((b -> a) -> b) -> ContraDad a b
  -- MkContraDad : ((((b -> a) -> a) -> a) -> b) -> ContraDad a b

-- Functor (ContraDad a) where
  -- map f (MkContraDad z) = MkContraDad $ \p0 => f (z (\p1 => p0 (\p2 => p1 (\p3 => p2 (f p3)))))


-- Functor (ContraDad a) where
  -- map f (MkContraDad g) = MkContraDad $ ?sdsdf

-- This is looping during FunctorVis for some reason. fp is fine
data DooDadL : Type -> Type -> Type where
  MkDooDadL : ((b -> a) -> a -> b) -> DooDadL a b

Functor (DooDadL a) where
  map f (MkDooDadL z) = MkDooDadL $ \b1,b2 => f (z (\y => b1 (f y)) b2)
-- given
-- \b1,b2 => f (z (\y => f (b1 y)) b2)

data DooDadLT : (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type -> Type where
  -- MkDooDadLT : ((b -> a) -> (((a,b,c) -> a) -> f (g b)) -> b) -> DooDadLT f g c a b
  -- MkDooDadLT : ((b -> a) -> (f (g b) -> b)) -> DooDadLT f g c a b
  MkDooDadLT : ((a -> b) -> b) -> DooDadLT f g c a b

-- Functor f => Functor g => Functor (DooDadLT f g h i) where
  -- map f (MkDooDadLT g) = MkDooDadLT $ \z => ?dsdsdfsfsdf
-- Functor f => Functor g => Functor (DooDadLT f g h i) where
--   map f (MkDooDadLT z) = MkDooDadLT $ \p0,p2 => f
--     (z (\p1 => p0 (f p1)) (\p3 => map (map ?sdfe)
--          (p2 (\p4 => p3 (case p4 of (t5,t6,t7) => (t5, ?dsf, t7))))))


-- %runElab getStuff `{DooDad}
-- %runElab getStuff `{DooDad2}
%runElab deriveBlessed `{DooDad} [Functor]
%runElab deriveBlessed `{DooDad2} [Functor]
%runElab deriveBlessed `{ContraDad} [Functor]
%runElab deriveBlessed `{DooDadL} [Functor]
-- %runElab deriveBlessed `{DooDadLT} [Functor]


data Borpa : (Type -> Type) -> Type -> Type -> Type where
  MkBorpa : f a -> b -> a -> f b -> Borpa f a b

-- %runElab getStuff `{Borpa}
%runElab deriveBlessed `{Borpa} [Functor]
%runElab deriveBlessed `{Borpa} [Foldable,Traversable]



-- Regrettably, this won't check if Foldable is missing until you use traverse
-- %runElab getStuff `{Tree1}
%runElab deriveBlessed `{Tree1} [Functor,Foldable,Traversable]
%runElab deriveBlessed `{Tree2} [Functor,Foldable,Traversable]
%runElab deriveBlessed `{Tree3} [Functor,Foldable,Traversable]

-- This should be an error but it's not! We've already derived this!
-- It won't even error when you use map oddly enough.
Functor FooA where
  map f (MkFooA x) = MkFooA (f x)

data Travo : (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  MkTravo1 : f a -> Travo f g a b
  MkTravo1' : a -> f a -> g a -> Travo f g a b
  MkTravo2 : f b -> Travo f g a b
  MkTravo3 : a -> f b -> g b -> Travo f g a b
  MkTravo4 : f b -> a -> f (g b) -> b -> g b -> Travo f g a b

%runElab getStuff `{Travo}
%runElab deriveBlessed `{Travo} [Functor,Foldable,Traversable]
-- %runElab deriveBlessed `{Travo} [Bifunctor]

-- data FooG : (Type -> Type) -> Type -> Type -> Type where
--   MkFooG : f b -> a -> FooG f a b

-- %runElab deriveBlessed "FooG" [Functor, Foldable, Traversable]



main : IO ()
main = pure ()
