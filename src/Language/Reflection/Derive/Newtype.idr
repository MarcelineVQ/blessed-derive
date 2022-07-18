module Language.Reflection.Derive.Newtype

-- WIP for now

{-

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types

import System

import Language.Reflection
import Language.Reflection.Syntax

import Prelude.Interfaces -- MkFunctor

import Data.String
import Text.PrettyPrint.Prettyprinter.Doc
import Text.PrettyPrint.Prettyprinter.Render.String

import Data.Contravariant

import Language.Reflection.Derive
%language ElabReflection

-- not newtype
data Foo = MkFoo

-- not newtype
data FooEnum = FooEnum1 | FooEnum2 | FooEnum3

-- newtype
data FooA a = MkFooA a

-- newtype
data FooInt = MkFooInt Int

-- not newtype
data FooA2 a = MkFooA2 | MkFooA2' a

-- not newtype
data FooAK a = MkFooAK

-- newtype
data F1 a b = MkF1 (a -> b)

-- newtype
data F1' : (Type -> Type) -> Type -> Type -> Type where
  MkF1' : (a -> f b) -> F1' f a b

-- newtype
data F1'' : (Type -> Type) -> Type -> Type -> Type -> Type where
  MkF1'' : (a -> b -> f c) -> F1'' f a b c

Num FooInt where
  (MkFooInt x) + (MkFooInt y) = MkFooInt (x + y)
  (MkFooInt x) * (MkFooInt y) = MkFooInt (x * y)
  fromInteger x = MkFooInt $ fromInteger x

Num b => Num (F1 a b) where
  (MkF1 f) + (MkF1 g) = MkF1 (\x => f x + g x)
  (MkF1 f) * (MkF1 g) = MkF1 (\x => f x * g x)
  fromInteger i = MkF1 (\_ => fromInteger i)

Num (f b) => Num (F1' f a b) where
  (MkF1' f) + (MkF1' g) = MkF1' (\x => f x + g x)
  (MkF1' f) * (MkF1' g) = MkF1' (\x => f x * g x)
  fromInteger i = MkF1' (\_ => fromInteger i)

Num (f c) => Num (F1'' f a b c) where
  (MkF1'' f) + (MkF1'' g) = MkF1'' (\x,y => f x y + g x y)
  (MkF1'' f) * (MkF1'' g) = MkF1'' (\x,y => f x y * g x y)
  fromInteger i = MkF1'' (\_,_ => fromInteger i)

init' : List a -> List a
init' (x :: xs@(_ :: _)) = x :: init xs
init' [x] = []
init' [] = []


||| Given a `TTImp` representing an interface, generates
||| the type of the implementation function with all type
||| parameters applied and auto implicits specified.
|||
||| Example: Given the `DeriveUtil` info of `Either`, this
||| will generate the following type for input ``(Eq)`:
|||
||| ```idris example
||| {0 a : _} -> {0 b : _} -> Eq a => Eq b => Eq (Either a b)
||| ```


-- not newtype
data Foo' : (Type -> Type -> Type) -> Type -> (Type -> Type) -> Type -> Type where
  MkFoo' : g (f b) a -> f a -> a -> Foo' g b f a

Functor f => Functor (g (f b)) => Functor (Foo' g b f) where
  map h (MkFoo' x y z) = MkFoo' (map h x) (map h y) (h z)

-- newtype
data Foo'' : (Type -> Type -> Type) -> Type -> (Type -> Type) -> Type -> Type where
  MkFoo'' : g (f b) a -> (0 _ : f a) -> (0 _ : a) -> Foo'' g b f a

-- Is this reasonable, at all? It should be safe since M0 fields aren't available to call.
0 emptyField : String -> a
emptyField str = unsafePerformIO $ die "Impossible error: A 0-use field of \{str} was used."

-- Is it more right to re-use w or s below, or to pass along our fake error-carrier?
Num (g (f b) a) => Num (Foo'' g b f a) where
  (MkFoo'' x z w) + (MkFoo'' y v s) = MkFoo'' (x + y) (emptyField "Foo''") (emptyField "Foo''")
  (MkFoo'' x z w) * (MkFoo'' y v s) = MkFoo'' (x * y) (emptyField "Foo''") (emptyField "Foo''")
  fromInteger x = MkFoo'' (fromInteger x) (emptyField "Foo''") (emptyField "Foo''")

shedOne : TTImp -> TTImp
shedOne (IApp _ l r) = r
shedOne tt = tt

-- This also needs special consideration for function-typed fields.
-- consider how only the final argument of a function type tends to need a constraint
-- e.g. Num b => Num (a -> b)
export
implementationTypeNT : (iface : TTImp) -> (ntUtil : DeriveUtil) -> TTImp
implementationTypeNT iface (MkDeriveUtil _ appTp names argTypesWithParams) =
    let appIface = iface .$ appTp
        implVars = argTypesWithParams -- vars which imply needed impls e.g. Num b required for F1
        autoArgs = pi (MkArg MW AutoImplicit (Just "pre") (iface .$ shedOne appTp)) appIface -- piAllAuto appIface $ map (iface .$) implVars
     in piAllImplicit autoArgs names


export
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

export
toBasicName' : Name -> TTImp
toBasicName' = var . UN . Basic . nameStr

export
appLevels : Name -> TTImp -> Nat -> TTImp
appLevels n _  Z = var n
appLevels n fn (S k) = fn .$ (appLevels n fn k)

-----------------------------------------------------------
-- Deriving can be provided for more than just single parameter interfaces like Num
-- examine this comprehensive case:
public export
interface Biz a b where
  constructor MkBiz
  biz : a -> Int -> a -> b
  borp : b -> a
  fiz : Maybe Char
  0 forp : a

export
Biz Int Char where
  biz x i y = chr $ x + i + y
  borp = ord
  fiz = Nothing
  forp = emptyField "Biz_Int_Char"

export
Biz a b => Biz a (FooA b) where
  biz x y z = MkFooA $ biz x y z
  borp (MkFooA x) = borp x
  fiz = Just 'b'
  forp = emptyField "Biz_a_FooA_b"

-- conceptually we're making this below, relying on the compiler to remove the extra contructors
export
-- (be : Biz Int Char) => Biz Int (FooA Char) where
--   biz x y z = biz @{be} x y z
--   borp x = borp @{be} x
--   fiz = fiz @{be}
--   forp = emptyField "Biz_a_FooA_b"

Biz a b => Biz (FooA a) b where
  biz (MkFooA x) y (MkFooA z) = biz x y z
  borp x = MkFooA $ borp x
  fiz = Just 'a'
  forp = emptyField "Biz_FooA_a_b"

-- This example is technially overlapping due to the above combined with `Biz a b => ...`
Biz a b => Biz (FooA a) (FooA b) where
  biz (MkFooA x) y (MkFooA z) = MkFooA $ biz x y z
  borp (MkFooA x) = MkFooA $ borp x
  fiz = Just 'c'
  forp = emptyField "Biz_FooA_a_FooA_b"


-- We unwrap our newtype, but leave other arguments as they are, applying them all as required by the field
-- ^ how do I define a %runElab `{FooA} [Newtype `{Biz}], allowing for selecting FooA for the a or b?
-- %runElab `{FooA} [Newtype `(Biz _ a)]   %runElab `{FooA} [Newtype `(Biz a _)]  ?
-----------------------------------------------------------

record NewtypeUtility where
  constructor MkNewtypeUtility
  -- We can pass along the DeriveUtil, so
  -- I require this to hold only what I need, iow the newtype name and its fields marked with whether they're 0 or not

  ||| The type constructor name of the newtype
  name : Name  

  ||| The data constructor name of the newtype
  conName : Name

  ||| Fully applied data type, i.e. `var "Either" .$ var "a" .$ var "b"`
  appliedType        : TTImp

  ||| The ordered fields of the newtype, along with a marker of whether they're 0-use
  conFields : List (ExplicitArg, Bool)

export
toLam : List NamedArg -> List Name -> TTImp -> TTImp
toLam [] ns tt = foldl (.$) tt (reverse (map var ns))
toLam (MkArg _ _ n _ :: xs) ns tt = lambdaArg n .=> toLam xs (n :: ns) tt

{-

:exec putPretty $ toLam [MkArg M0 ExplicitArg "n" (var "ty"),MkArg M0 ExplicitArg "m" (var "ty")] [] $ var "MkFooA" .$ `(~(var "+") @{~(var "pre")}) 

-}

-- each field is of the interface record to define
export
genField : (ntUtil : NewtypeUtility) -> (implField : (Name, Count, (List NamedArg, TTImp))) -> TTImp
genField ntg (n,c,(args,_)) = if c == M0
    then `(emptyField (nameStr ntUtil.name))
    -- else toLam args [] $ (var ntg.conName .$ `(~(var n) @{~(var "pre")}))
    else `(believe_me)
  -- where
  --   toLam : List NamedArg -> List Name -> TTImp -> TTImp
  --   toLam [] ns tt = foldl (.$) tt (reverse (map var ns))
  --   toLam (MkArg _ _ n _ :: xs) ns tt = lambdaArg n .=> toLam xs (n :: ns) tt


record ImplementationUtil where
  constructor MkImplementationUtil
  name : Name
  fields : List (Name, Count, (List NamedArg, TTImp))

-- map genField over each field and collect
mkNTImpl : (implConName : Name) -> (ntUtil : NewtypeUtility) -> (implUtil : ImplementationUtil) -> TTImp
mkNTImpl implConName ntg implUtil = appAll implConName $ map (genField ntg) (implUtil.fields)

tagIf0Use : ExplicitArg -> (ExplicitArg, Bool)
tagIf0Use arg = (arg, arg.uses == M0)

isNewType' : ParamTypeInfo -> Maybe NewtypeUtility
isNewType' ti = case ti.cons of
  [con] => Just $ let pNames = map fst $ params ti
                      appTpe = appNames (name ti) pNames
                  in  MkNewtypeUtility ti.name con.name appTpe (map (\arg => (arg, arg.uses /= M0)) con.explicitArgs)
  _   => Nothing

-- Is it worthwhile to find out if the presence of the %noNewtype pragma can be discovered
||| Check if this type is a Newtype.
||| A newtype has one data constructor with one non-erased field.
isNewType : ParamTypeInfo -> Bool
isNewType pt = isJust (isNewType' pt)

public export
getBaseImplementation' : (x : Type) -> Elab x
getBaseImplementation' implTy = do
  tpe <- quote implTy
  let d = `( let x = %search in the ~tpe x )
  z <- check {expected=implTy} d
  pure z

export %macro
getBaseImplementation : (x : Type) -> Elab x
getBaseImplementation = getBaseImplementation'

export
getBaseImplementationTT : (x : Type) -> Elab TTImp
getBaseImplementationTT x = getBaseImplementation' x >>= \z => quote z

-- %runElab do z <- getBaseImplementationTT (Foldable List)
            -- logTerm "" 0 "" z
            -- pure ()

makeImplementationUtil : Name -> Elab ImplementationUtil
-- makeImplementationUtil n = do
  -- getBaseImplementationTT


||| Derives an implementation of the given interface for the given newtype.
export
NewtypeAnyVis : Name -> Visibility -> (newtypeUtil : DeriveUtil) -> Elab InterfaceImpl
NewtypeAnyVis n vis g = do
  -- build the impl record, including named fields
  h <- genericUtil <$> getParamInfo' n
  (MkParamTypeInfo _ _ cs) <- pure $ h.typeInfo
  (con :: Nil) <- pure cs | _ => fail "not a single constructor"
  let implFields = con.explicitArgs
  fieldArgs <- traverse (\arg => pure (arg.name, arg.uses, !(unPiNamed (arg.tpe)))) implFields
  let implUtil = MkImplementationUtil n fieldArgs
      r = map (\(x,y,(z,z2)) => z2) fieldArgs
  traverse_ {f=Elab} (logTerm "fields" 0 (nameStr n)) r
  traverse_ {f=Elab} (logMsg "fieldsTT" 0 . show) (map (\(x,y,(z,z2)) => map (show . type) z ) fieldArgs)
  case isNewType' g.typeInfo of
    Just ntg => pure $ MkInterfaceImpl (nameStr n) vis [] (mkNTImpl (name con) ntg implUtil) (implementationTypeNT (var n) g)
    _ =>      fail $ show g.typeInfo.name ++ " is not a newtype."

||| Alias for `EqVis Public`.
export
Newtype : Name -> DeriveUtil -> Elab InterfaceImpl
Newtype n = NewtypeAnyVis n Public

getStuff : Elaboration m => Name -> m ()
getStuff n = do
  -- tyinfo <- getInfo' n
  eff <- getParamInfo' n
  -- logMsg "" 0 (show $ tyinfo.name)
  -- the pprinter does an assload of nat figuring that shits up the compile time
  -- logMsg "freaf" 0 $ renderString . layoutPretty defaultLayoutOptions $ (indent 2 $ vsep ["", pretty {ann = ()} eff, "",""])
  let usedArgs = calcArgTypesWithParams eff
  -- logMsg "usedArgs" 0 $ show usedArgs
  let g = genericUtil eff
  -- let b = doFunctor eff g
  -- logTerm "freafo" 0 "" $ impl b
  -- logTerm "freafo" 0 "" $ type b
  -- logTerm "freafo1" 0 "" $ type b
  -- logTerm "functorType" 0 "" $ r
  -- logMsg "functorType" 0 $ show usedArgs
  logMsg "functorType" 0 $ show $ implementationTypeNT `(Num) g
  let x : Biz Int (FooA Char)
      x = %search
  -- r <- check {expected=Biz Int (FooA Char)} `(%search)
  z <- quote x
  -- z' <- quote r
  logTerm "functorType" 0 "" $ z
  -- logTerm "functorType" 0 "" $ z'
  pure ()

  
  -- logMsg "functorType" 0 $ show eff.name
  -- logMsg "functorTypePTypes" 0 $ show $ map (show . map paramTypes . explicitArgs) eff.cons
  -- logMsg "functorTypeTPE" 0 $ show $ map (show . map tpe . explicitArgs) eff.cons

  -- logTerm "functorType" 0 "" $ b
  
  pure ()
  
export
infoFoo' : TypeInfo
infoFoo' = getInfo "Foo'"

export
infoNum : ParamTypeInfo
infoNum = getParamInfo "Num"

export
infoFooA : TypeInfo
infoFooA = getInfo "FooA"

export
infoFooAp : ParamTypeInfo
infoFooAp = getParamInfo "FooA"

export
infoF1'' : ParamTypeInfo
infoF1'' = getParamInfo "F1''"

data N : Type -> Type -> Type where
  N1 : (0 _ : a) -> (a -> b) -> N a b

data T a = T1 Int a | T2 (T a)
data S a b = S1 (List b) | S2 (a, b, b)
data H : Type -> Type -> Type where
  H1 :  (List b) -> H a b
  H1' : (0 r : b) -> (List b) -> H a b
  H2 : (a, b, b) -> H a b

export
infoN : ParamTypeInfo
infoN = getParamInfo "N"

export
infoT : ParamTypeInfo
infoT = getParamInfo "T"

export
infoS : ParamTypeInfo
infoS = getParamInfo "S"

export
infoH : ParamTypeInfo
infoH = getParamInfo "H"


||| macro version of `getParamInfo`.
export %macro
getInfo' : Name -> Elab (List (Name, NameInfo))
getInfo' = getInfo

export
getInfo'' : List (Name, NameInfo)
getInfo'' = getInfo' `{Functor}

-- getInfo'' : List (Name, NameInfo)
-- getInfo'' = %runElab getInfo''

%runElab getStuff `{FooA}
%runElab derive `{FooA} [Newtype `{Num},Newtype `{Show}]

main : IO ()
main = pure ()

-}