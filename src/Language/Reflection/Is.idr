module Language.Reflection.Is

import public Language.Reflection.Derive
%language ElabReflection

-- Derive dead-ass isConstructor checking functions
-- Filthy and fun, don't use this really, you're likely to be just as satisfied by
-- `map (\case (Foo _ _) => True; _ => False) some_foos`
-- instead of `map isFoo some_foos`

||| Build an isConstructor function for every constructor of a type
||| e.g.: `data Foo a b = Biz b | MkFoo a` will get you
||| `isBiz : Foo a b -> Bool` `isMkFoo : Foo a b -> Bool`
export
deriveIs : Name -> Visibility -> Elab ()
deriveIs tyName vis= do
    p <- getInfo' tyName
    let decs = p.cons >>= \c => do
      let implName = (fromString "is\{nameStr c.name}")
          implNameVar = var implName
          tyNames = name <$> p.args
          ty = piAllImplicit `(~(appNames p.name tyNames) -> Bool) tyNames
          head = simpleClaim vis implName ty
          cargs = filter isExplicit c.args
          lhs = implNameVar .$ foldl (\acc,x => acc .$ `(_)) (var c.name) cargs
          body = def implName $ [lhs .= `(True)] ++ if length p.cons > 1
            then [implNameVar .$ `(_) .= `(False)]
            else []
      [(head,body)]
    declare $ uncurry (++) $ unzip decs

public export
data Foo : Type -> (Type -> Type) -> Type -> Type where
  MkFoo1 : a -> Foo a f b
  MkFoo2 : b -> Foo a f b
  MkFoo3 : Foo a f b
  MkFoo6 : f a -> Foo a f b
  MkFoo0 : f (f b) -> Foo a f b

%runElab deriveIs "Foo" Public
