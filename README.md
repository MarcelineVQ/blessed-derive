# Prelude Interface Deriving via Idris 2 Elaborator Reflection

Package currently provides deriving of Functor, Foldable, and Traversable.  
It will also provide the Bi-versions of each.

`Blessed` is referring to those interfaces defined in the `Prelude`.
Allthough some interfaces don't make sense to derive and won't be included, e.g. `Interpolation`.

This package is very fresh and my test cases not very inventive, please do submit any datatypes you have issues with so I can nail them down.

If you're instead looking for generics check out the sop package linked below.

## Use

`Functor` is restricted to types which do not use their last parameter in a negative function position.  
Given some function `a -> b` the positions can be thought of as negative to the left and positive to the right, `negative` -> `positive`.  
Nesting of the left argument flips this polarity.  
This means that for some type `Foo a b`, its constructors may contain a type such as  
`(a -> b)` / `(n -> p)` or `((b -> a) -> b)` / `((p -> n) -> p)`  
but not `(((b -> a) -> a) -> b)` / `(((n -> p) -> n) -> p)`  
or `((a -> b) -> b)` / `(p -> n) -> p `  
In each disallowed case the `b` is `n`egative.

Datatypes which use their last parameter in a function type at all are disallowed in Foldable/Traversable instances.

Deriving is straightforward:
```idris2
import Language.Reflection.Blessed

%language ElabReflection

data Foo : (Type -> Type) -> Type -> Type -> Type where
  MkFoo : f b -> a -> Foo f a b

%runElab deriveBlessed "Foo" [Functor, Foldable, Traversable]
```

## Issues

The largest issue with this as it stands is that there's no warning for clashing instances until use. You can define Functor yourself and also derive it but there won't be an error until you use map. There may be a clue for solving that in the error you get about defaultFoldr when having clashing Foldables.

This doesn't derive indexed types yet, but there's no reason it can't be made to.

## Next

Other potential/planned instances to derive will include
- `Eq`
- `Ord`
- `Range`
- `Uninhabited`

If possible I'd like to add `generalized newtype deriving` as well which would allow for pretty much any interface to be derived for your type if it's a single constructor type with a single used field, e.g.
```idris
data Foo1 = MkFoo1 Int
data Foo2 a = MkFoo1 a
data Foo3 f g a = MkFoo3 (f (g a) a)
data Foo4 : Type -> Type -> Type where
  MkFoo4 : (0 notUsed : Int) -> (a,b) -> Foo2 a b
```
Derivation would merely be the unwrapping and wrapping of your datatype to use the implementation already defined for the contained field. For example we simply call to the Num instance of Int for Foo1. This is straightforward to write for a given instance like `Num`, the hurdle with `generalized` newtype deriving is generating for any possible given interface.

I'd also like to include some other derivations that I think are cute. Such as `is`:
```idris
data Faf = Faf1 | Faf2 | Faf3 |Faf4
%runelab deriveIs "Faf"

-- deriveIs would cause the following to come into scope:
isFaf1 : Faf -> Bool
isFaf1 Faf1 = True; isFaf1 _ = False

isFaf2 : Faf -> Bool
isFaf2 Faf2 = True; isFaf2 _ = False
...etc
```

## Related Libraries

[sop](https://github.com/stefan-hoeck/idris2-sop) by [Stefan Hoeck](https://github.com/stefan-hoeck)  
[newtype-deriving](https://github.com/MarcelineVQ/idris2-newtype-deriving) by [some jerk](https://github.com/MarcelineVQ)  
