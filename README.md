# Deriving Blessed Interfaces via Idris 2 Elaborator Reflection

Package provides deriving of Functor, Foldable, and Traversable.  
It's intended to also provide the Bi-versions of each and possibly
generalized newtype deriving if the underlying machinery provides enough.

This package is very fresh and my test cases not very inventive, please do submit any datatypes you have issues with so I can nail them down.

`Functor` is restricted to types which do not use its last parameter in a negative function position.  
Given some function `a -> b` the positions can be thought of as negative to the left and positive to the right, `negative` -> `positive`.  
Nesting of the left argument flips this polarity.  
This means that for some type `Foo a b`, its constructors may contain a type such as  
`(a -> b) i.e. (n -> p)` or `((b -> a) -> b) i.e. ((p -> n) -> p)`  
but not `(((b -> a) -> a) -> b) i.e. (((n -> p) -> n) -> p)`  
or `((a -> b) -> b) i.e. (p -> n) -> p `  
Note how in the disallowed cases it's because `b` is `n`egative.

Function types are disallowed entirely in Foldable/Traversable instances.

Deriving is straightforward:
```idris2
import Language.Reflection.Blessed

%language ElabReflection

data Foo f a b = MkFoo (f b) a
%runElab derive [Functor, Foldable, Traversable]
```

If you're instead looking for generics check out the sop package linked below.

## Issues

The largest issue with this as it stands is that there's no warning for missing instances until use. For example you can derive Traversable without deriving Foldable, but won't get an error until you actually use traverse.

The package currently needs efficiency changes for traverse, in that it has extraneous applications of  <*> and the AppT case of map isn't ideal yet.

This doesn't derive indexed types yet, but there's no reason it can't be made to.

## Related Libraries

[sop](https://github.com/stefan-hoeck/idris2-sop) by [Stefan Hoeck](https://github.com/stefan-hoeck)  
[newtype-deriving](https://github.com/MarcelineVQ/idris2-newtype-deriving) by [some jerk](https://github.com/MarcelineVQ)  
