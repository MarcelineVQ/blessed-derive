module Util

import Data.Vect -- Vect.Nil

import Data.List -- instance Zippable List

import Language.Reflection.Is

import public Language.Reflection.Derive
%language ElabReflection

-- isIVar, isIPi, etc.
%runElab deriveIs "TTImp" Public

--------------------------------------------------
-- Utils
--------------------------------------------------
public export
replicateA : Applicative m => (n : Nat) -> m a -> m (Vect n a)
replicateA Z act = pure []
replicateA (S k) act = [| act :: replicateA k act |]

namespace ZipStreamL
  export
  zipWithStream : (a -> b -> c) -> List a -> Stream b -> List c
  zipWithStream f [] _ = []
  zipWithStream f (x :: xs) (y :: ys) = f x y :: zipWithStream f xs ys
namespace ZipStreamR
  export
  zipWithStream : (a -> b -> c) -> Stream a -> List b -> List c
  zipWithStream f _ [] = []
  zipWithStream f (x :: xs) (y :: ys) = f x y :: zipWithStream f xs ys

export
%inline
numberedList : Range b => Num b => List a -> List (a,b)
numberedList xs = zipWithStream (\x,y => (x,y)) xs [0..]

export
iterfN : Nat -> (b -> b) -> b -> b
iterfN Z f = id
iterfN (S k) f = f . iterfN k f

{-
getBaseImplementation' : (x : Type) -> Elab x
getBaseImplementation' implTy = do
  tpe <- quote implTy
  let d = `( let x = %search in the ~tpe x )
  z <- check {expected=implTy} d
  pure z
-}