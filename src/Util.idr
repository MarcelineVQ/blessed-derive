module Util

import Data.Vect -- Vect.Nil
import Data.DPair -- Subset

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
namespace ZipStreamVL
  export
  zipWithStream : (a -> b -> c) -> Vect n a -> Stream b -> Vect n c
  zipWithStream f [] _ = []
  zipWithStream f (x :: xs) (y :: ys) = f x y :: zipWithStream f xs ys

namespace ZipStreamR
  export
  zipWithStream : (a -> b -> c) -> Stream a -> List b -> List c
  zipWithStream f _ [] = []
  zipWithStream f (x :: xs) (y :: ys) = f x y :: zipWithStream f xs ys
namespace ZipStreamVR
  export
  zipWithStream : (a -> b -> c) -> Stream a -> Vect n b -> Vect n c
  zipWithStream f _ [] = []
  zipWithStream f (x :: xs) (y :: ys) = f x y :: zipWithStream f xs ys

export
%inline
numberedList : Range b => Num b => List a -> List (a,b)
numberedList xs = zipWithStream (\x,y => (x,y)) xs [0..]

export
%inline
numberedVect : Range b => Num b => Vect n a -> Vect n (a,b)
numberedVect xs = zipWithStream (\x,y => (x,y)) xs [0..]

export
iterfN : Nat -> (b -> b) -> b -> b
iterfN Z f = id
iterfN (S k) f = f . iterfN k f

export
%inline
maybeToList : Maybe a -> List a
maybeToList = maybe [] (::[])
-- maybeToList' : Maybe a -> List a
-- maybeToList' = lowerMaybe . map (::[])

||| Turn any name into a Basic name
export
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

export
toBasicName' : Name -> TTImp
toBasicName' = var . toBasicName

export
stripLAp : Nat -> TTImp -> Maybe (TTImp,List TTImp)
stripLAp (S n) (IApp fc s u) = mapSnd (++ [u]) <$> stripLAp n s
stripLAp (S n) tt = Nothing
stripLAp Z tt = Just (tt,[])

{-
getBaseImplementation' : (x : Type) -> Elab x
getBaseImplementation' implTy = do
  tpe <- quote implTy
  let d = `( let x = %search in the ~tpe x )
  z <- check {expected=implTy} d
  pure z
-}
