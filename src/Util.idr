module Util

import Data.Vect -- Vect.Nil

import Data.List -- instance Zippable List

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
iterf : Nat -> (b -> b) -> b -> b
iterf Z f = id
iterf (S k) f = f . iterf k f
