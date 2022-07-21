module Language.Reflection.Maps

-- public exports here are for the purposes of exposing for elaboration

import public Data.Stream         -- nats
import public Control.Monad.State

import public Data.SortedMap
import public Data.SortedMap.Dependent

import public Language.Reflection.Derive

--------------------------------------------------
-- Name Map and Fresh Varible Source
--------------------------------------------------

namespace VarSrc
    ||| Map of Strings to Stream Nat to provide endless, but per-string-sequential, variable names
    export
    VarSrc : Type
    VarSrc = SortedMap String (Stream Nat)

    export
    srcVarToName : (String,Nat) -> Name
    srcVarToName (s,n) = UN . Basic $ (s ++ if n == 0 then "" else show n)

    export
    srcVarToName' : (String,Nat) -> Name
    srcVarToName' (s,n) = UN . Basic $ (s ++ show n)

    export
    empty : VarSrc
    empty = SortedMap.empty

    ||| evalState empty $ getNext' "b"                 === ("b",0)
    ||| evalState empty $ getNext' "b" *> getNext' "b" === ("b",1)
    export
    getNext : MonadState VarSrc m => String -> m (String,Nat)
    getNext s = do
            vm <- get
            case lookup s vm of
              Nothing        => do put (insert s (tail nats) vm); pure (s,0)
              Just (v :: vs) => do put (insert s vs          vm); pure (s,v)

namespace NameMap
    ||| Track name and some associated data
    export
    NameMap : Type -> Type
    NameMap t = SortedMap Name t

    private
    Ord Name where
      compare x y = nameStr x `compare` nameStr y

    export
    insert : Name -> a -> NameMap a -> NameMap a
    insert = SortedMap.insert

    export
    lookup : Name -> NameMap a -> Maybe a
    lookup = SortedMap.lookup
    
    export
    empty : NameMap a
    empty = SortedMap.empty

export
replaceNames : NameMap Name -> TTImp -> TTImp
replaceNames m (IVar fc nm) = IVar fc $ fromMaybe nm (lookup nm m)
replaceNames m (IPi fc rig pinfo mnm argTy retTy)
  = IPi fc rig pinfo (mnm >>= (`lookup`m)) (replaceNames m argTy) (replaceNames m retTy)
replaceNames m (IApp fc s t) = IApp fc (replaceNames m s) (replaceNames m t)
replaceNames m tt = tt

export
fetchNext : MonadState (Stream a) m => m a
fetchNext = do (x :: xs) <- get
               () <- put xs
               pure x

export
||| Name variables of a type, preferring [a-e] for simple parameters, [f-h] for
||| increasing levels of application, and ix for indices.
nameParams : MonadState VarSrc m => Vect n (Name, TTImp) -> m (NameMap Name)
nameParams cn = do
    let depths = map (mapSnd classifyParam) (toList cn)
        (ixs,rest) = partition ((== Ix) . snd) depths -- partition out ix-params (indices)
        (flat,roughs) = partition ((== Flat) . snd) rest -- partition out simple-params vs applied-params
        flatvars = zip flat (take (length flat) (cycle alpha)) -- assign each flat a simple var name
    r <- foldlM (\m,((n,_),v) => pure $ insert n (srcVarToName !(getNext v)) m) NameMap.empty flatvars
    r <- foldlM (\m,(n,_) => pure $ insert n (srcVarToName !(getNext "ix")) m) r ixs
    r <- foldlM (\m,(n,d) => case d of
      Depth 1 => pure $ NameMap.insert n (srcVarToName !(getNext "f")) m
      Depth 2 => pure $ NameMap.insert n (srcVarToName !(getNext "g")) m
      _       => pure $ NameMap.insert n (srcVarToName !(getNext "h")) m) r roughs
    pure r
  where
    data Tag = Ix | Flat | Depth Nat
    Eq Tag where Ix == Ix = True;Flat == Flat = True;Depth _ == Depth _ = True;_ == _ = False
    alpha : List String
    alpha = ["a","b","c","d","e"]
    classifyParam : TTImp -> Tag
    classifyParam tt = case mapFst (map Arg.type) (unPi tt) of
      (ts@(_ :: _), _) => Depth (length ts) -- takes multiple args
      ([], IType _) => Flat -- singular and Type
      (_ , _) => Ix -- index

