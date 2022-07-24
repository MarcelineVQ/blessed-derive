module Language.Reflection.Derive.Derive

import public Language.Reflection.Derive

{-
Ideally I want to just use `derive` from elab-utils so that people can use one
invocation for any need but it's a little greedy in how it does things.
Generation of an InterfaceImpl happens all at once even though declaration of
types and implementations are done separately. What this means is that I can't
check for previous implementations existing as when doing something like
%runElab derive "Foo" [Functor,Foldable,Traversable]
where creating the Traversable happens in one step when generating the InterfaceImpl
but at that time we've not yet declared the Functor or Foldable Claims and so
it's impossible to check for their existence when generating Traversable.

One potential solution is to have the `type` and `impl` fields of InterfaceImpl be
`Elab TTImp` instead of plain TTImp. And have the existence check moved to `impl`.
In this way the claims can be all done before checking for their existence.
-}

||| Declares each instance all at once, to allow for checking of dependent instances.
||| Sets Hint True to clash with user defined instances, so they're aware that
||| multiples exist.
export
deriveBlessed : Name -> List (DeriveUtil -> Elab InterfaceImpl) -> Elab ()
deriveBlessed name fs = do p <- getParamInfo' name
                           let g = genericUtil p
                           for_ fs $ \f => do
                             (MkInterfaceImpl iname vis opts impl type) <- f g
                             let function = implName g iname
                             declare [interfaceHintOpts vis (opts ++ [Hint True]) function type
                                     , def function [var function .= impl]]
