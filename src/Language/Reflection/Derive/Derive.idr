module Language.Reflection.Derive.Derive

import public Language.Reflection.Derive

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
