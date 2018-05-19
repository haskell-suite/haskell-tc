module InlinePragma where

{-# NOINLINE x #-}
x () = ()

{-# INLINE y #-}
y () = ()
