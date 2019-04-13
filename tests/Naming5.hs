module Naming5 where

outer b = b
  where
    inner :: a -> a
    inner a = const b a

const _ b = b
