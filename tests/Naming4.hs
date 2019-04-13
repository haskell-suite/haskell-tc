module Naming4 where

{-
fn var_a = sub var_a
  where
    sub another_a = const var_a another_a
-}
const _ b = b

{-
outer a = a
  where
    inner b = b
-}

outer a = a
  where
    inner b = const (const a ()) b
    id x = x
