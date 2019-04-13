module Naming1 where

fn :: a -> a
fn var_a = sub var_a
  where
    sub :: a -> a
    sub another_a = const var_a another_a

const :: a -> b -> b
const _ b = b
