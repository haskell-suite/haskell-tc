{-# LANGUAGE RankNTypes #-}
module Naming3 where

fn :: forall b. b -> (forall a. a -> a)
fn b a = a
