{-# LANGUAGE RankNTypes #-}
module Bug3 where

higher :: (forall a. a -> a) -> ()
higher id = id ()

bug :: (a -> a) -> ()
bug id = higher id
