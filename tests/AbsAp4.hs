module AbsAp4 where

undefined x = undefined x

fn1 x = fn2 x undefined

fn2 y i = ()
  where
    fn3 a z = fn1 z
