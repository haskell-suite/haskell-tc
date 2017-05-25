module Class4 where

data String

class Show a where
  show :: a -> String

fn1 x y = (fn2 x, y)
  where
    fn2 x = show x
