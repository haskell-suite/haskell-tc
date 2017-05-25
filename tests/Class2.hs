module Class2 where

data String
data Bool = True | False

class Show a where
  show :: a -> String

instance Show Bool

false x = show False

falseFn x = show (x False)

show' x = show x
