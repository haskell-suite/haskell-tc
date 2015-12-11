module Class1 where

data String
data Bool = True | False

class Show a where
  show :: a -> String


false = show False

show' = show
