module Class1 where

data String

class Show a where
  show :: a -> String

class Monad m where
  return :: a -> m a

list x = return [x]
