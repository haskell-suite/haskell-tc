module Class6 where

class Plus a where
  plus :: a -> a -> a

data Maybe a = Nothing | Just a

instance Plus (Maybe a) where
  plus = \a b -> Nothing
