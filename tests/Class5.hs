module Class5 where

data Bool = True | False

class Default a where
  def :: a

instance Default Bool where
  def = True

data Maybe a = Nothing | Just a
instance Default b => Default (Maybe b) where
  def = Just def
