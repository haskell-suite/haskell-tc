module AbsAp1 where

data Maybe a = Just a | Nothing

id x = x

fromJust :: Maybe a -> a
fromJust mb =
  case mb of
    Just a -> id a


