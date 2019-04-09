module Pattern2 where

data Maybe a = Nothing | Just a

fromMaybe def Nothing  = def
fromMaybe def (Just a) = a
