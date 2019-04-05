module Append where

data List a = Nil | Cons a (List a)

append :: List x -> List x -> List x
append a b =
  case a of
    Nil       -> b
    Cons x xs -> Cons x (append xs b)
