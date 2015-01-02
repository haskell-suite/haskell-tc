module Append where

data List a = Nil | Cons a (List a)

append a b =
  case a of
    Nil       -> b
    Cons x xs -> Cons x (append xs b)
