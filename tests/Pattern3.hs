module Pattern2 where

data List a = Nil | Cons a (List a)

drop1 ( x `Cons` xs) = xs
