data List a = Nil | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f lst =
  case lst of
    Nil -> Nil
    Cons x xs -> Cons (f x) (map f xs)
