{-# LANGUAGE RankNTypes #-}

f :: (forall a. a -> a) -> ()
f = f

k :: forall a b c. a -> b -> c
k = k

-- test1 = f (\a -> a)
-- test2 = f k
test3 n = f (k n)
