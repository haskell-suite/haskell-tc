{-# LANGUAGE ExplicitForAll #-}
module Class3 where

-- Errors:
--   Could not deduce (Show b) from context.
--     Kept contains a skolem variable
--     Example:
--       fn :: Class a => a -> String
--       err :: a -> String
--       err a = fn a
--   No instance for (Show meta_var_10)
--     Kept contains a meta variable
--     Example:
--       fn :: Class a => a -> String
--       err = fn undefined
--       err x = show (read x) -- with no defaulting
--   context too weak
--     Context is not null.

data String

-- class Show a where
--
-- show :: Show a => a -> String
-- show x = show x

class Super a
class Super a => Sub a
-- class Sub a
instance (Super a, Super b) => Super (a,b)

super :: Super a => a -> String
super x = super x

-- sub :: Sub a => a -> String
-- sub x = super x

-- byInst :: (Super a, Super b) => a -> b -> String
byInst a b = super (a,b)

-- show' :: (Show a, Show b)  => a -> b -> String
-- show' a b = show' a b

-- Could not deduce (Show b) from context.
-- show2 :: Show a => a -> b -> String
-- show2 a b = show2 b a

-- undefined :: a -> b
-- undefined x = undefined x

-- No instance for (Show meta_var_10)
-- err3 :: a -> String
-- err3 x = show' x (undefined x)

-- context too weak
-- bad :: a -> String
-- bad x = show x

-- s2s :: String -> String
-- s2s x = s2s x

-- Signature too general
-- unify 'String' with skolem_a
-- s2any :: String -> a
-- s2any x = s2s x

-- show' x = show x

{-
add assumption: show :: forall a. Show a => a -> String
show' :: _A_
x     :: _B_
_A_ = _B_ -> _C_
instantiate (forall a. Show a => a -> String) => _D_ -> String
add predicate: Show _D_
_B_ = _D_
_C_ = String
_A_ = _D_ -> String
generalize: _A_ => _D_ -> String => forall a. a -> String
Add predicates: forall a. Show a => a -> String
-}
