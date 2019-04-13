[![Build Status](https://travis-ci.org/haskell-suite/haskell-tc.svg?branch=master)](https://travis-ci.org/haskell-suite/haskell-tc)

haskell-tc
==========

This package contains an implementation of a bidirectional typechecker for Haskell.

TC Overview
===========

I'm no expert on type theory. This is how thing make sense in my head; take it with a grain of salt.

Basic HM
--------

Simple yet powerful type-inference by unification.

Bidirectional
-------------

Extention to HM. Works on higher rank types. Eg:

    fn :: (forall a. [a] -> [a]) -> ([Int],[Char])
    fn g = (g [1,2,3], g ['a','b','c'])

It's bidirectional because it can either do type-checking (down) or type-inference (up). This means it can verify the correctness of user-written higher ranked types even though it wouldn't be able to infer those types.

Boxy types
----------
Extension to bidirectional TC. Instead of having to distinct modes (up and down), this system can work with partial type signatures, checking what is known and inferring the rest. This granularity is required when using higher ranked types together with polymorphic data types. Eg:

    fn :: Maybe (forall a. [a] -> [a]) -> ([Int],[Char])
    fn Nothing = ([],[])
    fn (Just g) = (g [1,2,3], g ['a','b','c'])

The same goes for using higher ranked types together with polymorphic functions. In the following example, '$' has a polymorphic type and 'runST' has a rank-2 type.

    fn = runST $ do ...

This is called impredicativity. Both HM and Bidirectional are predicative. Boxy types are implemented by jhc.

OutsideIn
---------

The latest and greatest. Breaks the pattern of the previous extensions by strictly speaking not being backwards compatible with HM. Used by GHC.
