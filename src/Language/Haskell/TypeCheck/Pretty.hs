module Language.Haskell.TypeCheck.Pretty where

import Text.PrettyPrint.ANSI.Leijen (Doc, parens, list)

class Pretty a where
  prettyPrec :: Int -> a -> Doc
  prettyPrec _ = pretty
  pretty :: a -> Doc
  pretty = prettyPrec 0
  {-# MINIMAL prettyPrec | pretty #-}

instance Pretty a => Pretty [a] where
  prettyPrec _ = list . map pretty

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id
