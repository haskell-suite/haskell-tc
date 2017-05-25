module Language.Haskell.TypeCheck
  ( module Language.Haskell.TypeCheck.Types
  , TcEnv(..), emptyTcEnv
  , typecheck
  ) where

import Language.Haskell.Scope
import Language.Haskell.TypeCheck.Types
import Language.Haskell.TypeCheck.Monad
import Language.Haskell.TypeCheck.Misc
import Language.Haskell.TypeCheck.SyntaxDirected
-- import Language.Haskell.TypeCheck.Annotate

import Language.Haskell.Exts

import Control.Monad.ST
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map

{-
Scan module, collect type signatures


-}

typecheck :: TcEnv -> Module Origin -> Either TIError (Module Typed, TcEnv)
typecheck env ast = runST (evalStateT (runExceptT (unTI f)) st)
  where
    st = emptyTcState
          { tcStateValues = Map.map toTcType (tcEnvValues env) }
    f = do
      pinned <- pinAST ast
      tiModule pinned
      typed <- unpinAST pinned
      tys <- getZonkedTypes
      return (typed, TcEnv tys)
