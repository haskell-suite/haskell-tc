module Language.Haskell.TypeCheck where

import Language.Haskell.Scope
import Language.Haskell.TypeCheck.Types
import Language.Haskell.TypeCheck.Monad
import Language.Haskell.TypeCheck.Infer

import Language.Haskell.Exts.Annotated

import Control.Monad.ST
import Control.Monad.State
import qualified Data.Map as Map

{-
Scan module, collect type signatures


-}

typecheck :: TcEnv -> Module Origin -> (Module Typed, TcEnv)
typecheck env ast = runST (evalStateT (unTI f) st)
  where
    st = emptyTcState
          { tcStateValues = Map.map toTcType (tcEnvValues env) }
    f = do
        tiModule ast
        vars <- gets tcStateValues
        vars' <- forM (Map.assocs vars) $ \(src, ty) -> do
            ty' <- zonk ty
            return (src, ty')
        coercions <- gets tcStateCoercions
        coercions' <- forM (Map.assocs coercions) $ \(src, coerce) -> do
            coerce' <- zonkCoercion coerce
            return (src, coerce')
        -- tyApps <- sequence
        --   [
        --   | CoerceAp tys ]
        -- modify $ \st -> st{tcStateValues = Map.fromList vars'
        --                   ,tcStateCoercions = Map.fromList coercions'}
        return $ (undefined, TcEnv Map.empty)
