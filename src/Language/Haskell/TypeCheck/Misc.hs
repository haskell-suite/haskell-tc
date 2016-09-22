module Language.Haskell.TypeCheck.Misc where

import Language.Haskell.TypeCheck.Types
import Language.Haskell.TypeCheck.Monad hiding (unify,getMetaTyVars)

import Data.STRef

-- property:    \ty -> getFreeTyVars ty == []
-- property:    \tv -> do (tvs, rho, coercion) <- skolemize ty
--                        all (`elem` tvs) <$> getFreeTyVars rho
getFreeTyVars :: [TcType s] -> TI s [TcVar]
getFreeTyVars tys = goMany [] tys []
  where
    goMany bound [] acc = pure acc
    goMany bound (x:xs) acc = go bound x acc >>= goMany bound xs
    go bound ty acc =
      case ty of
        TcForall tvs (TcQual _ ty') -> go (tvs ++ bound) ty' acc
        TcFun a b -> go bound a =<< go bound b acc
        TcApp a b -> go bound a =<< go bound b acc
        TcRef v | v `elem` bound -> pure acc
                | v `elem` acc   -> pure acc
                | otherwise      -> pure (v:acc)
        TcCon{} -> pure acc
        TcUnboxedTuple tys -> goMany bound tys acc
        TcMetaVar var@(TcMetaRef _ ref) -> do
          mbTy <- liftST $ readSTRef ref
          case mbTy of
            Just ty' -> go bound ty' acc
            Nothing  -> pure acc
        TcTuple tys -> goMany bound tys acc
        TcList elt -> go bound elt acc

getEnvTypes :: TI s [Sigma s]
getEnvTypes = undefined

-- property: \ty -> do (tvs, rho, _) <- skolemize ty
--                     (ty', proof) <- instantiate (TcForall tvs (TcQual [] rho))
--                     meta <- getMetaTyVars [ty']
--                     length meta <= length tvs
getMetaTyVars :: [TcType s] -> TI s [TcMetaVar s]
getMetaTyVars tys = goMany tys []
  where
    goMany [] acc = pure acc
    goMany (x:xs) acc = go x acc >>= goMany xs
    go ty acc =
      case ty of
        TcForall _tvs (TcQual _ ty') -> go ty' acc
        TcFun a b -> go a =<< go b acc
        TcApp a b -> go a =<< go b acc
        TcRef {} -> pure acc
        TcCon{} -> pure acc
        TcUnboxedTuple tys -> goMany tys acc
        TcMetaVar var@(TcMetaRef _ ref) -> do
          mbTy <- liftST $ readSTRef ref
          case mbTy of
            Just ty' -> go ty' acc
            Nothing
              | var `elem` acc -> pure acc
              | otherwise      -> pure (var:acc)
        TcTuple tys -> goMany tys acc
        TcList elt -> go elt acc
