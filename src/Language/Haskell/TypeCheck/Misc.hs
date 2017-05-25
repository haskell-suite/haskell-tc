module Language.Haskell.TypeCheck.Misc where

import           Language.Haskell.TypeCheck.Monad hiding (getMetaTyVars, unify)
import           Language.Haskell.TypeCheck.Types
import           Language.Haskell.TypeCheck.Proof
import           Language.Haskell.Scope
import           Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.TypeCheck.Pretty as Doc

import Data.Either
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.STRef

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

predFreeTyVars :: [TcPred s] -> TI s [TcVar]
predFreeTyVars preds = getFreeTyVars [ ty | TcIsIn _class ty <- preds ]

explicitTcForall :: TcType s -> TI s (TcType s)
explicitTcForall src@(TcForall tvs qual) = do
  tvs' <- getFreeTyVars [src]
  return $ TcForall (tvs++tvs') qual
explicitTcForall ty = do
  tvs <- getFreeTyVars [ty]
  return $ TcForall tvs (TcQual [] ty)


getEnvTypes :: TI s [Sigma s]
getEnvTypes = do
  m <- gets tcStateValues
  return (Map.elems m)

getZonkedTypes :: TI s (Map GlobalName Type)
getZonkedTypes = do
  tys <- Map.assocs <$> gets tcStateValues
  Map.fromList <$> forM tys (\(name, ty) -> do
    ty' <- zonkType ty
    return (name, ty'))

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

predMetaTyVars :: [TcPred s] -> TI s [TcMetaVar s]
predMetaTyVars preds = getMetaTyVars [ ty | TcIsIn _class ty <- preds ]


getFreeMetaVariables :: TI s [TcMetaVar s]
getFreeMetaVariables = getMetaTyVars =<< getEnvTypes

lowerMetaVars :: TcType s -> TI s (TcType s)
lowerMetaVars = substituteTyVars []

lowerPredMetaVars :: TcPred s -> TI s (TcPred s)
lowerPredMetaVars (TcIsIn className ty) =
  TcIsIn className <$> substituteTyVars [] ty

substituteTyVars :: [(TcVar, TcType s)] -> TcType s -> TI s (TcType s)
substituteTyVars vars = go
  where
    go (TcForall tvs (TcQual preds ty)) = TcForall tvs . TcQual preds <$> go ty
    go (TcFun a b)          = TcFun <$> go a <*> go b
    go (TcApp a b)          = TcApp <$> go a <*> go b
    go (TcRef var)          =
      case lookup var vars of
        Nothing -> pure $ TcRef var
        Just ty -> pure ty
    go (TcCon con)          = pure $ TcCon con
    go (TcMetaVar meta@(TcMetaRef _name var)) = do
      mbVal <- liftST $ readSTRef var
      case mbVal of
        Nothing -> pure $ TcMetaVar meta
        Just val -> go val
    go (TcUnboxedTuple tys) = TcUnboxedTuple <$> mapM go tys
    go (TcTuple tys)        = TcTuple <$> mapM go tys
    go (TcList ty)          = TcList <$> go ty
    go TcUndefined          = pure TcUndefined

substituteTyVarsPred :: [(TcVar, TcType s)] -> TcPred s -> TI s (TcPred s)
substituteTyVarsPred var (TcIsIn cls ty) =
  TcIsIn cls <$> substituteTyVars var ty

mapTcPredM :: (TcType s -> TI s (TcType s)) -> TcPred s -> TI s (TcPred s)
mapTcPredM fn (TcIsIn className ty) = TcIsIn className <$> fn ty

substituteMetaVars :: [(TcMetaVar s,TcType s)] -> TcType s -> TI s (TcType s)
substituteMetaVars vars = go
  where
    go (TcForall tvs (TcQual preds ty)) = TcForall tvs <$> (TcQual preds <$> go ty)
    go (TcFun a b)          = TcFun <$> go a <*> go b
    go (TcApp a b)          = TcApp <$> go a <*> go b
    go (TcRef var)          = pure $ TcRef var
    go (TcCon con)          = pure $ TcCon con
    go (TcMetaVar meta@(TcMetaRef _name var)) = do
      mbVal <- liftST $ readSTRef var
      case mbVal of
        Just val -> go val
        Nothing ->
          case lookup meta vars of
            Nothing -> pure $ TcMetaVar meta
            Just ty -> pure ty
    go (TcUnboxedTuple tys) = TcUnboxedTuple <$> mapM go tys
    go (TcTuple tys)        = TcTuple <$> mapM go tys
    go (TcList ty)          = TcList <$> go ty
    go TcUndefined          = pure TcUndefined

substituteMetaVarsPred :: [(TcMetaVar s, TcType s)] -> TcPred s -> TI s (TcPred s)
substituteMetaVarsPred var (TcIsIn cls ty) =
  TcIsIn cls <$> substituteMetaVars var ty


writeMetaVar :: TcMetaVar s -> TcType s -> TI s ()
writeMetaVar (TcMetaRef _name var) ty = liftST $ do
  mbVal <- readSTRef var
  case mbVal of
    Nothing -> writeSTRef var (Just ty)
    Just{}  -> error "writeMetaVar: Variable already set."

expectAny :: ExpectedRho s -> TI s (Rho s)
expectAny (Check rho) = return rho
expectAny (Infer ref) = do
  ty <- TcMetaVar <$> newTcVar
  liftST $ writeSTRef ref ty
  return ty

expectList :: ExpectedRho s -> TI s (Rho s)
expectList (Check rho) = return rho
expectList (Infer ref) = do
  ty <- TcList . TcMetaVar <$> newTcVar
  liftST $ writeSTRef ref ty
  return ty

newSkolemVar :: TcVar -> TI s TcVar
newSkolemVar (TcVar name src) = do
  u <- newUnique
  return $ TcVar ("sk_" ++ show u ++ "_"++name) src

-- split
--   1. simplify contexts
--   2. find predicates to defer
--   3. resolve ambiguity using defaulting
-- Input: skolemized tvs and predicates
-- Output: predicates to be deferred, predicates with defaulting
simplifyAndDeferPredicates outer_meta preds = do
  preds' <- forM preds $ \predicate -> do
    pred_meta <- predMetaTyVars [predicate]
    -- debug $ "Pred_meta: " ++ show (Doc.pretty pred_meta)
    if not (null pred_meta) && all (`elem` outer_meta) pred_meta
      then return $ Left predicate
      else return $ Right predicate
  let (ds, rs) = partitionEithers preds'
  -- debug $ "Defer: " ++ show (Doc.pretty ds)
  setPredicates ds
  return rs
