module Language.Haskell.TypeCheck.Misc where

import           Language.Haskell.TypeCheck.Monad hiding (getMetaTyVars, unify)
import           Language.Haskell.TypeCheck.Types
import           Language.Haskell.TypeCheck.Proof
import           Language.Haskell.Scope
import           Language.Haskell.Exts.SrcLoc

import           Control.Monad.State
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

explicitTcForall :: TcType s -> TI s (TcType s)
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

getZonkedProofs :: TI s (Map SrcSpanInfo Proof)
getZonkedProofs = do
  proofs <- Map.assocs <$> gets tcStateProofs
  Map.fromList . filter (not.isTrivial.snd) <$> forM proofs (\(name, p) -> do
    p' <- simplifyProof <$> zonkProof p
    return (name, p'))


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

getFreeMetaVariables :: TI s [TcMetaVar s]
getFreeMetaVariables = getMetaTyVars =<< getEnvTypes

substituteTyVars :: [(TcVar, TcMetaVar s)] -> TcType s -> TI s (TcType s)
substituteTyVars vars = go
  where
    go (TcForall tvs (TcQual preds ty)) = TcForall tvs . TcQual preds <$> go ty
    go (TcFun a b)          = TcFun <$> go a <*> go b
    go (TcApp a b)          = TcApp <$> go a <*> go b
    go (TcRef var)          =
      case lookup var vars of
        Nothing -> pure $ TcRef var
        Just meta -> pure $ TcMetaVar meta
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

mapTcPredM :: (TcType s -> TI s (TcType s)) -> TcPred s -> TI s (TcPred s)
mapTcPredM fn (TcIsIn className ty) = TcIsIn className <$> fn ty

substituteSkolem :: [(TcVar, TcVar)] -> TcType s -> TI s (TcType s)
substituteSkolem vars = go
  where
    go (TcForall tvs (TcQual preds ty)) = TcForall tvs <$> (TcQual preds <$> go ty)
    go (TcFun a b)          = TcFun <$> go a <*> go b
    go (TcApp a b)          = TcApp <$> go a <*> go b
    go (TcRef var)          =
      case lookup var vars of
        Nothing -> pure $ TcRef var
        Just skolem -> pure $ TcRef skolem
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

substituteMetaVars :: [(TcMetaVar s,TcVar)] -> TcType s -> TI s (TcType s)
substituteMetaVars vars = go
  where
    go (TcForall tvs (TcQual preds ty)) = TcForall tvs <$> (TcQual preds <$> go ty)
    go (TcFun a b)          = TcFun <$> go a <*> go b
    go (TcApp a b)          = TcApp <$> go a <*> go b
    go (TcRef var)          = pure $ TcRef var
    go (TcCon con)          = pure $ TcCon con
    go (TcMetaVar meta) =
      case lookup meta vars of
        Nothing -> pure $ TcMetaVar meta
        Just ref -> pure $ TcRef ref
    go (TcUnboxedTuple tys) = TcUnboxedTuple <$> mapM go tys
    go (TcTuple tys)        = TcTuple <$> mapM go tys
    go (TcList ty)          = TcList <$> go ty
    go TcUndefined          = pure TcUndefined

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
