module Language.Haskell.TypeCheck.Unify where

import Language.Haskell.TypeCheck.Types
import Language.Haskell.TypeCheck.Monad
import Language.Haskell.TypeCheck.Misc

import Control.Monad
import Control.Monad.Except
import Data.STRef

import qualified Language.Haskell.TypeCheck.Pretty as P

unifyExpected :: Tau s -> ExpectedRho s -> TI s ()
unifyExpected tau exp_ty =
  case exp_ty of
    Check rho -> unify tau rho
    Infer ref -> liftST $ writeSTRef ref tau

unify :: Tau s -> Tau s -> TI s ()
-- unify a b | trace ("Unify: " ++ show (P.pretty a) ++ " = " ++ show (P.pretty b)) False = undefined
unify (TcList a) (TcList b) =
    unify a b
unify (TcTuple as) (TcTuple bs) | length as == length bs =
    zipWithM_ unify as bs
unify (TcApp la lb) (TcApp ra rb) = do
    unify la ra
    unify lb rb
unify (TcFun la lb) (TcFun ra rb) = do
    unify la ra
    unify lb rb
unify (TcCon left) (TcCon right)
  | left == right = return ()
  | otherwise     = throwError $ UnificationError $ "unify con: " ++ show (left,right)
unify (TcUnboxedTuple as) (TcUnboxedTuple bs)
    | length as == length bs = zipWithM_ unify as bs
unify (TcMetaVar ref) a = unifyMetaVar ref a
unify a (TcMetaVar ref) = unifyMetaVar ref a
unify (TcRef a) (TcRef b) | a == b = return ()
unify (TcRef a) b       = throwError $ UnificationError $ "Unexpected ref: " ++ show (P.pretty a)
unify a b               = throwError $ UnificationError $ show (P.pretty a) ++ " <=> " ++ show (P.pretty b)

unifyMetaVar :: TcMetaVar s -> TcType s -> TI s ()
unifyMetaVar a (TcMetaVar b) | a == b = return ()
unifyMetaVar a@(TcMetaRef _ident ref) rightTy = do
    mbSubst <- liftST $ readSTRef ref
    case mbSubst of
        Just leftTy -> unify leftTy rightTy
        Nothing -> unifyUnboundVar a rightTy

unifyUnboundVar :: TcMetaVar s -> TcType s -> TI s ()
unifyUnboundVar tv bTy@(TcMetaVar b@(TcMetaRef _ refB)) = do
    mbSubst <- liftST $ readSTRef refB
    case mbSubst of
        Just ty -> unify (TcMetaVar tv) ty
        Nothing -> writeMetaVar tv (TcMetaVar b)
unifyUnboundVar tv b = do
    tvs <- getMetaTyVars [b]
    if tv `elem` tvs
        then throwError $ UnificationError "occurs check failed"
        else writeMetaVar tv b

unifyFun :: Rho s -> TI s (Sigma s, Rho s)
unifyFun (TcFun a b) = return (a,b)
unifyFun ty = do
  a <- TcMetaVar <$> newTcVar
  b <- TcMetaVar <$> newTcVar
  unify ty (TcFun a b)
  return (a, b)

unifyFun2 :: Rho s -> TI s (Sigma s, Sigma s, Rho s)
unifyFun2 rho = do
  (a_ty, tmp) <- unifyFun rho
  (b_ty, ret) <- unifyFun tmp
  return (a_ty, b_ty, ret)

unifyFuns :: Int -> Rho s -> TI s ([Sigma s], Rho s)
unifyFuns = worker []
  where
    worker acc 0 ty = return (reverse acc, ty)
    worker acc n (TcFun a b) = worker (a : acc) (n-1) b
    worker acc n ty = do
      args <- replicateM n $ TcMetaVar <$> newTcVar
      ret <- TcMetaVar <$> newTcVar
      unify ty (foldr TcFun ret args)
      return (reverse acc ++ args, ret)

unifyApp :: Rho s -> TI s (Sigma s, Sigma s)
unifyApp (TcApp a b) = pure (a,b)
unifyApp ty = do
  a <- TcMetaVar <$> newTcVar
  b <- TcMetaVar <$> newTcVar
  unify ty (TcApp a b)
  return (a, b)

unifyUnboxedTuple :: Int -> Rho s -> TI s [Sigma s]
unifyUnboxedTuple n (TcUnboxedTuple tys) | length tys == n = return tys
unifyUnboxedTuple n ty = do
  tys <- replicateM n $ TcMetaVar <$> newTcVar
  unify ty (TcUnboxedTuple tys)
  return tys

unifyTuple :: Int -> Rho s -> TI s [Sigma s]
unifyTuple n (TcTuple tys) | length tys == n = return tys
unifyTuple n ty = do
  tys <- replicateM n $ TcMetaVar <$> newTcVar
  unify ty (TcTuple tys)
  return tys

unifyList :: Rho s -> TI s (Sigma s)
unifyList (TcList elt) = return elt
unifyList ty = do
  elt <- TcMetaVar <$> newTcVar
  unify ty (TcList elt)
  return elt






-- matchTypes (TcIsIn "Ord" value) (TcIsIn "Ord" a)         = Just [(a, value)]
-- matchTypes (TcIsIn "Ord" value) (TcIsIn "blah" a)        = Nothing
-- matchTypes (TcIsIn "Ord" value) (TcIsIn "Ord" (a,b))     = Nothing
-- matchTypes (TcIsIn "Ord" (Int, t1)) (TcIsIn "Ord" (a,b)) = Just [(a, Int), (b, t1)]
-- matchTypes (TcIsIn "Ord" ref) (TcIsIn "Ord" a)         = Just [(a, ref)]
matchTypes :: TcType s -> TcType s -> TI s (Maybe [(TcVar, TcType s)])
matchTypes t1 t2 = flip catchError (const $ return Nothing) $ do
    tvs <- getFreeTyVars [t2]
    tvs' <- replicateM (length tvs) newTcVar
    t2' <- substituteTyVars (zip tvs $ map TcMetaVar tvs') t2

    mtvs <- getMetaTyVars [t1]
    mtvs' <- replicateM (length mtvs) $ do
      u <- newUnique
      return $ TcVar ("tmp_" ++ show u) ["internal"]
    t1' <- substituteMetaVars (zip mtvs $ map TcRef mtvs') t1
    -- debug $ show $ P.pretty t1'
    -- debug $ show $ P.pretty t2'
    unify t1' t2'
    -- debug $ "Unification OK"
    tys <- forM tvs' $ \(TcMetaRef _ ref) -> do
      mbTy <- liftST (readSTRef ref)
      case mbTy of
        Nothing -> throwError MatchError
        Just (TcRef tv)
          | Just meta <- lookup tv (zip mtvs' mtvs)
          -> return $ TcMetaVar meta
        Just ty -> return ty
    return $ Just (zip tvs tys)

-- bySuper (TcIsIn "Ord" tcref) = [TcIsIn "Ord" tcref, TcIsIn "Eq" tcref]
bySuper :: TcPred s -> TI s [TcPred s]
bySuper p@(TcIsIn className ty) = do
  -- Constraints are the superclasses to our class.
  (constraints, classTy) <- lookupClass className
  -- Hmm, 'classTy' should always just be a TcRef so matching shouldn't be
  -- able to fail.
  mbSubst <- matchTypes ty classTy
  case mbSubst of
    Nothing -> return [p]
    Just subst -> do
      ps <- mapM (substituteTyVarsPred subst) constraints
      return (p:ps)

-- byInst (TcIsIn "Ord" (a, b)) = Just [TcIsIn "Ord" a, TcIsIn "Ord" b]
-- byInst (TcIsIn "Ord" (a -> b)) = Nothing
byInst :: TcPred s -> TI s (Maybe [TcPred s])
byInst (TcIsIn className ty) = do
    insts <- lookupInstances className
    go insts
  where
    go [] = return Nothing
    go ((constraints, instTy):rest) = do
      -- debug $ "Ty:   " ++ show (P.pretty ty)
      -- debug $ "Inst: " ++ show (P.pretty instTy)
      mbSubst <- matchTypes ty instTy
      case mbSubst of
        Nothing -> go rest
        Just subst ->
          Just <$> mapM (substituteTyVarsPred subst) constraints

-- True iff p is given by ps.
-- Superclasses:
--   class Eq a => Ord a
-- Instances:
--   instance Show a => Show [a]
--
-- entail [TcIsIn "Ord" a] (TcIsIn "Eq" a) = True
-- entail [] (TcIsIn "Ord" (Int, Char)) = True
-- entail [TcIsIn "Ord" a] (TcIsIn "Eq" (Int, a)) = True
--   byInst: [TcIsIn "Eq" Int, TcIsIn "Eq" a]
-- entail [TcIsIn "MArray" a e m] (TcIsIn "Monad" m)
--   bySuper: TcIsIn "MArray" a e m => [TcIsIn "Monad" m]
entail :: [TcPred s] -> TcPred s -> TI s Bool
entail ps p = do
  superSet <- mapM bySuper ps
  if any (p `elem`) superSet
    then return True
    else do
      mbInst <- byInst p
      case mbInst of
        Nothing -> return False
        Just constraints -> and <$> mapM (entail ps) constraints

inHnf :: TcPred s -> Bool
inHnf (TcIsIn c t) = hnf t
  where
    hnf TcRef{} = True
    hnf (TcApp t _) = hnf t
    hnf TcMetaVar{} = True
    hnf _ = False

-- toHnf (TcIsIn "Eq" (a,b)) = [TcIsIn "Eq" a, TcIsIn "Eq" b]
toHnf :: TcPred s -> TI s [TcPred s]
toHnf p
  | inHnf p = return [p]
  | otherwise = do
      mbInst <- byInst p
      case mbInst of
        Nothing -> throwError $ GeneralError $ "context reduction: " ++ show (P.pretty p)
        Just ps -> concat <$> mapM toHnf ps

simplify :: [TcPred s] -> TI s [TcPred s]
simplify = loop []
  where
    loop rs []     = pure rs
    loop rs (p:ps) = do
      doesEntail  <- entail (rs++ps) p
      if doesEntail
        then loop rs ps
        else loop (p:rs) ps

reduce :: [TcPred s] -> TI s [TcPred s]
reduce ps = simplify =<< concat <$> mapM toHnf ps
