module Language.Haskell.TypeCheck.Unify where

import Language.Haskell.TypeCheck.Types
import Language.Haskell.TypeCheck.Monad
import Language.Haskell.TypeCheck.Misc

import Control.Monad
import Data.STRef

import qualified Language.Haskell.TypeCheck.Pretty as P
import Debug.Trace

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
  | otherwise     = error $ "unify con: " ++ show (left,right)
unify (TcUnboxedTuple as) (TcUnboxedTuple bs)
    | length as == length bs = zipWithM_ unify as bs
unify (TcMetaVar ref) a = unifyMetaVar ref a
unify a (TcMetaVar ref) = unifyMetaVar ref a
unify (TcRef a) (TcRef b) | a == b = return ()
unify a b               = error $ "unify: " ++ show (P.pretty a) ++ " <=> " ++ show (P.pretty b)

unifyMetaVar :: TcMetaVar s -> TcType s -> TI s ()
unifyMetaVar a (TcMetaVar b) | a == b = return ()
unifyMetaVar a@(TcMetaRef _ident ref) rightTy = do
    mbSubst <- liftST $ readSTRef ref
    case mbSubst of
        Just leftTy -> unify leftTy rightTy
        Nothing -> unifyUnboundVar a rightTy

unifyUnboundVar :: TcMetaVar s -> TcType s -> TI s ()
unifyUnboundVar tv@(TcMetaRef _ident ref) bTy@(TcMetaVar b@(TcMetaRef _ refB)) = do
    mbSubst <- liftST $ readSTRef refB
    case mbSubst of
        Just ty -> unify (TcMetaVar tv) ty
        Nothing -> trace (show (P.pretty tv) ++ " = " ++ show (P.pretty bTy)) $
          liftST $ writeSTRef ref (Just $ TcMetaVar b)
unifyUnboundVar tv@(TcMetaRef _ident ref) b = do
    tvs <- getMetaTyVars [b]
    if tv `elem` tvs
        then error "occurs check failed"
        else trace (show (P.pretty tv) ++ " = " ++ show (P.pretty b)) $
          liftST $ writeSTRef ref (Just b)

unifyFun :: Rho s -> TI s (Sigma s, Rho s)
unifyFun (TcFun a b) = return (a,b)
unifyFun ty = do
  a <- TcMetaVar <$> newTcVar
  b <- TcMetaVar <$> newTcVar
  unify ty (TcFun a b)
  return (a, b)

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
