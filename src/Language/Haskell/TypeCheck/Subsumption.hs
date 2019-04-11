module Language.Haskell.TypeCheck.Subsumption where

import Language.Haskell.TypeCheck.Types
import Language.Haskell.TypeCheck.Monad
import Language.Haskell.TypeCheck.Misc
import Language.Haskell.TypeCheck.Unify
import Language.Haskell.TypeCheck.Proof
import Language.Haskell.TypeCheck.Debug

import Control.Monad
import Data.List
import Data.STRef

import qualified Language.Haskell.TypeCheck.Pretty as P

-- coercion :: sigma -> rho
instantiate :: Sigma s -> TI s (Rho s, TcCoercion s)
instantiate (TcForall [] (TcQual [] ty)) = do
  -- debug $ "Instatiate: Silly forall"
  instantiate ty
instantiate orig@(TcForall tvs (TcQual preds ty)) = do
  tvs' <- map TcMetaVar <$> replicateM (length tvs) newTcVar
  ty' <- substituteTyVars (zip tvs tvs') ty
  preds' <- forM preds $ mapTcPredM (substituteTyVars (zip tvs tvs'))
  -- debug $ "Instantiate: " ++ show (P.pretty orig) ++ " => " ++ show (P.pretty ty')
  addPredicates preds'
  return (ty', \x -> tcProofAp x tvs')
-- instantiate TcForall{} = error "instantiate: Predicate not supported yet."
instantiate tau = return (tau, id)

instantiateMethod :: Sigma s -> TcVar -> Sigma s
instantiateMethod (TcForall tvs (TcQual pred ty)) tv =
  TcForall (delete tv tvs) (TcQual [ elt | elt@(TcIsIn _cls (TcRef pTV)) <- pred, pTV /= tv ] ty)
instantiateMethod sigma tv = sigma

{-
skolemize sigma = /\a.rho + f::/\a.rho -> sigma

Skolemize hoists all forall's to the top-level and returns a coercion function
from the new sigma type to the old sigma type.
-}
-- FIXME: Return the predicates as well?
skolemize :: Sigma s -> TI s ([TcVar], [TcPred s], Rho s, TcCoercion s)
skolemize (TcForall tvs (TcQual preds ty)) = do
  sks <- mapM newSkolemVar tvs
  let skTys = map TcRef sks
  (sks2, preds2, ty', f) <- skolemize =<< substituteTyVars (zip tvs skTys) ty
  preds' <- forM preds $ mapTcPredM (substituteTyVars (zip tvs skTys))
  return (sks ++ sks2, preds' ++ preds2, ty', \x -> tcProofAbs sks $ f (x `tcProofAp` skTys))
skolemize (TcFun arg_ty res_ty) = do
  (sks, preds, res_ty', f) <- skolemize res_ty
  u <- newUnique
  return ( sks, preds, TcFun arg_ty res_ty'
         , \x -> tcProofLam u arg_ty $ f $
                 tcProofAbs sks $ ((x `tcProofAp` map TcRef sks) `TcProofPAp` TcProofVar u))
skolemize ty =
  return ([], [], ty, id)

-- quantify (MetaRef "a" `TcFun` MetaRef "a") = TcForall [a] (a -> a)
quantify :: [TcMetaVar s] -> [TcPred s] -> Rho s -> TI s (Sigma s, [TcVar])
quantify env_tvs predicates rho = do
    -- debug $ "Quantify: " ++ show env_tvs
    -- env_tvs' <- getMetaTyVars $ map TcMetaVar env_tvs
    -- debug $ "        : " ++ show env_tvs'
    rho_tvs <- getMetaTyVars [rho]
    -- debug $ "        : " ++ show rho_tvs
    let meta = rho_tvs \\ env_tvs
        tvs = map toTcVar meta
    -- debug $ "        : " ++ show meta
    -- rho' <- substituteMetaVars (zip meta (map TcRef tvs)) rho
    -- forM_ (zip meta tvs) $ \(var, ty) -> writeMetaVar var (TcRef ty)
    return (TcForall tvs (TcQual predicates rho), tvs)
  where
    -- toTcVar n = TcVar ("t"++show n) []
    toTcVar (TcMetaRef name _) = TcVar name []



-- tcRho :: Term -> Expected s (Rho s) -> TI s ()
-- tcRho = undefined

checkRho :: (ExpectedRho s -> TI s ()) -> Rho s -> TI s ()
checkRho action ty = action (Check ty)

inferRho :: (ExpectedRho s -> TI s ()) -> TI s (Rho s)
inferRho action = do
  ref <- liftST $ newSTRef (error "inferRho: empty result")
  action (Infer ref)
  liftST $ readSTRef ref

-- inferSigma :: Term -> TI s (Sigma s)
-- inferSigma term = do
--   exp_ty <- inferRho term
--   env_tys <- getEnvTypes
--   env_tvs <- getMetaTyVars env_tys
--   res_tvs <- getMetaTyVars [exp_ty]
--   let forall_tvs = res_tvs \\ env_tvs
--   (sigma, rhoToSigma) <- quantify forall_tvs exp_ty
--   return sigma

checkSigma :: (ExpectedRho s -> TI s ()) -> Sigma s -> TI s ()
checkSigma action sigma = do
  -- debug $ "CheckSigma: " ++ show (P.pretty sigma)
  -- (rho, _rhoToSigma) <- instantiate sigma
  (_skol_tvs, _preds, rho, _prenexToSigma) <- skolemize sigma
  checkRho action rho
  -- env_tys <- getEnvTypes
  -- esc_tvs <- getFreeTyVars (sigma : env_tys)
  -- let bad_tvs = filter (`elem` esc_tvs) skol_tvs
  -- unless (null bad_tvs) $ error $ "Type not polymorphic enough: " ++ show (P.pretty bad_tvs)
  -- let coercion = tcProofAbs skol_tvs
  -- setProof pin rhoToSigma rho

-- Rule DEEP-SKOL
-- subsCheck offered_type expected_type
-- coercion :: Sigma1 -> Sigma2
subsCheck :: Sigma s -> Sigma s -> TI s (TcCoercion s)
subsCheck sigma1 sigma2 = do
  -- debug $ "subsCheck: " ++ show (P.pretty sigma1) ++ " >> " ++ show (P.pretty sigma2)
  (skol_tvs, _preds, rho2, forallrho2ToSigma2) <- skolemize sigma2
  sigma1ToRho2 <- subsCheckRho sigma1 rho2
  esc_tvs <- getFreeTyVars [sigma1, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skol_tvs
  unless (null bad_tvs) $ error $ "Subsumption check failed: " ++ show bad_tvs
  -- /\a.rho = sigma2
  -- \sigma1 -> forallrho2ToSigma2 (/\a. sigma1ToRho2 sigma1)
  -- return (CoerceCompose (CoerceAbs skol_tvs) sigma2ToRho2)
  return $ \x -> forallrho2ToSigma2 (tcProofAbs skol_tvs (sigma1ToRho2 x))

-- instSigma ((forall a. a -> a) -> Int) ((forall a b. a -> b) -> Int)
--     = CoerceFun Id (subsCheck (forall a b. a -> b) (forall a. a -> a))
-- subsCheck (forall a b. a -> b) (forall a. a -> a)
--     = Compose (Abs [a]) (subsCheckRho (forall a b. a -> b) (a -> a))
--     = Compose (Abs [a]) (Compose Id (Ap [a,b]))

-- (forall ab. a -> b)          (a -> a) = Compose  (subsCheckRho (a -> b) (a -> a)) (Ap [a,b])
-- subsCheckRho (a -> b) (a -> a) = CoerceFun (subCheckRho b a) (subsCheck a a) = CoerceFun Id Id
-- subsCheckRho tau tau = Id
subsCheckRho :: Sigma s -> Rho s -> TI s (TcCoercion s)
subsCheckRho sigma1@TcForall{} rho2 = do
  (rho1, sigma1ToRho1) <- instantiate sigma1
  rho1ToRho2 <- subsCheckRhoRho rho1 rho2
  let sigma1ToRho2 = rho1ToRho2 . sigma1ToRho1
  return sigma1ToRho2
subsCheckRho t1 t2 = subsCheckRhoRho t1 t2

-- coercion :: rho1 -> rho2
subsCheckRhoRho :: Rho s -> Rho s -> TI s (TcCoercion s)
subsCheckRhoRho (TcFun a1 r1) t2 = do
  (a2, r2) <- unifyFun t2
  subsCheckFun a1 r1 a2 r2
subsCheckRhoRho t1 (TcFun a2 r2) = do
  (a1, r1) <- unifyFun t1
  subsCheckFun a1 r1 a2 r2
subsCheckRhoRho t1 t2 = do
  unify t1 t2
  return id

-- subsCheckFun (a1 -> r1) (a2 -> r2)
-- coercion :: (a1 -> r1) -> (a2 -> r2)
subsCheckFun :: Sigma s -> Rho s -> Sigma s -> Rho s -> TI s (TcCoercion s)
subsCheckFun a1 r1 a2 r2 = do
  co_arg <- subsCheck a2 a1
  -- co_arg :: a2 -> a1
  co_res <- subsCheckRho r1 r2
  -- co_res :: r1 -> r2
  u <- newUnique
  return $ \x -> tcProofLam u a2 (co_res (x `TcProofPAp` co_arg (TcProofVar u)))



-- We have type 'Sigma' and we want type 'Rho'. The coercion is a function of
-- type Sigma->Rho
instSigma :: Sigma s -> Expected s (Rho s) -> TI s (TcCoercion s)
instSigma ty (Infer r) = do
  (ty', coerce) <- instantiate ty
  liftST $ writeSTRef r ty'
  return coerce
instSigma ty (Check rho) = subsCheckRho ty rho
