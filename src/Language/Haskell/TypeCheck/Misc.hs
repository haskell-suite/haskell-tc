{-# LANGUAGE ParallelListComp #-}
module Language.Haskell.TypeCheck.Misc where

import           Language.Haskell.Scope
import           Language.Haskell.TypeCheck.Monad
-- import qualified Language.Haskell.TypeCheck.Pretty as Doc
import           Language.Haskell.TypeCheck.Types

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Either
import           Data.List
import           Data.Map                          (Map)
import qualified Data.Map                          as Map
import           Data.Maybe
import           Data.Set                          (Set)
import qualified Data.Set                          as Set
import           Data.STRef

-- property:    \ty -> getFreeTyVars ty == []
-- property:    \tv -> do (tvs, rho, coercion) <- skolemize ty
--                        all (`elem` tvs) <$> getFreeTyVars rho
getFreeTyVars :: [TcType s] -> TI s [TcVar]
getFreeTyVars tys = goMany [] tys []
  where
    goMany _bound [] acc     = pure acc
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
        TcMetaVar (TcMetaRef _ ref) -> do
          mbTy <- liftST $ readSTRef ref
          case mbTy of
            Just ty' -> go bound ty' acc
            Nothing  -> pure acc
        TcTuple tys -> goMany bound tys acc
        TcList elt -> go bound elt acc
        TcStar -> pure acc

getAllTyVars :: [TcType s] -> TI s [TcVar]
getAllTyVars tys = reverse <$> goMany tys []
  where
    goMany [] acc     = pure acc
    goMany (x:xs) acc = go x acc >>= goMany xs
    go ty acc =
      case ty of
        TcForall _tvs (TcQual _ ty') -> go ty' acc
        TcFun a b -> go b =<< go a acc
        TcApp a b -> go a =<< go b acc
        TcRef v | v `elem` acc   -> pure acc
                | otherwise      -> pure (v:acc)
        TcCon{} -> pure acc
        TcUnboxedTuple tys -> goMany tys acc
        TcMetaVar (TcMetaRef _ ref) -> do
          mbTy <- liftST $ readSTRef ref
          case mbTy of
            Just ty' -> go ty' acc
            Nothing  -> pure acc
        TcTuple tys -> goMany tys acc
        TcList elt -> go elt acc
        TcStar -> pure acc

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

getZonkedTypes :: TI s (Map Entity Type)
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
    goMany [] acc     = pure acc
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
        TcStar -> pure acc

getProofMetaTyVars :: TcProof s -> TI s [TcMetaVar s]
getProofMetaTyVars p =
  case p of
    TcProofAbs _ p' -> getProofMetaTyVars p'
    TcProofAp p' ts -> liftM2 (++) (getMetaTyVars ts) (getProofMetaTyVars p')
    TcProofLam _ t p' -> liftM2 (++) (getMetaTyVars [t]) (getProofMetaTyVars p')
    TcProofSrc t -> getMetaTyVars [t]
    TcProofPAp pl pr -> liftM2 (++) (getProofMetaTyVars pl) (getProofMetaTyVars pr)
    TcProofVar{} -> pure []

getProofTyVars :: TcProof s -> TI s (Set String)
getProofTyVars p =
  case p of
    TcProofAbs tvs p' -> flip Set.difference (toSet tvs) <$> getProofTyVars p'
    TcProofAp p' ts -> liftM2 (Set.union) (fromTy ts) (getProofTyVars p')
    TcProofLam _ t p' -> liftM2 (Set.union) (fromTy [t]) (getProofTyVars p')
    TcProofSrc t -> fromTy [t]
    TcProofPAp pl pr -> liftM2 (Set.union) (getProofTyVars pl) (getProofTyVars pr)
    TcProofVar{} -> pure Set.empty
  where
    toSet tvs = Set.fromList $
      [ name | TcVar name _ <- tvs ] ++ [ name | TcSkolemVar name <- tvs ]
    fromTy tys = do
      lst <- getFreeTyVars tys
      return $ toSet lst

getProofUniques :: TcProof s -> TI s [Int]
getProofUniques p =
  case p of
    TcProofAbs _ p' -> getProofUniques p'
    TcProofAp p' ts -> liftM2 (++) (fromTy ts) (getProofUniques p')
    TcProofLam _ t p' -> liftM2 (++) (fromTy [t]) (getProofUniques p')
    TcProofSrc t -> fromTy [t]
    TcProofPAp pl pr -> liftM2 (++) (getProofUniques pl) (getProofUniques pr)
    TcProofVar{} -> pure []
  where
    fromTy tys = do
      lst <- getAllTyVars tys
      return $ [ u | TcUniqueVar u <- lst ]

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
        Nothing  -> pure $ TcMetaVar meta
        Just val -> go val
    go (TcUnboxedTuple tys) = TcUnboxedTuple <$> mapM go tys
    go (TcTuple tys)        = TcTuple <$> mapM go tys
    go (TcList ty)          = TcList <$> go ty
    go TcStar               = pure TcStar

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
    go TcStar               = pure TcStar

substituteMetaVarsPred :: [(TcMetaVar s, TcType s)] -> TcPred s -> TI s (TcPred s)
substituteMetaVarsPred var (TcIsIn cls ty) =
  TcIsIn cls <$> substituteMetaVars var ty


writeMetaVar :: TcMetaVar s -> TcType s -> TI s ()
writeMetaVar (TcMetaRef _name var) ty = do
  -- debug $ "write " ++ show name ++ " = " ++ show (Doc.pretty ty)
  liftST $ do
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
newSkolemVar (TcVar name _loc) = do
  skolems <- gets tcStateSkolems
  let newName = head $ filter (`Set.notMember` skolems) (name : [ name ++ show n | n <- [2..] ])
  modify $ \st -> st{tcStateSkolems = Set.insert newName skolems}
  return $ TcSkolemVar newName
newSkolemVar _ = error "expected simple tcvar"
  -- u <- newUnique
  -- return $ TcVar ("sk_" ++ show u ++ "_"++name) src

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

renameTyVars :: [(TcVar, TcVar)] -> TcType s -> TI s (TcType s)
renameTyVars vars = go
  where
    rename tv = fromMaybe tv (lookup tv vars)
    renamePred (TcIsIn e t) = TcIsIn e <$> go t
    go (TcForall tvs (TcQual preds ty)) =
      TcForall (map rename tvs) <$>
        (TcQual <$> mapM renamePred preds <*> go ty)
    go (TcFun a b)          = TcFun <$> go a <*> go b
    go (TcApp a b)          = TcApp <$> go a <*> go b
    go (TcRef var)          = pure $ TcRef $ rename var
    go (TcCon con)          = pure $ TcCon con
    go (TcMetaVar meta@(TcMetaRef _name var)) = do
      mbVal <- liftST $ readSTRef var
      case mbVal of
        Nothing  -> pure $ TcMetaVar meta
        Just val -> go val
    go (TcUnboxedTuple tys) = TcUnboxedTuple <$> mapM go tys
    go (TcTuple tys)        = TcTuple <$> mapM go tys
    go (TcList ty)          = TcList <$> go ty
    go TcStar               = pure TcStar

renameTyVarsProof :: [(TcVar, TcVar)] -> TcProof s -> TI s (TcProof s)
renameTyVarsProof vars = go
  where
    rename tv = fromMaybe tv (lookup tv vars)
    go (TcProofAbs tvs p) = TcProofAbs (map rename tvs) <$> go p
    go (TcProofAp p tys) = TcProofAp <$> go p <*> mapM (renameTyVars vars) tys
    go (TcProofLam n t p) = TcProofLam n <$> renameTyVars vars t <*> go p
    go (TcProofSrc t) = TcProofSrc <$> renameTyVars vars t
    go (TcProofPAp pl pr) = TcProofPAp <$> go pl <*> go pr
    go (TcProofVar n) = pure $ TcProofVar n

{-
input:
  Proof: ∀ 1 3. 0<1<1> →  2<3<3>> →  3<3>>
  Proof: 2<3<3>>
  Proof: 2<3<3>>

output (skolems=[]):
  Proof: ∀ a b. a →  b →  b
  Proof: b
  Proof: b

output (skolems=[a]):
  Proof: ∀ b c. b →  c →  c
  Proof: c
  Proof: c
-}
renameProofs :: TI s ()
renameProofs = do
  skolems <- gets tcStateSkolems --    :: !(Set String)
  proofRefs <- gets tcStateProofGroup -- :: ![STRef s (Maybe (TcProof s))]

  all_meta <- getFreeMetaVariables
  unless (null all_meta) $ error "renameProofs: Unexpected meta variables"

  proofs <- liftST $ map fromJust <$> mapM readSTRef proofRefs

  -- forM_ proofs $ \proof ->
  --   debug $ "  Proof: " ++ show (Doc.pretty proof)

  usedTypes <- Set.unions <$> mapM getProofTyVars proofs

  let reserved = skolems `Set.union` usedTypes
      a_to_z = [ [c] | c <- ['a' .. 'z']]
      all_names = concat $ a_to_z : [ map (++show n) a_to_z | n <- [2..] ]

      usableNames = filter (`Set.notMember` reserved) all_names

  uniques <- nub . concat <$> mapM getProofUniques proofs
  -- debug $ "Uniques: " ++ show uniques
  -- debug $ "Reserved: " ++ show reserved
  let replace = [ (TcUniqueVar u, TcSkolemVar name) | u <- uniques | name <- usableNames ]

  forM_ proofRefs $ \ref -> do
    Just proof <- liftST $ readSTRef ref
    proof' <- renameTyVarsProof replace proof
    liftST $ writeSTRef ref (Just proof')

  -- FIXME: This is an inefficient hack. We want to replace numbered tcvars with named
  --        tcvars but not all values may have numbered tcvars in their signature.
  values <- gets (Map.toList . tcStateValues)
  forM_ values $ \(key, ty) -> do
    ty' <- renameTyVars replace ty
    setAssumption key ty'

  modify $ \st -> st{tcStateProofGroup = []}
  return ()
