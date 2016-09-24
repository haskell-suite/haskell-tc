{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Language.Haskell.TypeCheck.Monad where

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.ST
import           Data.STRef
import           Data.List
import           Data.Map                               (Map)
import qualified Data.Map                               as Map
import           Data.Set                               (Set)
import qualified Data.Set                               as Set
import           Language.Haskell.Exts.Syntax (Boxed (..), Name,
                                                         QName (..),
                                                         SpecialCon (..),
                                                         Type (..), ann)
import           Language.Haskell.Exts.SrcLoc

import           Language.Haskell.Scope
import           Language.Haskell.TypeCheck.Types hiding (Type(..), Typed(..))
import qualified Language.Haskell.TypeCheck.Types as T

import qualified Language.Haskell.TypeCheck.Pretty as P
import Debug.Trace

data TcEnv = TcEnv
  { tcEnvValues :: Map GlobalName T.Type
  }

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv { tcEnvValues = Map.empty }

data TcState s = TcState
    { -- Values such as 'length', 'Nothing', 'Just', etc
      tcStateValues    :: Map GlobalName (TcType s)
    , tcStateUnique    :: Int
    , tcStateProofs    :: Map SrcSpanInfo (TcProof s)
    , tcStateRecursive :: Set GlobalName
    -- ^ Set of recursive bindings in the current group.
    , tcStateKnots     :: [(GlobalName, SrcSpanInfo)]
    -- ^ Locations where bindings from the current group are used. This is used to set
    --   proper coercions after generalization.
    }
newtype TI s a = TI { unTI :: StateT (TcState s) (ST s) a }
    deriving ( Monad, Functor, Applicative, MonadState (TcState s) )

liftST :: ST s a -> TI s a
liftST action = TI $ StateT $ \env -> do
  a <- action
  return (a,env)

debug :: String -> TI s ()
debug str = trace str (return ())

--type Infer a = a Origin -> TI (a Typed)

emptyTcState :: TcState s
emptyTcState = TcState
    { tcStateValues   = Map.empty
    , tcStateUnique    = 0
    , tcStateProofs = Map.empty
    , tcStateRecursive = Set.empty
    , tcStateKnots = [] }

-- runTI :: forall a. TcEnv -> (forall s. TI s a) -> TcEnv
-- runTI env action = runST (toEnv =<< execStateT (unTI f) st)
--   where
--     toEnv st = return (TcEnv Map.empty)
--     st = emptyTcState
--           { tcStateValues = Map.map toTcType (tcEnvValues env) }
--     f = do
--         action
--         vars <- gets tcStateValues
--         vars' <- forM (Map.assocs vars) $ \(src, ty) -> do
--             ty' <- zonk ty
--             return (src, ty')
--         coercions <- gets tcStateCoercions
--         coercions' <- forM (Map.assocs coercions) $ \(src, coerce) -> do
--             coerce' <- zonkCoercion coerce
--             return (src, coerce')
--         -- modify $ \st -> st{tcStateValues = Map.fromList vars'
--         --                   ,tcStateCoercions = Map.fromList coercions'}
--         return ()

withRecursive :: [GlobalName] -> TI s a -> TI s a
withRecursive rec action = do
    modify $ \st -> st{tcStateRecursive = Set.fromList rec}
    a <- action
    modify $ \st -> st{tcStateRecursive = Set.empty, tcStateKnots = []}
    return a

isRecursive :: GlobalName -> TI s Bool
isRecursive gname = gets $ Set.member gname . tcStateRecursive

setKnot :: GlobalName -> SrcSpanInfo -> TI s ()
setKnot gname src =
    modify $ \st -> st{tcStateKnots = (gname,src) : tcStateKnots st}

getKnots :: TI s [(GlobalName, SrcSpanInfo)]
getKnots = gets tcStateKnots

newUnique :: TI s Int
newUnique = do
    u <- gets tcStateUnique
    modify $ \env -> env{ tcStateUnique = u + 1 }
    return u

-- getFreeMetaVariables :: TI s [TcMetaVar s]
-- getFreeMetaVariables = do
--     m <- gets tcStateValues
--     nub . concat <$> mapM metaVariables (Map.elems m)

setAssumption :: GlobalName -> TcType s -> TI s ()
setAssumption ident tySig = -- trace (show (P.pretty ident) ++ " :: " ++ show (P.pretty tySig)) $
  modify $ \env ->
    env{ tcStateValues = Map.insert ident tySig (tcStateValues env) }

findAssumption :: GlobalName -> TI s (Sigma s)
findAssumption ident = do
    m <- gets tcStateValues
    case Map.lookup ident m of
        Nothing -> error $ "Language.Haskell.TypeCheck.findAssumption: Missing ident: " ++ show ident
        Just scheme -> return scheme

setProof :: SrcSpanInfo -> TcCoercion s -> TcType s -> TI s ()
setProof span coercion src = modify $ \env ->
    env{ tcStateProofs = Map.insert span proof (tcStateProofs env) }
  where
    proof = coercion (TcProofSrc src)

-- getCoercion :: SrcSpanInfo -> TI s (TcCoercion s)
-- getCoercion src = gets $ Map.findWithDefault id src . tcStateCoercions

-- setGlobal :: QualifiedName -> TcType -> TI ()
-- setGlobal gname scheme = modify $ \env ->
--     env{ tcEnvGlobals = Map.insert gname scheme (tcEnvGlobals env) }

-- findGlobal :: QualifiedName -> TI TcType
-- findGlobal gname = do
--     m <- gets tcEnvGlobals
--     case Map.lookup gname m of
--         Nothing -> error $ "Missing global: " ++ show gname
--         Just scheme -> return scheme

-- freshInst :: TcType s -> TI s (TcQual s (TcType s), Coercion s)
-- freshInst (TcForall tyvars (TcQual preds t0)) = do
--     refs <- replicateM (length tyvars) newTcVar
--     let subst = zip tyvars refs
--         instPred (TcIsIn className ty) =
--             TcIsIn className (instantiate ty)
--         instantiate ty =
--             case ty of
--                 TcForall{} -> error "freshInst"
--                 TcFun a b -> TcFun (instantiate a) (instantiate b)
--                 TcApp a b -> TcApp (instantiate a) (instantiate b)
--                 TcRef v ->
--                     case lookup v subst of
--                         Nothing -> TcRef v
--                         Just ref -> TcMetaVar ref
--                 TcCon{} -> ty
--                 TcMetaVar{} -> ty -- FIXME: Is this an error?
--                 TcUnboxedTuple tys -> TcUnboxedTuple (map instantiate tys)
--                 TcTuple tys -> TcTuple (map instantiate tys)
--                 TcList elt -> TcList (instantiate elt)
--     return (map instPred preds `TcQual` instantiate t0, CoerceAp $ map TcMetaVar refs)
-- freshInst ty = pure (TcQual [] ty, CoerceId )


-- getMetaTyVars :: TcType s -> TI s [TcMetaVar s]
-- getMetaTyVars = metaVariables


zonkType :: TcType s -> TI s T.Type
zonkType ty =
  case ty of
    TcForall tyvars (TcQual predicates tty) ->
      T.TyForall tyvars <$> ((:=>) <$> mapM zonkPredicate predicates <*> zonkType tty)
    TcFun a b -> T.TyFun <$> zonkType a <*> zonkType b
    TcApp a b -> T.TyApp <$> zonkType a <*> zonkType b
    TcRef var -> pure $ T.TyRef var
    TcCon con -> pure $ T.TyCon con
    TcMetaVar (TcMetaRef name meta) -> do
        mbTy <- liftST (readSTRef meta)
        case mbTy of
            Nothing -> error $ "Zonking unset meta variable: " ++ name
            Just sub -> zonkType sub
    TcUnboxedTuple tys -> T.TyUnboxedTuple <$> mapM zonkType tys
    TcTuple tys -> T.TyTuple <$> mapM zonkType tys
    TcList elt -> T.TyList <$> zonkType elt

zonkPredicate :: TcPred s -> TI s Predicate
zonkPredicate (TcIsIn className ty) = IsIn className <$> zonkType ty

zonkProof :: TcProof s -> TI s Proof
zonkProof proof =
  case proof of
    TcProofAbs tvs p  -> ProofAbs tvs <$> zonkProof p
    TcProofAp p tys   -> ProofAp <$> zonkProof p <*> mapM zonkType tys
    TcProofLam n ty p -> ProofLam n <$> zonkType ty <*> zonkProof p
    TcProofSrc ty     -> ProofSrc <$> zonkType ty
    TcProofPAp p1 p2  -> ProofPAp <$> zonkProof p1 <*> zonkProof p2
    TcProofVar n      -> pure $ ProofVar n

tcVarFromName :: Name Origin -> TcVar
tcVarFromName name =
    TcVar (getNameIdentifier name) src
  where
    Origin (Resolved (GlobalName src _qname)) _ = ann name

newTcVar :: TI s (TcMetaVar s)
newTcVar = do
    u <- newUnique
    ref <- liftST $ newSTRef Nothing
    return $ TcMetaRef ("v"++show u) ref

typeToTcType :: Type Origin -> TcType s
typeToTcType ty =
    case ty of
        TyFun _ a b -> TcFun (typeToTcType a) (typeToTcType b)
        TyVar _ name -> TcRef (tcVarFromName name)
        TyCon _ (Special _ UnitCon{}) ->
            TcTuple []
        TyCon _ conName ->
            let Origin (Resolved (GlobalName _ qname)) _ = ann conName
            in TcCon qname
        TyApp _ a b -> TcApp (typeToTcType a) (typeToTcType b)
        TyParen _ t -> typeToTcType t
        TyTuple _ Unboxed tys -> TcUnboxedTuple (map typeToTcType tys)
        TyTuple _ Boxed tys -> TcTuple (map typeToTcType tys)
        TyList _ elt -> TcList (typeToTcType elt)
        _ -> error $ "typeToTcType: " ++ show ty

--tcTypeToScheme :: TcType -> TcType
--tcTypeToScheme ty = Scheme (freeTcVariables ty) ([] :=> ty)

-- freeTcVariables :: TcType s -> [TcVar]
-- freeTcVariables = nub . worker []
--   where
--     worker ignore ty =
--         case ty of
--             TcForall{} -> error "freeTcVariables"
--             TcFun a b -> worker ignore a ++ worker ignore b
--             TcApp a b -> worker ignore a ++ worker ignore b
--             TcRef v | v `elem` ignore -> []
--                     | otherwise       -> [v]
--             TcCon{} -> []
--             TcUnboxedTuple tys -> concatMap (worker ignore) tys
--             TcMetaVar{} -> []
--             TcTuple tys -> concatMap (worker ignore) tys
--             TcList elt -> worker ignore elt

-- metaVariables :: TcType s -> TI s [TcMetaVar s]
-- metaVariables ty =
--     case ty of
--         -- XXX: There shouldn't be any meta variables inside a forall scope.
--         TcForall _ (TcQual _ ty') -> metaVariables ty'
--         TcFun a b -> (++) <$> metaVariables a <*> metaVariables b
--         TcApp a b -> (++) <$> metaVariables a <*> metaVariables b
--         TcRef{} -> pure []
--         TcCon{} -> pure []
--         TcMetaVar var@(TcMetaRef _ ref) -> do
--           mbTy <- liftST $ readSTRef ref
--           case mbTy of
--             Just ty' -> metaVariables ty'
--             Nothing  -> return [var]
--         TcUnboxedTuple tys -> concat <$> mapM metaVariables tys
--         TcTuple tys -> concat <$> mapM metaVariables tys
--         TcList elt -> metaVariables elt

-- Replace free meta vars with tcvars. Compute the smallest context.
--
-- generalize :: [TcMetaVar s] -> TcType s -> TI s (TcType s, Coercion s)
-- generalize free ty = do
--     meta <- metaVariables ty
--     let unbound = nub meta \\ free
--     forM_ unbound $ \var@(TcMetaRef _name ref) ->
--         liftST $ writeSTRef ref (Just (TcRef (toTcVar var)))
--     -- ty' <- zonk ty
--     let tcVars = map toTcVar unbound
--     return ( TcForall tcVars (TcQual [] ty), CoerceAbs tcVars)
--   where
--     toTcVar (TcMetaRef name _) = TcVar name noSrcSpanInfo

noSrcSpanInfo :: SrcSpanInfo
noSrcSpanInfo = infoSpan (mkSrcSpan noLoc noLoc) []

mkBuiltIn :: String -> String -> QualifiedName
mkBuiltIn m ident = QualifiedName m ident
