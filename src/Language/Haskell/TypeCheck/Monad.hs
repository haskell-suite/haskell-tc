{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
module Language.Haskell.TypeCheck.Monad where

import           Control.Monad.Except
import           Control.Monad.Fail
import           Control.Monad.ST
import           Control.Monad.ST.Unsafe
import           Control.Monad.State
import           Data.Map                          (Map)
import qualified Data.Map                          as Map
import           Data.Maybe
import           Data.Set                          (Set)
import qualified Data.Set                          as Set
import           Data.STRef
import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Syntax      (Asst (..), Boxed (..),
                                                    Context (..), Module,
                                                    Name (..), QName (..),
                                                    SpecialCon (..),
                                                    TyVarBind (..), Type (..),
                                                    ann)

import           Language.Haskell.Scope            as Scope
import qualified Language.Haskell.TypeCheck.Pretty as Doc
import           Language.Haskell.TypeCheck.Proof
import           Language.Haskell.TypeCheck.Types  hiding (Type (..),TyVar(..))
import qualified Language.Haskell.TypeCheck.Types  as T

{-
TcQual [] (TcIsIn Show a)
class Show a

TcQual [TcIsIn "Eq" a] (TcIsIn Ord a)
class Eq a => Ord a

TcQual [TcIsIn "Monad" m] (TcIsIn MArray a e m)]
class Monad m => MArray a e m

TcQual [TcIsIn "Ord" a, TcIsIn "Ord" b] (TcIsIn Ord (a,b))
instance (Ord a, Ord b) => Ord (a, b)

TcQual [] (TcIsIn Ord Char)
instance Ord Char

classes :: TcQual s (TcPred s)
instances :: TcQual s (TcPred s)

API:
bySuper :: TcPred s -> [TcPred s]
bySuper (TcIsIn "Ord" value) = [TcIsIn "Eq" value]
bySuper (TcIsIn "MArray" a e m) = [TcIsIn "Monad" m]

byInst :: TcPred s -> [TcPred s]
byInst (TcIsIn "Ord" (fst, snd)) = [TcIsIn "Ord" fst, TcIsIn "Ord" snd]

instance Class [Char]
TcIsIn Class [a]

matchInstance :: TcPred s -> TcPred s -> TI s (Maybe [(TyVar, TcType s)])

preds :=> head
subst <- match p head
subst :: [(TyVar, TcType s)]
map (applySubst subst) preds


-}

data TcEnv = TcEnv
  { tcEnvValues :: Map Entity T.Type
  }

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv { tcEnvValues = Map.empty }

data TIError
  = UnificationError String
  | ContextTooWeak
  | MatchError
  | GeneralError String
    deriving (Show)

data TcState s = TcState
    { -- Values such as 'length', 'Nothing', 'Just', etc
      tcStateValues     :: !(Map Entity (TcType s))
    , tcStateClasses    :: !([TcQual s (TcPred s)])
    , tcStateInstances  :: !([TcQual s (TcPred s)])
    , tcStateUnique     :: !(Int)
    , tcStateSkolems    :: !(Set String)
    , tcStateProofGroup :: ![STRef s (Maybe (TcProof s))]
    , tcStateRecursive  :: !(Set Entity)
    -- ^ Set of recursive bindings in the current group.
    , tcStateKnots      :: [(Entity, Pin s)]
    -- ^ Locations where bindings from the current group are used. This is used to set
    --   proper coercions after generalization.

    -- FIXME: We want to use a Writer for the predicates.
    , tcStatePredicates :: [TcPred s]
    }
newtype TI s a = TI { unTI :: ExceptT TIError (StateT (TcState s) (ST s)) a }
    deriving ( Monad, MonadFail, Functor, Applicative, MonadState (TcState s)
             , MonadError TIError )

liftST :: ST s a -> TI s a
liftST action = TI $ ExceptT $ StateT $ \env -> do
  a <- action
  return (Right a,env)

instance MonadIO (TI s) where
  liftIO io = liftST (unsafeIOToST io)

tiMaybe :: b -> (a -> TI s b) -> Maybe a -> TI s b
tiMaybe def _ Nothing = pure def
tiMaybe _ fn (Just a) = fn a

debug :: String -> TI s ()
debug str = liftIO (putStrLn str)

debugPP :: Doc.Pretty a => String -> a -> TI s ()
debugPP tag value = debug $ tag ++ ": " ++ show (Doc.pretty value)


--type Infer a = a Origin -> TI (a Typed)

emptyTcState :: TcState s
emptyTcState = TcState
    { tcStateValues    = Map.empty
    , tcStateClasses   = []
    , tcStateInstances = []
    , tcStateUnique    = 0
    , tcStateSkolems   = Set.empty
    , tcStateProofGroup = []
    , tcStateRecursive = Set.empty
    , tcStateKnots = []
    , tcStatePredicates = []
    }

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

withRecursive :: [Entity] -> TI s a -> TI s a
withRecursive rec action = do
    original <- get
    modify $ \st -> st{tcStateRecursive = tcStateRecursive st `Set.union` Set.fromList rec}
    a <- action
    modify $ \st -> st{tcStateRecursive = tcStateRecursive original}
    return a

isRecursive :: Entity -> TI s Bool
isRecursive gname = gets $ Set.member gname . tcStateRecursive

setKnot :: Entity -> Pin s -> TI s ()
setKnot gname pin =
    modify $ \st -> st{tcStateKnots = (gname,pin) : tcStateKnots st}

getKnots :: TI s [(Entity, Pin s)]
getKnots = gets tcStateKnots

addPredicates :: [TcPred s] -> TI s ()
addPredicates predicates =
  modify $ \st -> st{tcStatePredicates = predicates ++ tcStatePredicates st}

getPredicates :: TI s [TcPred s]
getPredicates = gets tcStatePredicates

setPredicates :: [TcPred s] -> TI s ()
setPredicates predicates =
  modify $ \st -> st{tcStatePredicates = predicates}

dropSkolem :: TcVar -> TI s ()
dropSkolem (TcVar name _) =
  modify $ \st -> st{tcStateSkolems = Set.delete name (tcStateSkolems st) }
dropSkolem (TcSkolemVar name) =
  modify $ \st -> st{tcStateSkolems = Set.delete name (tcStateSkolems st) }
dropSkolem TcUniqueVar{} = return ()

newUnique :: TI s Int
newUnique = do
    u <- gets tcStateUnique
    modify $ \env -> env{ tcStateUnique = u + 1 }
    return u

-- getFreeMetaVariables :: TI s [TcMetaVar s]
-- getFreeMetaVariables = do
--     m <- gets tcStateValues
--     nub . concat <$> mapM metaVariables (Map.elems m)

setAssumption :: Entity -> TcType s -> TI s ()
setAssumption ident tySig = do
  -- debug $ "SetAssumption: " ++ show (Doc.pretty ident) ++ " :: " ++ show (Doc.pretty tySig)
  modify $ \env ->
    env{ tcStateValues = Map.insert ident tySig (tcStateValues env) }

findAssumption :: Entity -> TI s (Sigma s)
findAssumption ident = do
    m <- gets tcStateValues
    case Map.lookup ident m of
        Nothing -> error $ "Language.Haskell.TypeCheck.findAssumption: Missing ident: " ++ show ident
        Just scheme -> return scheme

setProof :: Pin s -> TcCoercion s -> TcType s -> TI s ()
setProof (Pin _ ref) coercion src = do
  mbProof <- liftST $ readSTRef ref
  case mbProof of
    Nothing -> do
      -- debug $ "SetProof: " ++ show (Doc.pretty $ coercion $ TcProofSrc src)
      liftST $ writeSTRef ref (Just $ coercion $ TcProofSrc src)
      modify $ \st -> st{tcStateProofGroup = ref : tcStateProofGroup st}
    Just{} -> error "Proof already set"

getProof :: Pin s -> TI s (TcProof s)
getProof (Pin _ ref) = liftST $ do
  Just proof <- readSTRef ref
  return proof

pinAST :: Module Origin -> TI s (Module (Pin s))
pinAST = liftST . traverse newPin
  where
    newPin origin = do
      ref <- newSTRef Nothing
      return $ Pin origin ref

unpinAST :: Module (Pin s) -> TI s (Module Typed)
unpinAST = traverse unpin
  where
    unpin (Pin (Origin nameinfo srcspan) ref) = do
      mbProof <- liftST $ readSTRef ref
      case mbProof of
        Nothing -> return $ Scoped nameinfo srcspan
        Just proof -> do
          -- debug (show nameinfo)
          zonked <- simplifyProof.simplifyProof <$> zonkProof proof
          pure $ Coerced nameinfo srcspan zonked
          -- if isTrivial zonked && not (isBinding nameinfo)
          --   then pure $ Scoped nameinfo srcspan
          --   else pure $ Coerced nameinfo srcspan zonked

isBinding :: Scope.NameInfo -> Bool
isBinding Scope.Binding{} = True
isBinding _               = False

expectResolvedPin :: Pin s -> TI s Entity
expectResolvedPin (Pin (Origin (Resolved gname) _) _) = pure gname
expectResolvedPin (Pin (Origin (Binding gname) _) _)  = pure gname
expectResolvedPin _ = throwError $ GeneralError "expected resolved"

qnameToEntity :: QName (Pin s) -> TI s Entity
qnameToEntity qname =
  case qname of
    Qual _src _mod name      -> expectResolvedPin (ann name)
    UnQual _src name         -> expectResolvedPin (ann name)
    Special _src _specialCon -> error "qnameToEntity: Special?"

addClass :: TcQual s (TcPred s) -> TI s ()
addClass classDef =
  modify $ \st -> st{ tcStateClasses = classDef : tcStateClasses st }

addInstance :: TcQual s (TcPred s) -> TI s ()
addInstance instDef =
  modify $ \st -> st{ tcStateInstances = instDef : tcStateInstances st }

-- ass "Ord" = ([TcIsIn "Eq" a], TcRef a)
-- lookupClass "Monad" = ([TcIsIn "Applicative" m], TcRef m)
-- lookupClass "Show" = ([], TcRef a)
lookupClass :: Entity -> TI s ([TcPred s], TcType s)
lookupClass className = do
  clss <- gets tcStateClasses
  case [ (constraints, ty)
       | TcQual constraints (TcIsIn thisClassName ty) <- clss
       , thisClassName == className ] of
    [ ret ] -> return ret
    _       -> error $ "Class not found: " ++ show className

-- lookupInstances "Ord" = [ ([], Int)
--                         , ([TcIsIn "Ord" a], Maybe a)
--                         , ([TcIsIn "Ord" a, TcIsIn "Ord" b], (a, b)) ]
lookupInstances :: Entity -> TI s [([TcPred s], TcType s)]
lookupInstances className = do
  insts <- gets tcStateInstances
  return [ (constraints, ty)
         | TcQual constraints (TcIsIn thisClassName ty) <- insts
         , thisClassName == className ]

zonkTcVar :: TcVar -> T.TyVar
zonkTcVar (TcVar name _loc) = T.TyVar name
zonkTcVar (TcSkolemVar name) = T.TyVar name
zonkTcVar (TcUniqueVar n) = T.TyVar (show n)

zonkType :: TcType s -> TI s T.Type
zonkType ty = do
  -- debug $ "Zonk: " ++ show (Doc.pretty ty)
  case ty of
    TcForall tyvars (TcQual predicates tty) ->
      T.TyForall (map zonkTcVar tyvars) <$>
        ((:=>) <$> mapM zonkPredicate predicates <*> zonkType tty)
    TcFun a b -> T.TyFun <$> zonkType a <*> zonkType b
    TcApp a b -> T.TyApp <$> zonkType a <*> zonkType b
    TcRef var -> pure $ T.TyRef $ zonkTcVar var
    TcCon con -> pure $ T.TyCon con
    TcMetaVar (TcMetaRef name meta) -> do
        mbTy <- liftST (readSTRef meta)
        case mbTy of
            Nothing  -> error $ "Zonking unset meta variable: " ++ show name
            Just sub -> zonkType sub
    TcUnboxedTuple tys -> T.TyUnboxedTuple <$> mapM zonkType tys
    TcTuple tys -> T.TyTuple <$> mapM zonkType tys
    TcList elt -> T.TyList <$> zonkType elt
    TcStar -> pure T.TyStar

zonkPredicate :: TcPred s -> TI s Predicate
zonkPredicate (TcIsIn className ty) = IsIn className <$> zonkType ty

zonkProof :: TcProof s -> TI s Proof
zonkProof proof =
  case proof of
    TcProofAbs tvs p  -> ProofAbs (map zonkTcVar tvs) <$> zonkProof p
    TcProofAp p tys   -> ProofAp <$> zonkProof p <*> mapM zonkType tys
    TcProofLam n ty p -> ProofLam n <$> zonkType ty <*> zonkProof p
    TcProofSrc ty     -> ProofSrc <$> zonkType ty
    TcProofPAp p1 p2  -> ProofPAp <$> zonkProof p1 <*> zonkProof p2
    TcProofVar n      -> pure $ ProofVar n

tcVarFromName :: Name (Pin s) -> TcVar
tcVarFromName name =
    TcVar ident src
  where
    src = case ann name of
            Pin (Origin (Resolved entity) _) _ -> entityLocation entity
            Pin (Origin (Binding entity) _) _  -> entityLocation entity
            _ -> []
    ident =
      case name of
        Symbol _ symbol -> symbol
        Ident _ ident   -> ident

newTcVar :: TI s (TcMetaVar s)
newTcVar = do
    u <- newUnique
    ref <- liftST $ newSTRef Nothing
    return $ TcMetaRef u ref

typeToTcType :: Type (Pin s) -> TI s (TcType s)
typeToTcType ty =
    case ty of
      TyForall _ mbTybinds mbContext ty' ->
        TcForall
          [ case bind of
              KindedVar _ name _kind -> tcVarFromName name
              UnkindedVar _ name     -> tcVarFromName name | bind <- fromMaybe [] mbTybinds ]
          <$> (TcQual <$> tiMaybe [] contextToPredicates mbContext <*> typeToTcType ty')
      TyFun _ a b -> TcFun <$> typeToTcType a <*> typeToTcType b
      TyVar _ name -> pure $ TcRef (tcVarFromName name)
      TyCon _ (Special _ UnitCon{}) ->
          pure $ TcTuple []
      TyCon _ qname -> do
        entity <- qnameToEntity qname
        pure $ TcCon $ entityName entity
      TyApp _ a b -> TcApp <$> typeToTcType a <*> typeToTcType b
      TyParen _ t -> typeToTcType t
      TyTuple _ Unboxed tys -> TcUnboxedTuple <$> mapM typeToTcType tys
      TyTuple _ Boxed tys -> TcTuple <$> mapM typeToTcType tys
      TyList _ elt -> TcList <$> typeToTcType elt
      _ -> error $ "typeToTcType: " ++ show ty

contextToPredicates :: Context (Pin s) -> TI s [TcPred s]
contextToPredicates ctx =
  case ctx of
    CxEmpty{}             -> pure []
    CxSingle _origin asst -> pure <$> assertionToPredicate asst
    CxTuple _origin assts -> mapM assertionToPredicate assts

assertionToPredicate :: Asst (Pin s) -> TI s (TcPred s)
assertionToPredicate asst =
  case asst of
    ParenA _ sub -> assertionToPredicate sub
    ClassA _ qname [ty] ->
      TcIsIn <$> qnameToEntity qname <*> typeToTcType ty
    ClassA _ _qname [] -> error "assertionToPredicate: MultiParamTypeClasses not supported"
    _ -> error "assertionToPredicate: unsupported assertion"

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

-- mkBuiltIn moduleName identifier
mkBuiltIn :: String -> String -> QualifiedName
mkBuiltIn = QualifiedName
