module Language.Haskell.TypeCheck.Debug where

import Language.Haskell.TypeCheck.Types
import Language.Haskell.TypeCheck.Monad
import           Language.Haskell.Scope

import Data.List
import           Data.STRef

type Verbose = Bool

class DebugShow a where
  dshow :: Verbose -> a -> String

instance DebugShow GlobalName where
  dshow verbose (GlobalName _loc qname) = dshow verbose qname

instance DebugShow QualifiedName where
  dshow _ (QualifiedName _ ident) = ident

instance DebugShow a => DebugShow [a] where
  dshow verbose lst = "[" ++ intercalate ", " (map (dshow verbose) lst) ++ "]"

-- instance DebugShow (TcType s) where
--   dshow verbose ty = show (runresolveMetaVars ty)

resolveMetaVars :: TcType s -> TI s (TcType s)
resolveMetaVars ty =
  case ty of
    TcForall tyvars (TcQual predicates tty) ->
      TcForall tyvars <$> (TcQual <$> mapM resolvePredicate predicates <*> resolveMetaVars tty)
    TcFun a b -> TcFun <$> resolveMetaVars a <*> resolveMetaVars b
    TcApp a b -> TcApp <$> resolveMetaVars a <*> resolveMetaVars b
    TcRef var -> pure $ TcRef var
    TcCon con -> pure $ TcCon con
    TcMetaVar (TcMetaRef name meta) -> do
        mbTy <- liftST (readSTRef meta)
        case mbTy of
            Nothing -> pure $ TcMetaVar (TcMetaRef name meta)
            Just sub -> resolveMetaVars sub
    TcUnboxedTuple tys -> TcUnboxedTuple <$> mapM resolveMetaVars tys
    TcTuple tys -> TcTuple <$> mapM resolveMetaVars tys
    TcList elt -> TcList <$> resolveMetaVars elt

resolvePredicate :: TcPred s -> TI s (TcPred s)
resolvePredicate (TcIsIn className ty) = TcIsIn className <$> resolveMetaVars ty
