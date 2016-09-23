module Language.Haskell.TypeCheck.Annotate ( AnnEnv(..), runReader, annotate ) where

import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Syntax hiding (Type(..))
import qualified Language.Haskell.Exts.Syntax as HS

import           Language.Haskell.Scope (Origin(..), GlobalName)
import qualified Language.Haskell.Scope as Scope
import           Language.Haskell.TypeCheck.Monad
import           Language.Haskell.TypeCheck.Types
import qualified Language.Haskell.TypeCheck.Types as TC

import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import Control.Monad.Reader

data AnnEnv = AnnEnv
  { annTypes :: Map GlobalName Type
  , annProofs :: Map SrcSpanInfo Proof }

type AnnM a = Reader AnnEnv a
type Ann a = a Origin -> AnnM (a Typed)
type AnnT t a = t (a Origin) -> AnnM (t (a Typed))

annotate :: Ann Module
annotate m =
  case m of
    Module origin mhead pragma imports decls ->
      Module <$> toTyped origin
        <*> annMaybe annModuleHead mhead
        <*> mapM annPragma pragma
        <*> mapM annImportDecl imports
        <*> mapM annDecl decls
    _ -> error "tiModule"

annDummy :: Functor a => Ann a
annDummy = pure . fmap dummy
  where
    dummy (Origin nameInfo srcspan) =
      case nameInfo of
        Scope.Resolved gname -> Resolved gname srcspan
        Scope.None           -> None srcspan
        Scope.ScopeError err -> ScopeError err srcspan

binding :: Origin -> AnnM Typed
binding (Origin nameInfo srcspan) =
  case nameInfo of
    Scope.Resolved gname -> do
      Just ty <- lookupType gname
      Just proof <- lookupProof srcspan
      pure $ Binding gname ty proof srcspan
    Scope.None           -> error "binding: None"
    Scope.ScopeError err -> error "binding: ScopeError"

toTyped :: Origin -> AnnM Typed
toTyped (Origin nameInfo srcspan) =
  case nameInfo of
    Scope.Resolved gname -> pure $ Resolved gname srcspan
    Scope.None           -> pure $ None srcspan
    Scope.ScopeError err -> pure $ ScopeError err srcspan

annMaybe :: Ann a -> AnnT Maybe a
annMaybe _ Nothing   = pure Nothing
annMaybe fn (Just a) = Just <$> fn a

annModuleHead :: Ann ModuleHead
annModuleHead mhead =
  case mhead of
    ModuleHead origin name mbWarn mbExports ->
      ModuleHead <$> toTyped origin
        <*> annModuleName name
        <*> annMaybe annWarningText mbWarn
        <*> annMaybe annExportSpecList mbExports

annModuleName :: Ann ModuleName
annModuleName name =
  case name of
    ModuleName origin string ->
      ModuleName <$> toTyped origin <*> pure string

annWarningText :: Ann WarningText
annWarningText = annDummy

annExportSpecList :: Ann ExportSpecList
annExportSpecList = annDummy

annPragma :: Ann ModulePragma
annPragma = annDummy

annImportDecl :: Ann ImportDecl
annImportDecl = annDummy

annDecl :: Ann Decl
annDecl decl =
  case decl of
    FunBind origin matches ->
      FunBind
        <$> toTyped origin
        <*> mapM annMatch matches
    _ -> annDummy decl

annMatch :: Ann Match
annMatch match =
  case match of
    Match origin name pats rhs mbBinds ->
      Match
        <$> toTyped origin
        <*> annName binding name
        <*> mapM annDummy pats
        <*> annDummy rhs
        <*> annMaybe annDummy mbBinds

annName :: (Origin -> AnnM Typed) -> Ann Name
annName handler name =
  case name of
    Ident origin ident ->
      Ident <$> handler origin <*> pure ident
    _ -> annDummy name



------------------------------------
-- Misc

lookupType :: GlobalName -> AnnM (Maybe Type)
lookupType gname = asks $ Map.lookup gname . annTypes

lookupProof :: SrcSpanInfo -> AnnM (Maybe Proof)
lookupProof srcspan = asks $ Map.lookup srcspan . annProofs
