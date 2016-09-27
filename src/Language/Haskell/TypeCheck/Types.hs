module Language.Haskell.TypeCheck.Types where

import           Data.IORef
import           Data.STRef
import           Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.TypeCheck.Pretty as P
import           System.IO.Unsafe                  (unsafePerformIO)
import qualified Text.PrettyPrint.ANSI.Leijen      as Doc

import           Language.Haskell.Scope            (GlobalName (..),
                                                    QualifiedName (..))
import qualified Language.Haskell.Scope as Scope

-- Type variables are uniquely identified by their name and binding point.
-- The binding point is not enough since ty vars can be bound at an implicit
-- forall.
data TcVar = TcVar String SrcSpanInfo
    deriving ( Show, Eq, Ord )

data TcMetaVar s = TcMetaRef String (STRef s (Maybe (TcType s)))
instance Show (TcMetaVar s) where
    show (TcMetaRef name _) = name
instance Eq (TcMetaVar s) where
    TcMetaRef _ r1 == TcMetaRef _ r2 = r1==r2
instance Ord (TcMetaVar s) where
    compare (TcMetaRef i1 _) (TcMetaRef i2 _) = compare i1 i2

data Expected s a = Infer (STRef s a) | Check a

data TcType s
    = TcForall [TcVar] (TcQual s (TcType s))
    | TcFun (TcType s) (TcType s)
    | TcApp (TcType s) (TcType s)
    -- Uninstantiated tyvar
    | TcRef TcVar
    | TcCon QualifiedName
    -- Instantiated tyvar
    | TcMetaVar (TcMetaVar s)
    | TcUnboxedTuple [TcType s]
    | TcTuple [TcType s]
    | TcList (TcType s)
    | TcUndefined
    deriving ( Show, Eq, Ord )

-- Foralls can appear anywhere.
type Sigma s = TcType s
-- No foralls at the top-level
type Rho s = TcType s
-- No foralls anywhere.
type Tau s = TcType s

type ExpectedRho s = Expected s (Rho s)

data Type
    = TyForall [TcVar] (Qualified Type)
    | TyFun Type Type
    | TyApp Type Type
    | TyRef TcVar
    | TyCon QualifiedName
    | TyUnboxedTuple [Type]
    | TyTuple [Type]
    | TyList Type
    | TyUndefined
    deriving ( Show, Eq, Ord )

toTcType :: Type -> TcType s
toTcType ty =
  case ty of
    TyForall tyvars (pred :=> t) -> TcForall tyvars (TcQual (map toTcPred pred) (toTcType t))
    TyFun t1 t2 -> TcFun (toTcType t1) (toTcType t2)
    TyApp t1 t2 -> TcApp (toTcType t1) (toTcType t2)
    TyRef tyvar -> TcRef tyvar
    TyCon qualifiedName -> TcCon qualifiedName
    TyUnboxedTuple tys -> TcUnboxedTuple (map toTcType tys)
    TyTuple tys -> TcTuple (map toTcType tys)
    TyList t1 -> TcList (toTcType t1)
    TyUndefined -> TcUndefined

toTcPred :: Predicate -> TcPred s
toTcPred (IsIn className ty) = TcIsIn className (toTcType ty)

-- data Coercion s
--     = CoerceId
--     | CoerceAbs [TcVar]
--     | CoerceAp [TcType s]
--     | CoerceFun (Coercion s) (Coercion s)
--     | CoerceCompose (Coercion s) (Coercion s)
--     | CoerceAbsAp [TcVar] (Coercion s)
--     | CoerceFunAbsAp [TcVar] (Coercion s)
--     deriving (Show , Eq)

type TcCoercion s = TcProof s -> TcProof s
data TcProof s
  = TcProofAbs [TcVar] (TcProof s)
  | TcProofAp (TcProof s) [TcType s]
  | TcProofLam Int (TcType s) (TcProof s)
  | TcProofSrc (TcType s)
  | TcProofPAp (TcProof s) (TcProof s)
  | TcProofVar Int

type Coercion = Proof -> Proof
data Proof
  = ProofAbs [TcVar] Proof
  | ProofAp Proof [Type]
  | ProofLam Int Type Proof
  | ProofSrc Type
  | ProofPAp Proof Proof
  | ProofVar Int



-- for arguments to the left of ->
arrowPrecedence :: Int
arrowPrecedence = 1

-- for arguments of type or data constructors, or of a class.
appPrecedence :: Int
appPrecedence = 2

instance P.Pretty (TcType s) where
  prettyPrec p ty =
    case ty of
      TcForall [] (TcQual [] t) ->
        P.prettyPrec p t
      TcForall vars qual -> P.parensIf (p > 0) $
        Doc.text "∀" Doc.<+> Doc.hsep (map P.pretty vars) Doc.<>
        Doc.dot Doc.<+> P.pretty qual
      TcFun a b -> P.parensIf (p > 0) $
        P.prettyPrec arrowPrecedence a Doc.<+>
        Doc.text "→ " Doc.<+> P.pretty b
      TcApp a b -> P.parensIf (p > arrowPrecedence) $
        P.pretty a Doc.<+> P.prettyPrec appPrecedence b
      TcCon (QualifiedName "" ident) ->
        Doc.text ident
      TcCon (QualifiedName m ident) ->
        Doc.text (m ++ "." ++ ident)
      TcRef var -> P.pretty var
      TcMetaVar meta ->
        P.prettyPrec p meta
      TcUnboxedTuple tys ->
        Doc.text "(#" Doc.<+>
        (Doc.hsep $ Doc.punctuate Doc.comma $ map P.pretty tys) Doc.<+>
        Doc.text "#)"
      TcTuple tys -> Doc.tupled (map P.pretty tys)
      TcList ty ->
        Doc.brackets (P.pretty ty)
      TcUndefined ->
        Doc.red (Doc.text "undefined")

instance P.Pretty TcVar where
    pretty (TcVar ident _src) = Doc.text ident

instance P.Pretty (TcMetaVar s) where
    -- prettyPrec p (TcMetaRef ident ref) =
    --     -- Doc.parens (Doc.text ident) Doc.<>
    --     unsafePerformIO (do
    --     mbTy <- readIORef ref
    --     case mbTy of
    --         Just ty -> return $ P.prettyPrec p ty
    --         Nothing -> return $ Doc.blue (Doc.text ident))
    pretty (TcMetaRef ident _) = Doc.blue (Doc.text ident)

instance P.Pretty t => P.Pretty (TcQual s t) where
    prettyPrec p (TcQual [] t) = P.prettyPrec p t
    prettyPrec p (TcQual quals t) =
        P.parensIf (length quals > 1) (Doc.hsep $ Doc.punctuate Doc.comma $ map P.pretty quals) Doc.<+>
        Doc.text "⇒" Doc.<+> P.prettyPrec p t

instance P.Pretty t => P.Pretty (Qualified t) where
    prettyPrec p ([] :=> t) = P.prettyPrec p t
    prettyPrec p (quals :=> t) =
        P.parensIf (length quals > 1) (Doc.hsep $ Doc.punctuate Doc.comma $ map P.pretty quals) Doc.<+>
        Doc.text "⇒" Doc.<+> P.prettyPrec p t

instance P.Pretty GlobalName where
    pretty (GlobalName _ qname) = P.pretty qname

instance P.Pretty QualifiedName where
    pretty (QualifiedName m ident) =
        Doc.text (m ++ "." ++ ident)

instance P.Pretty (TcPred s) where
    pretty (TcIsIn gname t) =
        P.pretty gname Doc.<+> P.pretty t

instance P.Pretty Predicate where
    pretty (IsIn gname t) =
        P.pretty gname Doc.<+> P.pretty t


instance P.Pretty Type where
  prettyPrec p ty =
    case ty of
      TyForall [] ([] :=> t) ->
        P.prettyPrec p t
      TyForall vars qual -> P.parensIf (p > 0) $
        Doc.text "∀" Doc.<+> Doc.hsep (map P.pretty vars) Doc.<>
        Doc.dot Doc.<+> P.pretty qual
      TyFun a b -> P.parensIf (p > 0) $
        P.prettyPrec arrowPrecedence a Doc.<+>
        Doc.text "→ " Doc.<+> P.pretty b
      TyApp a b -> P.parensIf (p > arrowPrecedence) $
        P.pretty a Doc.<+> P.prettyPrec appPrecedence b
      TyCon (QualifiedName "" ident) ->
        Doc.text ident
      TyCon (QualifiedName m ident) ->
        Doc.text (m ++ "." ++ ident)
      TyRef var -> P.pretty var
      TyUnboxedTuple tys ->
        Doc.text "(#" Doc.<+>
        (Doc.hsep $ Doc.punctuate Doc.comma $ map P.pretty tys) Doc.<+>
        Doc.text "#)"
      TyTuple tys -> Doc.tupled (map P.pretty tys)
      TyList ty ->
        Doc.brackets (P.pretty ty)
      TyUndefined ->
        Doc.red (Doc.text "undefined")

instance P.Pretty Proof where
  prettyPrec prec p =
    case p of
      ProofAbs tvs p' -> P.parensIf (prec > 0) $
        Doc.text "Λ" Doc.<> Doc.hsep (map P.pretty tvs) Doc.<> Doc.dot Doc.<+> P.pretty p'
      ProofAp p' tys -> P.parensIf (prec > 0) $
        P.prettyPrec arrowPrecedence p' Doc.<+> Doc.text "@" Doc.<+> Doc.hsep (map (P.prettyPrec appPrecedence) tys)
      ProofLam n ty p' -> -- P.parensIf (True) $
        Doc.text "λ" Doc.<>
        Doc.int n Doc.<> Doc.text "::" Doc.<> P.prettyPrec appPrecedence ty Doc.<>
        Doc.dot Doc.<+> P.pretty p'
      ProofSrc ty -> P.prettyPrec prec ty
      ProofPAp p1 p2 -> P.parensIf (prec > arrowPrecedence) $
        P.prettyPrec arrowPrecedence p1 Doc.<+> P.prettyPrec appPrecedence p2
      ProofVar n -> Doc.int n

data TcQual s t = TcQual [TcPred s] t
    deriving ( Show, Eq, Ord )
data Qualified t = [Predicate] :=> t
    deriving ( Show, Eq, Ord )

data TcPred s = TcIsIn GlobalName (TcType s)
    deriving ( Show, Eq, Ord )
data Predicate = IsIn GlobalName Type
    deriving ( Show, Eq, Ord )


--data Typed = Typed TcType Origin

data Typed
  = Binding GlobalName Type Proof SrcSpanInfo
  | Coerced Proof Scope.NameInfo SrcSpanInfo
  | Scoped Scope.NameInfo SrcSpanInfo
