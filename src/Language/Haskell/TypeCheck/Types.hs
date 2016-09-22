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

type Coercion s = Proof s -> Proof s
data Proof s
  = ProofAbs [TcVar] (Proof s)
  | ProofAb (Proof s) [TcType s]
  | ProofLam Int (TcType s) (Proof s)
  | ProofSrc (TcType s)
  | ProofAp (Proof s) (Proof s)
  | ProofVar Int

-- PRPOLY:    \x. /\a. f (x @a)
--            \x -> Abs [a] (f (Ap [a] x))
-- PRFUN:     \x y. f (/\a. x @a y)
--            \x -> Lam y (f (Abs [a] (x `Ap` [a] `ApE` y)))
-- PRMONO:    \x. x                     Id
-- DEEP-SKOL: \x. f1 (/\a. f2 x)
-- SPEC:      \x. f (x @t)              Compose
-- FUN:       \x y. f2 (x (f1 y))
-- GEN1:      @a
-- GEN2:      f . @a
-- \f -> f
-- \x -> co_res (/\a. co_arg x)
-- \f x -> co_res (f (co_arg x))
-- AbsAp a f => \x -> /\a. f (x @a)
-- FunAbsAp a f => \x y -> f (/\a. x @a y)

-- instance P.Pretty (Coercion s) where
--     prettyPrec _ c = Doc.text "not implemented"
        -- case c of
        --     CoerceId  ->
        --         Doc.text "id"
        --     CoerceAbs vars ->
        --         Doc.text "∀" Doc.<+> Doc.hsep (map P.pretty vars) Doc.<> Doc.dot
        --         -- Doc.text "abs" Doc.<+> P.pretty vars
        --     CoerceAp metas ->
        --         Doc.text "@" Doc.<+> Doc.hsep (map (P.prettyPrec appPrecedence) metas)
                -- Doc.text "ap" Doc.<+> P.pretty metas

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
            TcForall vars qual ->
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

instance P.Pretty GlobalName where
    pretty (GlobalName _ qname) = P.pretty qname

instance P.Pretty QualifiedName where
    pretty (QualifiedName m ident) =
        Doc.text (m ++ "." ++ ident)

instance P.Pretty (TcPred s) where
    pretty (TcIsIn gname t) =
        P.pretty gname Doc.<+> P.pretty t

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
  = Binding GlobalName Type SrcSpanInfo
  | TypeApplication GlobalName [Type] SrcSpanInfo
  | Resolved GlobalName SrcSpanInfo
  | ScopeError Scope.ScopeError
  | None
