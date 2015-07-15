module Language.Haskell.TypeCheck.Types where

import           Data.Binary
import           Data.IORef
import           Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.TypeCheck.Pretty as P
import           System.IO.Unsafe                  (unsafePerformIO)
import qualified Text.PrettyPrint.ANSI.Leijen      as Doc

import           Language.Haskell.Scope            (GlobalName (..),
                                                    QualifiedName (..))

-- Type variables are uniquely identified by their name and binding point.
-- The binding point is not enough since ty vars can be bound at an implicit
-- forall.
data TcVar = TcVar String SrcSpanInfo
    deriving ( Show, Eq )

data TcMetaVar = TcMetaRef String (IORef (Maybe TcType))
instance Show TcMetaVar where
    show (TcMetaRef name _) = name
instance Eq TcMetaVar where
    TcMetaRef _ r1 == TcMetaRef _ r2 = r1==r2

instance Binary TcMetaVar where
    put (TcMetaRef name _) = put name
    -- put = error "Binary.put: TcMetaVar"
    get = do
        name <- get
        return $ TcMetaRef name (unsafePerformIO $ newIORef Nothing)
    -- get = error "Binary.get: TcMetaVar"

data TcType
    = TcForall [TcVar] (Qual TcType)
    | TcFun TcType TcType
    | TcApp TcType TcType
    -- Uninstantiated tyvar
    | TcRef TcVar
    | TcCon QualifiedName
    -- Instantiated tyvar
    | TcMetaVar TcMetaVar
    | TcUnboxedTuple [TcType]
    | TcTuple [TcType]
    | TcList TcType
    | TcUndefined
    deriving ( Show, Eq )

data Coercion
    = CoerceId
    | CoerceAbs [TcVar]
    | CoerceAp [TcType]
    deriving ( Show , Eq)

instance P.Pretty Coercion where
    prettyPrec _ c =
        case c of
            CoerceId  ->
                Doc.text "id"
            CoerceAbs vars ->
                Doc.text "abs" Doc.<+> P.pretty vars
            CoerceAp metas ->
                Doc.text "ap" Doc.<+> P.pretty metas

-- for arguments to the left of ->
arrowPrecedence :: Int
arrowPrecedence = 1

-- for arguments of type or data constructors, or of a class.
appPrecedence :: Int
appPrecedence = 2

instance P.Pretty TcType where
    prettyPrec p ty =
        case ty of
            TcForall [] ([] :=> t) ->
                P.pretty t
            TcForall vars qual ->
                Doc.text "∀" Doc.<+> Doc.hsep (map P.pretty vars) Doc.<>
                Doc.dot Doc.<+> P.pretty qual
            TcFun a b -> P.parensIf (p > 0) $
                P.prettyPrec arrowPrecedence a Doc.<+>
                Doc.text "→ " Doc.<+> P.pretty b
            TcApp a b -> P.parensIf (p > arrowPrecedence) $
                P.pretty a Doc.<+> P.prettyPrec appPrecedence b
            TcCon (QualifiedName m ident) ->
                Doc.text (m ++ "." ++ ident)
            TcRef var -> P.pretty var
            TcMetaVar meta ->
                P.pretty meta
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

instance P.Pretty TcMetaVar where
    pretty (TcMetaRef ident ref) =
        -- Doc.parens (Doc.text ident) Doc.<>
        unsafePerformIO (do
        mbTy <- readIORef ref
        case mbTy of
            Just ty -> return $ P.pretty ty
            Nothing -> return $ Doc.blue (Doc.text ident))
    --pretty (TcMetaRef ident _) = Doc.blue (Doc.text ident)

instance P.Pretty t => P.Pretty (Qual t) where
    prettyPrec p ([] :=> t) = P.prettyPrec p t
    prettyPrec p (quals :=> t) =
        Doc.parens (Doc.hsep $ Doc.punctuate Doc.comma $ map P.pretty quals) Doc.<+>
        Doc.text "⇒" Doc.<+> P.prettyPrec p t

instance P.Pretty Pred where
    pretty (IsIn _gname _t) = error "Pretty pred"

data Qual t = [Pred] :=> t
    deriving ( Show, Eq )
data Pred = IsIn GlobalName TcType
    deriving ( Show, Eq )

-- Uninstantiated type signature.
-- eg: forall a. Maybe a -- type of Nothing
-- eg: Int -- type of 10
--data Scheme = Scheme [TcVar] (Qual TcType)
--    deriving ( Show )

--data Typed = Typed TcType Origin


