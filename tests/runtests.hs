module Main (main) where

import           Control.Monad                     (fmap, mplus, when)
import           Data.Foldable                     (foldMap)
import           Data.Foldable                     (toList)
import           Data.List                         (nub, partition)
import qualified Data.Map                          as Map
import           Data.Maybe                        (fromMaybe, maybeToList)
import           Data.Maybe                        (isJust)
import           Language.Haskell.Exts
import           Language.Haskell.Scope            (Entity (..),
                                                    Origin (..),
                                                    QualifiedName (..),
                                                    emptyResolveEnv, resolve)
import qualified Language.Haskell.Scope            as Scope
import           Language.Haskell.TypeCheck
import           Language.Haskell.TypeCheck.Monad
import qualified Language.Haskell.TypeCheck.Pretty as P
import           Language.Haskell.TypeCheck.Types
import           System.Directory                  (doesFileExist)
import           System.Environment                (getArgs)
import           System.Exit                       (ExitCode (..), exitWith)
import           System.FilePath                   (replaceExtension, (<.>))
import           System.IO                         (hPutStrLn, stderr)
import           Test.Framework                    (defaultMain, testGroup)
import           Test.Framework.Providers.HUnit
import           Test.HUnit
import           Text.PrettyPrint.ANSI.Leijen      (Doc, indent, text,
                                                    underline, vsep, (<+>),
                                                    (<>))
import qualified Text.PrettyPrint.ANSI.Leijen      as Doc
import           Text.Printf                       (printf)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      exist <- doesFileExist path
      when exist $ do
        info <- getTcInfo path
        case info of
          Left err -> do
            hPutStrLn stderr err
            exitWith (ExitFailure 1)
          Right msg -> do
            putStr msg
            exitWith ExitSuccess
    _ -> return ()
  defaultMain unitTests

unitTests =
  [ typeTest "Basic1"
  , typeTest "Class1"
  , typeTest "Class2"
  , typeTest "Class3"
  , typeTest "Class4"
  , typeTest "Append"
  , typeTest "Map"
  , typeTest "AbsAp1"
  , typeTest "AbsAp2"
  , typeTest "AbsAp3"
  , typeTest "AbsAp4"
  , typeTest "InlinePragma"
  ]

--scopeTest :: String -> FilePath -> Test
typeTest name = testCase name $ do
  let testFile = name <.> "hs"
  expectedOutput <- readFile (replaceExtension testFile "stdout")
                        `mplus` return ""
  output <- either id id `fmap` getTcInfo testFile
  when (expectedOutput /= output) $ do
    fail "Diff Error"

getTcInfo :: FilePath -> IO (Either String String)
getTcInfo file = do
  fileContent <- readFile file
  parsed <- parseFile file
  case parsed of
    ParseFailed position msg -> do
      return $ Left $
        show position ++ "\n" ++
        msg
    ParseOk thisModule -> do
      let (env, errs, scoped) = resolve emptyResolveEnv thisModule
      case typecheck emptyTcEnv scoped of
        Left err -> error (show err)
        Right (typed, env') -> do
          let allTyped = nub $ foldMap getTyped typed
              getTyped (Coerced nameInfo src proof) = [(nameInfo, src, proof)]
              getTyped _ = []

              bindings = [ (src, proof) | (Scope.Binding{}, src, proof) <- allTyped ]
              builtin = [ (src, proof) | (Scope.None, src, proof) <- allTyped ]
              usages = [ (src, proof) | (Scope.Resolved{}, src, proof) <- allTyped ]

          return $ Right $ show $ Doc.vsep $
            [ Doc.text "Bindings:"] ++
            [ text "::" <+> tyMsg Doc.<$$>
              ppLocation 2 fileContent srcspan
            | (srcspan, proof) <- bindings
            , let tyMsg = P.pretty proof
            ] ++
            [ Doc.empty, Doc.text "Proofs:"] ++
            [ text "coercion" <> text ":" <+> tyMsg Doc.<$$>
              ppLocation 2 fileContent srcspan
            | (srcspan, proof)  <- builtin ++ usages
            , let tyMsg = P.pretty proof ] ++
            [Doc.empty]

ppGName :: SrcSpanInfo -> Entity -> Doc
ppGName srcSpanInfo Entity{entityName = QualifiedName m ident}
  | beginLine == endLine =
    Doc.pretty beginLine <> Doc.text ":" <> Doc.pretty beginColumn <>
    Doc.text "-" <> Doc.pretty endColumn <+>
    Doc.text m <> Doc.text "." <> Doc.text ident
  | otherwise =
    Doc.pretty beginLine <> Doc.text ":" <> Doc.pretty beginColumn <>
    Doc.text "-" <>
    Doc.pretty endLine <> Doc.text ":" <> Doc.pretty endColumn <+>
    Doc.text m <> Doc.text "." <> Doc.text ident
  where
    srcSpan = srcInfoSpan srcSpanInfo
    beginLine = srcSpanStartLine srcSpan
    beginColumn = srcSpanStartColumn srcSpan
    endLine = srcSpanEndLine srcSpan
    endColumn = srcSpanEndColumn srcSpan

ppQualName :: QualifiedName -> Doc
ppQualName (QualifiedName m ident) =
  Doc.text m <> Doc.text "." <> Doc.text ident

ppLocation :: Int -> String -> SrcSpanInfo -> Doc
ppLocation padding file srcSpanInfo =
    indent padding $ vsep $
    case relevantLines of
      [] -> []
      [line] ->
        let (before, line') = splitAt (beginColumn-1) line
            (highlight, after) = splitAt (endColumn-beginColumn) line'
        in [text before <> underline (text highlight) <> text after]
      (line:rest) -> map (underline . text) (line:rest)
  where
    relevantLines = take (endLine-beginLine+1) (drop (beginLine-1) (lines file))
    srcSpan = srcInfoSpan srcSpanInfo
    beginLine = srcSpanStartLine srcSpan
    beginColumn = srcSpanStartColumn srcSpan
    endLine = srcSpanEndLine srcSpan
    endColumn = srcSpanEndColumn srcSpan
