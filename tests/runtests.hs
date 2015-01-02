module Main (main) where

import           Control.Monad                   (fmap, mplus, when)
import           Data.Foldable                   (foldMap)
import           Data.List                       (nub, partition)
import           Data.Maybe                      (fromMaybe,maybeToList)
import           Language.Haskell.Exts.Annotated
import           Language.Haskell.Scope
import           Language.Haskell.TypeCheck
import           Language.Haskell.TypeCheck.Monad
import           Language.Haskell.TypeCheck.Infer
import           Language.Haskell.TypeCheck.Types
import           System.Directory                (doesFileExist)
import           System.Environment              (getArgs)
import           System.Exit                     (ExitCode (..), exitWith)
import           System.FilePath                 (replaceExtension, (<.>))
import           System.IO                       (hPutStrLn, stderr)
import           Test.Framework                  (defaultMain, testGroup)
import           Test.Framework.Providers.HUnit
import           Test.HUnit
import           Text.PrettyPrint.ANSI.Leijen    (Doc, indent, text, underline,
                                                  vsep, (<>), (<+>))
import           Text.Printf                     (printf)
import qualified Data.Map as Map
import qualified Text.PrettyPrint.ANSI.Leijen as Doc

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
  []

--scopeTest :: String -> FilePath -> Test
scopeTest name = testCase name $ do
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
          allResolved = nub $ foldMap getResolved scoped
          getResolved (Origin (Resolved gname) loc) = [(loc, gname)]
          getResolved _ = []
      tcEnv <- runTI emptyTcEnv (tiModule scoped)
      return $ Right $ show $ Doc.vsep $
        [ ppGName usage gname <+> text "::" <+> tyMsg Doc.<$$>
          Doc.indent 2 (Doc.pretty coercion)
        | (usage, gname) <- allResolved
        , ty <- maybeToList (Map.lookup gname (tcEnvValues tcEnv))
        , let tyMsg = Doc.pretty ty
              coercion = Map.findWithDefault CoerceId usage
                                (tcEnvCoercions tcEnv) ]
        ++ [Doc.empty]

ppGName :: SrcSpanInfo -> GlobalName -> Doc
ppGName srcSpanInfo (GlobalName _defLoc (QualifiedName m ident))
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
