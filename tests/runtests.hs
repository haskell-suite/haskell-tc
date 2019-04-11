module Main (main) where

import           Control.Monad                     (when)
import qualified Data.ByteString.Lazy              as BL
import           Data.Foldable                     (foldMap)
import           Data.List                         (nub, sort)
import qualified Data.Text                         as T
import qualified Data.Text.Encoding                as T
import           Language.Haskell.Exts             hiding (name)
import           Language.Haskell.Scope            (emptyResolveEnv, resolve)
import qualified Language.Haskell.Scope            as Scope
import           Language.Haskell.TypeCheck
import qualified Language.Haskell.TypeCheck.Pretty as P
import           System.Directory                  (doesFileExist)
import           System.Environment                (getArgs)
import           System.Exit                       (ExitCode (..), exitWith)
import           System.FilePath                   (replaceExtension,
                                                    takeBaseName)
import           System.IO                         (hPutStrLn, stderr)
import           Text.PrettyPrint.ANSI.Leijen      (Doc, indent, text,
                                                    underline, vsep, (<+>),
                                                    (<>))
import qualified Text.PrettyPrint.ANSI.Leijen      as Doc

import           Test.Tasty
import           Test.Tasty.ExpectedFailure
import           Test.Tasty.Golden


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
            putStr err
            hPutStrLn stderr ""
            exitWith (ExitFailure 1)
          Right msg -> do
            putStr msg
            exitWith ExitSuccess
    _ -> return ()
  goldenFiles <- sort <$> findByExtension [".stdout"] "tests"
  defaultMain $ testGroup "Tests"
    [ (if testName `elem` ignoreList
        then ignoreTest
        else id)
      (goldenVsText testName goldenFile (getTcInfo' testFile))
    | goldenFile <- goldenFiles
    , let testFile = replaceExtension goldenFile "hs"
    , let testName = takeBaseName goldenFile
    ]
  where
    ignoreList = []

getTcInfo' :: FilePath -> IO String
getTcInfo' path = fmap (either id id) (getTcInfo path)

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
      let (_env, _errs, scoped) = resolve emptyResolveEnv thisModule
      case typecheck emptyTcEnv scoped of
        Left err -> return $ Left $ show err
        Right (typed, _env') -> do
          let allTyped = nub $ foldMap getTyped typed
              getTyped (Coerced nameInfo src proof) = [(nameInfo, src, proof)]
              getTyped _                            = []

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

goldenVsText :: TestName -> FilePath -> IO String -> TestTree
goldenVsText name path gen =
    goldenVsStringDiff name (\ref new -> ["diff", ref, new]) path gen'
  where
    gen' = BL.fromStrict . T.encodeUtf8 . T.pack <$> gen
