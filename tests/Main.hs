{-# LANGUAGE BangPatterns #-}

module Main where

import Codec.Archive.Tar as Tar
import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class
import Control.Monad.State.Lazy (state)
import Data.Foldable
import Data.Map.Lazy as Map
import System.Exit (ExitCode(ExitSuccess))
import System.FilePath
import System.IO
import System.Process (readCreateProcessWithExitCode, shell)
import Z3.Monad as Z3 hiding (Version)

import Distribution.Compiler (CompilerId(..), CompilerFlavor(..))
import Distribution.Types.PackageId (PackageIdentifier)
import Distribution.Types.PackageName (mkPackageName)
import Distribution.Types.GenericPackageDescription (GenericPackageDescription(..), ConfVar(..))
import Distribution.Types.Dependency (Dependency, mkDependency)
import Distribution.Types.LibraryName (defaultLibName)
import Distribution.Types.VersionRange (anyVersion)
import Distribution.PackageDescription.Parsec (parseGenericPackageDescription, runParseResult)
import Distribution.Package (packageId)
import qualified Distribution.Compat.NonEmptySet as NES

import Development.Hake.Solver

import qualified Data.ByteString.Lazy as Bl

packageTarball :: IO String
packageTarball = do
  let cmd = shell "grep remote-repo-cache ~/.cabal/config | awk '{print $2}'"
  (ExitSuccess, dirs, _) <- readCreateProcessWithExitCode cmd ""
  case lines dirs of
    [dir] -> return $ combine dir "hackage.haskell.org/00-index.tar"
    _ -> fail "uhm"

foldEntriesM
  :: (Exception e, MonadIO m)
  => (a -> Entry -> m a)
  -> a
  -> Entries e
  -> m a
foldEntriesM f = step where
  step !s (Next e es) = f s e >>= flip step es
  step s Tar.Done = return s
  step _ (Fail e) = liftIO $ throwIO e

takeEntries
  :: Int
  -> Entries e
  -> Entries e
takeEntries 0 _ = Tar.Done
takeEntries i (Next e es) = Next e (takeEntries (i-1) es)
takeEntries _ x = x

loadPackageDescriptions
  :: Map PackageIdentifier GenericPackageDescription
  -> Entry
  -> IO (Map PackageIdentifier GenericPackageDescription)
loadPackageDescriptions !agg e
  | ".cabal" <- takeExtension (entryPath e)
  , NormalFile lbs _fs <- entryContent e
  = do
      let strictBs = Bl.toStrict lbs
      case snd $ runParseResult $ parseGenericPackageDescription strictBs of
        Left _ -> do
          putChar 'x'
          hFlush stdout
          return agg
        Right gpd -> do
          putChar '.'
          hFlush stdout
          return $ Map.insert (packageId gpd) gpd agg

  | otherwise = do
      putChar 'x'
      hFlush stdout
      return agg

loadGlobalDatabase
  :: HakeSolverT Z3 ()
loadGlobalDatabase = do
  entries <- liftIO $ Tar.read <$> (Bl.readFile =<< packageTarball)
  let entries' = takeEntries 10000 entries
  gpdMap <- liftIO $ foldEntriesM loadPackageDescriptions Map.empty entries'
  let gpdHakeMap = splitPackageIdentifiers gpdMap
  state (\ x -> ((), x{hakeSolverGenDesc = gpdHakeMap}))

mkDep :: String -> Dependency
mkDep name = mkDependency (mkPackageName name) anyVersion (NES.singleton defaultLibName)

query :: Z3 (Result, Maybe String)
query = do
  x <- mkFreshBoolVar "x"
  assert x
  (res, mmodel) <- getModel
  case mmodel of
    Just model -> do
      str <- modelToString model
      return (res, Just str)
    Nothing -> return (res, Nothing)

main :: IO ()
main = do
  env <- Z3.newEnv Nothing stdOpts
  st <- execHakeSolverT defaultSolverState env loadGlobalDatabase

  let prog = do
        setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
        ghcFlag <- getGlobalConfVar (Impl GHC anyVersion)
        assert ghcFlag

        Just x <- getDependency $ mkDep "Coroutine"
        bs <- astToString x
        liftIO $ putStrLn bs

        _b <- getDependency $ mkDep "base"
        bns <- getDependencyNodes $ mkDep "base"
        b <- getDistinctVersion $ mkDep "base"
        bs' <- astToString b
        liftIO $ putStrLn bs'

        assert b
        assert x
        (res, mmodel) <- getModel
        case mmodel of
          Just model -> do
            -- str <- modelToString model
            for_ bns $ \ (pn, bn) -> do
              mmev <- evalBool model bn
              liftIO $ case mmev of
                Just True -> putStrLn $ "Ploz install: " ++ show pn
                Just False -> putStrLn $ "Skip: " ++ show pn
                Nothing -> putStrLn $ "Undef: " ++ show pn
            return (res, Just "")
          Nothing -> return (res, Nothing)

  (x, _st') <- runLocalHakeSolverT st env prog

  case x of
    (Sat, Just str) -> do
      putStrLn "found model"
      putStr str
    _ -> print x
