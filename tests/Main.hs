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
import Z3.Monad as Z3

import qualified Data.Text.Encoding.Error as T
import qualified Data.Text.Lazy as Tl
import qualified Data.Text.Lazy.Encoding as Tl

import Distribution.Compiler
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Version

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
  , ParseOk _ gpd <- parsePackageDescription (Tl.unpack (Tl.decodeUtf8With T.ignore lbs)) = do
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

        Just x <- getDependency $ Dependency (PackageName "Coroutine") anyVersion
        bs <- astToString x
        liftIO $ putStrLn bs

        _b <- getDependency $ Dependency (PackageName "base") anyVersion
        bns <- getDependencyNodes $ Dependency (PackageName "base") anyVersion
        b <- getDistinctVersion $ Dependency (PackageName "base") anyVersion
        bs <- astToString b
        liftIO $ putStrLn bs

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
