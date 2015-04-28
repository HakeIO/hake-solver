{-# LANGUAGE BangPatterns #-}

module Main where

import Control.Monad.IO.Class
import Control.Monad.State.Lazy (state)
import Control.Monad.Trans.Resource
import Data.Foldable
import Data.Map.Lazy as Map
import System.IO
import Z3.Monad as Z3

import qualified Database.LevelDB as LevelDB

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Encoding.Error as T

import Distribution.Compiler
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Version

import Development.Hake.Solver

loadGlobalDatabase
  :: HakeSolverT Z3 ()
loadGlobalDatabase = do
  gpdHakeMap <- liftIO . runResourceT $ do
    db <- LevelDB.open "/tmp/hackagedb" LevelDB.defaultOptions{LevelDB.createIfMissing = False}
    LevelDB.withIterator db LevelDB.defaultReadOptions $ \ iter ->
      let go :: Map PackageIdentifier GenericPackageDescription -> ResourceT IO (PackageVersionMap GenericPackageDescription)
          go agg = do
            isValid <- LevelDB.iterValid iter
            if not isValid
              then return $ splitPackageIdentifiers agg
              else do
                Just bs <- LevelDB.iterValue iter
                case parsePackageDescription . T.unpack $ T.decodeUtf8With T.ignore bs of
                  ParseOk _ gpd -> do
                    LevelDB.iterNext iter
                    liftIO $ putStr "."
                    liftIO $ hFlush stdout
                    go $ Map.insert (packageId gpd) gpd agg
                  _ -> fail "asdfasdf"

      in LevelDB.iterFirst iter >> go Map.empty

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
        ghcFlag <- getConfVar (PackageName "##global") (Impl GHC anyVersion)
        assert ghcFlag

        x <- getDependency $ Dependency (PackageName "Coroutine") anyVersion
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
