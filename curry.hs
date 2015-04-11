{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Main (main) where

import Control.Applicative
import Control.Concurrent.STM (TVar, atomically, newTVarIO, readTVar, readTVarIO, writeTVar)
import Control.Exception (Exception, throwIO)
import Control.Lens
import Control.Monad as Monad
import Control.Monad.State.Strict as State
import Control.Monad.Trans.Control (MonadBaseControl)
import Data.ByteString.Char8 ()
import qualified Data.ByteString.Lazy as Bl
import Data.Foldable (Foldable)
import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Encoding.Error as T
import qualified Data.Text.Lazy as Tl
import qualified Data.Text.Lazy.Encoding as Tl
import Data.Traversable (Traversable, traverse)
import Network.HTTP.Types
import Network.Wai as Wai
import Network.Wai.Handler.Warp as Warp
import Data.Aeson (Result(..), fromJSON, json')
import Data.Conduit
import Data.Conduit.Attoparsec
import qualified Z3.Base as Z3B
import Z3.Base (Result(..))
import Z3.Lang as Z3
import Z3.Lang.Monad as Z3
import System.FilePath
import System.IO
import Codec.Archive.Tar as Tar
import Debug.Trace (trace)

import Distribution.Compat.ReadP (readP_to_S)
import Distribution.Compiler
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.PackageDescription.PrettyPrint (showGenericPackageDescription)
import Distribution.Text as Dt
import Distribution.Version
import Text.PrettyPrint hiding ((<>), ($$))

parseDependencies :: [T.Text] -> [Dependency]
parseDependencies = concatMap step where
  step x = [dep | (dep, "") <- readP_to_S Dt.parse (T.unpack x)]

curryApp :: TVar HakeSolverState -> TVar Z3State -> Wai.Application
curryApp stref z3ref req
  | "GET" <- requestMethod req, ["package", pkgName] <- pathInfo req = do
      pkgs <- hakeSolverGenDesc <$> liftIO (readTVarIO stref)
      let desc = do
            ve <- Map.lookup (PackageName (T.unpack pkgName)) pkgs
            (g, _) <- Map.maxView ve
            return . T.encodeUtf8 . T.pack $ showGenericPackageDescription g

      case desc of
        Just val -> return $ responseLBS status200 [("Content-Type", "text/plain")] (Bl.fromChunks [val])
        Nothing  -> return $ responseLBS status404 [] "Package not found"

  | "PUT" <- requestMethod req, ["search", "package", pkgName] <- pathInfo req = do
      constraints <- requestBody req $$ sinkParser json'
      case fromJSON constraints of
        Error str -> fail str
        Success deps -> do
          let deps' = parseDependencies deps
          liftIO $ print deps'
          (st, z3s) <- liftIO . atomically $ (,) <$> readTVar stref <*> readTVar z3ref
          (res, st', z3s') <- evalHakeSolverT st z3s $ do
            ghcFlag <- getConfVar (PackageName "##global") (Impl GHC anyVersion)
            distVars <- Z3.and_ <$> mapM getDistinctVersion deps'
            depsVars <- Z3.and_ <$> mapM getDependency deps'
            pkgs <- gets hakeSolverGenDesc
            Z3B.withContext $ do
              -- lift $ assert ghcFlag
              -- lift $ assert distVars
              -- assert depsVars
              getLatestVersion $ PackageName (T.unpack pkgName)

          liftIO . atomically $ do
            writeTVar z3ref z3s'
            writeTVar stref st'

          case res of
            Sat pkgId -> do
              let asUrl = T.encodeUtf8 . mappend "https://hackage.haskell.org/package/archive/" . T.pack . renderOneLine
                  headers = [("Location", asUrl pkgId)]
              return $ responseLBS status303 headers Bl.empty

            Unsat ->
              let headers = [("Reason", "Unsat")]
              in return $ responseLBS status404 headers Bl.empty

            Undef ->
              let headers = [("Reason", "Undef")]
              in return $ responseLBS status404 headers Bl.empty

  | "PUT" <- requestMethod req, ["search", "module", moduleName] <- pathInfo req = do
      error "search/module/..."

  -- | ("package":xs) <- pathInfo req = return . responseLBS status200 [] $ "ok\n" <> Bl.fromChunks (fmap T.encodeUtf8 xs)
  | otherwise = fail "foo"

foldEntriesM :: (Exception e, MonadIO m) => (a -> Entry -> m a) -> a -> Entries e -> m a
foldEntriesM f = step where
  step !s (Next e es) = f s e >>= flip step es
  step s Tar.Done = return s
  step _ (Fail e) = liftIO $ throwIO e

main :: IO ()
main = do
  entries <- Tar.read <$> Bl.readFile "/Source/curry/00-index.tar"
  -- entries <- Tar.read <$> Bl.readFile "/Source/curry/test.tar"

  let step !agg e
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

  gpdMap <- foldEntriesM step Map.empty entries

  let gpdHakeMap = splitDependMap gpdMap
      packages    = Map.keys gpdMap
      initPackages = do
        return ()
        -- forM_ packages getPackage
        -- forM_ (Map.keys gpdHakeMap) assertDistinctVersion

  z3s <- initZ3State Z3.stdArgs

  (st, z3s') <- runZ3 (execStateT (runHakeSolverT initPackages)
          HakeSolverState
            { hakeSolverGenDesc = gpdHakeMap
            , hakeSolverVars = Map.empty
            , hakeSolverPkgs = Map.empty
            }) z3s

  forM_ (Map.keys (hakeSolverVars st)) $ \ (OrderedConfVar v) -> print v

  z3ref <- newTVarIO z3s'
  stref <- newTVarIO st

  -- Warp.run 7575 $ curryApp st{currySolverGenDesc = Map.empty} z3ref
  Warp.run 7575 $ curryApp stref z3ref
