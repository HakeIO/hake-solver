{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Codec.Archive.Tar as Tar
import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class
import Control.Monad.Trans.Resource
import System.Exit (ExitCode(ExitSuccess))
import System.FilePath
import System.Process (readCreateProcessWithExitCode, shell)

import Data.Aeson as Aeson

import qualified Data.Vector as V

import Distribution.ModuleName (ModuleName)
import Distribution.Types.GenericPackageDescription (GenericPackageDescription(..))
import Distribution.Types.ConfVar (ConfVar(..))
import Distribution.Types.Flag (PackageFlag(..), unFlagName)
import Distribution.Types.Library (Library(..))
import Distribution.Types.Dependency (Dependency, depPkgName, depVerRange)
import Distribution.Types.CondTree (CondTree(..), CondBranch(..))
import Distribution.Types.Condition (Condition(..))
import Distribution.Types.Version (Version)
import Distribution.Types.VersionRange (VersionRange)
import Distribution.Pretty (prettyShow)
import Distribution.PackageDescription.Parsec (parseGenericPackageDescription, runParseResult)

import qualified Data.ByteString.Lazy as Bl

instance ToJSON GenericPackageDescription where
  toJSON GenericPackageDescription{..} = object
    [ "flags" .= toJSON genPackageFlags
    , "libraries" .= toJSON condLibrary
    ]

instance ToJSON PackageFlag where
  toJSON MkPackageFlag{..} = object
    [ "name" .= unFlagName flagName
    , "description" .= flagDescription
    , "default" .= flagDefault
    , "manual" .= flagManual
    ]

instance (ToJSON v, ToJSON c, ToJSON a) => ToJSON (CondTree v c a) where
  toJSON CondNode{..} = object
    [ "data" .= toJSON condTreeData
    , "constraints" .= toJSON condTreeConstraints
    , "components" .= toJSON condTreeComponents
    ]

instance (ToJSON v, ToJSON c, ToJSON a) => ToJSON (CondBranch v c a) where
  toJSON (CondBranch cond ifTrue maybeIfFalse) = object
    [ "condition" .= toJSON cond
    , "if-true" .= toJSON ifTrue
    , "if-false" .= toJSON maybeIfFalse
    ]

instance ToJSON c => ToJSON (Condition c) where
  toJSON (Var c) = toJSON c
  toJSON (Lit f) = toJSON f
  toJSON (CNot c) = object ["not" .= toJSON c]
  toJSON (COr l r) = object ["or" .= V.fromList [toJSON l, toJSON r]]
  toJSON (CAnd l r) = object ["and" .= V.fromList [toJSON l, toJSON r]]

instance ToJSON ConfVar where
  toJSON (OS os) = object ["os" .= prettyShow os]
  toJSON (Arch arch) = object ["arch" .= prettyShow arch]
  toJSON (PackageFlag fn) = object ["flag" .= unFlagName fn]
  toJSON (Impl compiler version) = object ["compiler" .= prettyShow compiler, "version" .= toJSON version]

instance ToJSON VersionRange where
  toJSON = toJSON . prettyShow

instance ToJSON Version where
  toJSON = toJSON . prettyShow

instance ToJSON Dependency where
  toJSON dep = object
    [ "package" .= prettyShow (depPkgName dep)
    , "version" .= toJSON (depVerRange dep)
    ]

instance ToJSON Library where
  toJSON _ = object
    [ "library" .= toJSON ("hum" :: String)
    ]

instance ToJSON ModuleName where
  toJSON = toJSON . prettyShow

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

loadPackageDescriptions
  :: ()
  -> Entry
  -> ResourceT IO ()
loadPackageDescriptions !agg e
  | ".cabal" <- takeExtension (entryPath e)
  , NormalFile lbs _fs <- entryContent e
  = do
      let strictBs = Bl.toStrict lbs
      case snd $ runParseResult $ parseGenericPackageDescription strictBs of
        Left _ -> liftIO $ return agg
        Right gpd -> liftIO $ do
          Bl.putStr $ encode gpd
          Bl.putStr "\n"

  | otherwise = liftIO $ do
      return agg

main :: IO ()
main = runResourceT $ do
  entries <- liftIO $ Tar.read <$> (Bl.readFile =<< packageTarball)
  _ <- foldEntriesM (loadPackageDescriptions) () entries
  return ()
