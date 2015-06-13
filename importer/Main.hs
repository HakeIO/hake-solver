{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Codec.Archive.Tar as Tar
import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class
import Control.Monad.Trans.Resource
import System.Exit (ExitCode(ExitSuccess))
import System.FilePath
import System.IO
import System.Process (readCreateProcessWithExitCode, shell)

import Data.Aeson as Aeson

import qualified Data.Vector as V

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Encoding.Error as T
import qualified Data.Text.Lazy as Tl
import qualified Data.Text.Lazy.Encoding as Tl

import Distribution.ModuleName (ModuleName)
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Text (display)
import Distribution.Version

import qualified Data.ByteString.Lazy as Bl

instance ToJSON GenericPackageDescription where
  toJSON GenericPackageDescription{..} = object
    [ "flags" .= toJSON genPackageFlags
    , "libraries" .= toJSON condLibrary
    ]

instance ToJSON Flag where
  toJSON MkFlag{flagName = FlagName name, ..} = object
    [ "name" .= name
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

instance ToJSON c => ToJSON (Condition c) where
  toJSON (Var c) = toJSON c
  toJSON (Lit f) = toJSON f
  toJSON (CNot c) = object ["not" .= toJSON c]
  toJSON (COr l r) = object ["or" .= V.fromList [toJSON l, toJSON r]]
  toJSON (CAnd l r) = object ["and" .= V.fromList [toJSON l, toJSON r]]

instance ToJSON ConfVar where
  toJSON (OS os) = object ["os" .= display os]
  toJSON (Arch arch) = object ["arch" .= display arch]
  toJSON (Flag (FlagName flagName)) = object ["flag" .= flagName]
  toJSON (Impl compiler version) = object ["compiler" .= display compiler, "version" .= toJSON version]

instance ToJSON VersionRange where
  toJSON = toJSON . display

instance ToJSON Version where
  toJSON = toJSON . display

instance ToJSON Dependency where
  toJSON (Dependency package version) = object
    [ "package" .= display package
    , "version" .= toJSON version
    ]

instance ToJSON Library where
  toJSON Library{..} = object
    [ "library" .= toJSON ("hum" :: String)
    ]

instance ToJSON ModuleName where
  toJSON = toJSON . display

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
  , ParseOk _ gpd <- parsePackageDescription (Tl.unpack (Tl.decodeUtf8With T.ignore lbs)) = do
      liftIO . Bl.putStrLn $ encode gpd

  | otherwise = liftIO $ do
      return agg

main :: IO ()
main = runResourceT $ do
  entries <- liftIO $ Tar.read <$> (Bl.readFile =<< packageTarball)
  _ <- foldEntriesM (loadPackageDescriptions) () entries
  return ()
