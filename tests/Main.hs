{-# LANGUAGE BangPatterns #-}

module Main where

import Codec.Archive.Tar as Tar
import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class
import Data.Map.Lazy as Map
import System.FilePath
import System.IO
import Z3.Monad as Z3

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Encoding.Error as T
import qualified Data.Text.Lazy as Tl
import qualified Data.Text.Lazy.Encoding as Tl

import Distribution.Compat.ReadP (readP_to_S)
import Distribution.Compiler
import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.PackageDescription.PrettyPrint (showGenericPackageDescription)
import Distribution.Text as Dt
import Distribution.Version

import qualified Data.ByteString.Lazy as Bl

packageTarball :: String
packageTarball = "/Users/nhowell/Library/Haskell/repo-cache/hackage.haskell.org/00-index.tar"

foldEntriesM :: (Exception e, MonadIO m) => (a -> Entry -> m a) -> a -> Entries e -> m a
foldEntriesM f = step where
  step !s (Next e es) = f s e >>= flip step es
  step s Tar.Done = return s
  step _ (Fail e) = liftIO $ throwIO e

step !agg e
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

globalDatabase :: Z3 ()
globalDatabase = do
  entries <- liftIO $ Tar.read <$> Bl.readFile packageTarball
  gpdMap <- liftIO $ foldEntriesM step Map.empty entries
  return ()

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
  env <- Z3.newEnv (Just QF_BV) stdOpts
  evalZ3WithEnv globalDatabase env
  (x, y) <- evalZ3WithEnv (local query) env
  print x
  print y
  return ()
