{-# LANGUAGE BangPatterns #-}

module Main where

import Codec.Archive.Tar as Tar
import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class
import Control.Monad.Trans.Resource
import System.Exit (ExitCode(ExitSuccess))
import System.FilePath
import System.IO
import System.Process (readCreateProcessWithExitCode, shell)

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Encoding.Error as T
import qualified Data.Text.Lazy as Tl
import qualified Data.Text.Lazy.Encoding as Tl

import Distribution.Package
import Distribution.PackageDescription.Parse
import Distribution.Text (display)

import qualified Data.ByteString.Lazy as Bl
import qualified Database.LevelDB as LevelDB

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
  :: LevelDB.DB
  -> ()
  -> Entry
  -> ResourceT IO ()
loadPackageDescriptions db !agg e
  | ".cabal" <- takeExtension (entryPath e)
  , NormalFile lbs _fs <- entryContent e
  , ParseOk _ gpd <- parsePackageDescription (Tl.unpack (Tl.decodeUtf8With T.ignore lbs)) = do
      liftIO $ do
        putChar '.'
        hFlush stdout
      let key = T.encodeUtf8 . T.pack . display $ packageId gpd
          value = Bl.toStrict lbs
      LevelDB.put db LevelDB.defaultWriteOptions{LevelDB.sync = False} key value

  | otherwise = liftIO $ do
      putChar 'x'
      hFlush stdout
      return agg

main :: IO ()
main = runResourceT $ do
  db <- LevelDB.open "/tmp/hackagedb" LevelDB.defaultOptions{LevelDB.createIfMissing = True}
  entries <- liftIO $ Tar.read <$> (Bl.readFile =<< packageTarball)
  _ <- foldEntriesM (loadPackageDescriptions db) () entries
  return ()
