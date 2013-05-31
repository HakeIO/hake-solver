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

newtype CurryConfVar = CurryConfVar ConfVar deriving Eq

instance Ord CurryConfVar where
  l `compare` r | l == r = EQ
  CurryConfVar l `compare` CurryConfVar r = case (l, r) of
    (OS     x, OS     y) -> compare x y
    (OS     _,        _) -> LT
    (Arch   x, Arch   y) -> compare x y
    (Arch   _,        _) -> LT
    (Flag   x, Flag   y) -> compare x y
    (Flag   _,        _) -> LT
    (Impl x _, Impl y _) -> compare x y
    (Impl _ _,        _) -> LT

-- useful orphans..
-- deriving instance Ord a => Ord (Condition a)
deriving instance Functor     Condition
deriving instance Foldable    Condition
deriving instance Traversable Condition

splitDependMap :: Map PackageIdentifier a -> Map PackageName (Map Version a)
splitDependMap = Map.fromListWith Map.union . fmap step . Map.toList where
  step (k, v) = (pkgName k, Map.singleton (pkgVersion k) v)

type CurryMap a = Map PackageName (Map Version a)

curryMapLookup :: PackageIdentifier -> CurryMap a -> Maybe a
curryMapLookup package packages = do
  versions <- Map.lookup (pkgName package) packages
  Map.lookup (pkgVersion package) versions

curryMapInsert :: PackageIdentifier -> a -> CurryMap a -> CurryMap a
curryMapInsert k = Map.insertWith mappend (pkgName k) . Map.singleton (pkgVersion k)

-- | Convert a Cabal condition tree into a Z3 expression
condL :: Condition (Expr Bool) -> Expr Bool
condL (Var c)    = c
condL (Lit c)    = if c then Z3.true else Z3.false
condL (CNot c)   = Z3.not_ (condL c)
condL (COr x y)  = condL x Z3.||* condL y
condL (CAnd x y) = condL x Z3.&&* condL y

renderOneLine :: Text a => a -> String
renderOneLine = renderStyle style{mode=OneLineMode} . disp

data CurrySolverState = CurrySolverState
  { currySolverGenDesc :: !(CurryMap GenericPackageDescription)
  , currySolverVars    :: !(Map CurryConfVar (Z3.Expr Bool))
  , currySolverPkgs    :: !(Map PackageIdentifier (Z3.Expr Bool))
  }

newtype CurrySolverT m a = CurrySolverT {runCurrySolverT :: StateT CurrySolverState m a}
  deriving (Applicative, Functor, Monad, MonadIO, MonadTrans, MonadState CurrySolverState)

evalCurrySolverT
  :: CurrySolverState
  -> Z3State
  -> CurrySolverT Z3 a
  -> IO (a, CurrySolverState, Z3State)
evalCurrySolverT st z3s app = do
  ((a, st'), z3s') <- runZ3 (Z3B.withContext (runStateT (runCurrySolverT app) st)) z3s
  return (a, st', z3s')

builtinPackages :: [PackageName]
builtinPackages = map PackageName $
  [ "rts"
  , "ffi"
  , "ghc"
  , "ghc-binary"
  , "ghc-prim"
  , "integer"
  , "integer-gmp"
  , "integer-simple"
  ] ++
  [ "concurrent"
  , "applicative"
  ]

getDependency :: Dependency -> CurrySolverT Z3 (Expr Bool)
getDependency (Dependency pkgName verRange)
  | pkgName `elem` builtinPackages = return Z3.true
  | otherwise = do
      pkgs <- gets currySolverGenDesc
      case Map.lookup pkgName pkgs of
        Just vers -> do
          let (ixs, oxs) = List.partition (`withinRange` verRange) (Map.keys vers)
              somePackage xs = fmap Z3.or_ . forM xs $ getPackage . PackageIdentifier pkgName

          -- select at least one package in version range. this will be limited to
          -- one distinct version by an implies assertion in the same scope
          ixs' <- somePackage ixs

          -- avoid all packages out of range
          oxs' <- Z3.not_ <$> somePackage oxs

          -- and the combined rule
          lift . Z3.let_ $ ixs' &&* oxs'

        Nothing -> do
          liftIO . putStrLn $ "missing: " ++ show pkgName
          return Z3.true -- hmmm?

renderConfVar :: ConfVar -> String
renderConfVar (OS x) = "os##" ++ renderOneLine x
renderConfVar (Arch x) = "arch##" ++ renderOneLine x
renderConfVar (Flag (FlagName x)) = "flag##" ++ x
renderConfVar (Impl x _) = "impl##" ++ renderOneLine x -- ++ y

getConfVar :: MonadIO m => PackageName -> ConfVar -> CurrySolverT Z3 (Expr Bool)
getConfVar pkg k = do
  let k' = CurryConfVar k
      prefix | Flag _ <- k = renderOneLine pkg ++ "/"
             | otherwise   = "##global/"
  st@CurrySolverState{currySolverVars} <- get
  case Map.lookup k' currySolverVars of
    Just v -> return v
    Nothing -> do
      v <- lift . Z3.namedVar $ prefix ++ renderConfVar k
      put st{currySolverVars = Map.insert k' v currySolverVars}
      return v

getCondTree :: PackageName -> CondTree ConfVar [Dependency] a -> CurrySolverT Z3 (Expr Bool)
getCondTree pkg CondNode{condTreeConstraints, condTreeComponents} = do
  deps <- Z3.and_ <$> mapM getDependency condTreeConstraints
  components <- forM condTreeComponents $ \ (cond, child, _mchild) -> do
    condVar  <- condL <$> traverse (getConfVar pkg) cond
    childVar <- getCondTree pkg child
    return $ condVar Z3.&&* childVar

  return $! if List.null components
    then deps
    else deps Z3.&&* Z3.or_ components

getPackage :: PackageIdentifier -> CurrySolverT Z3 (Expr Bool)
getPackage pkgId
  -- packages installed with GHC don't have .cabal files in hackage
  -- eventually these should have their cabal files added in so this
  -- special case could be removed
  | pkgName pkgId `elem` builtinPackages = return Z3.true
  | otherwise = do
      mcachedVar <- Map.lookup pkgId <$> gets currySolverPkgs
      mgdesc <- curryMapLookup pkgId <$> gets currySolverGenDesc
      case (mcachedVar, mgdesc) of
        (Just cachedVar, _) -> return cachedVar
        (Nothing, Nothing) -> trace "wtf2" $ return Z3.false
        (_, Just gdesc)
          | Just condNode <- condLibrary gdesc -> do
              self <- lift . Z3.namedVar $ renderOneLine pkgId
              -- getCondTree may make recursive calls into getPackage. I'm not sure if Cabal internally supports
              -- bidirectional dependencies (parent <=> child) so it may be better to insert a Z3.false constant instead.
              State.modify $ \ s@CurrySolverState{currySolverPkgs = pkgs} -> s{currySolverPkgs = Map.insert pkgId self pkgs}
              deps <- getCondTree (pkgName pkgId) condNode
              self' <- lift . Z3.let_ $ self &&* deps
              -- other packages should infer our dependencies, make them known
              State.modify $ \ s@CurrySolverState{currySolverPkgs = pkgs} -> s{currySolverPkgs = Map.insert pkgId self' pkgs}
              return $! self'

          -- pretend we can always build executables (like cpphs) for now
          | otherwise -> return Z3.true

getDistinctVersion :: Dependency -> CurrySolverT Z3 (Expr Bool)
getDistinctVersion (Dependency pkgName _) = do
  pkgs <- splitDependMap <$> gets currySolverPkgs
  case Map.lookup pkgName pkgs of
    -- the (or (distinct x y) true) assertion is useful for global assertions
    -- to validate that one of two cases will occur:
    -- 1) only a single version of the package is selected, regardless of constraints
    -- 2) no version of the package is selected
    Just k  -> lift . Z3.let_ $! Z3.distinct (Map.elems k) ||* Z3.true
    Nothing -> trace ("assertDistinctVersion couldn't find: " ++ show pkgName) $ return Z3.false

getLatestVersion :: PackageName -> CurrySolverT Z3 (Z3.Result PackageIdentifier)
getLatestVersion pkgName = do
  pkgs <- gets currySolverGenDesc
  case Map.lookup pkgName pkgs of
    Nothing -> trace "whut" $ return Unsat
    Just ve ->
      let step [] = return Unsat
          step (pkgVer:ys) = do
            let pkgId = PackageIdentifier pkgName pkgVer
            pkgVar <- getPackage pkgId
            res <- lift . Z3B.withContext $ do
              assert pkgVar
{-
              liftIO . putStrLn =<< showContext
              x <- showModel
              case x of
                Sat x' -> liftIO $ putStrLn x'
                Unsat  -> liftIO $ putStrLn "Unsat"
                Undef  -> liftIO $ putStrLn "Undef"
-}
              check

            case res of
              Sat _ -> return $! Sat pkgId
              _     -> step ys

      in step . List.reverse $ Map.keys ve

-- getLatestVersion :: Map x -> CurrySolverT Z3 (Z3.Result PackageIdentifier)
getLatestVersion' :: PackageName -> Map Version a -> CurrySolverT Z3 (Z3.Result PackageIdentifier)
getLatestVersion' pkgName =
      let step [] = return Unsat
          step (pkgVer:ys) = do
            let pkgId = PackageIdentifier pkgName pkgVer
            pkgVar <- getPackage pkgId
            res <- lift . Z3B.withContext $ do
              assert pkgVar
{-
              liftIO . putStrLn =<< showContext
              x <- showModel
              case x of
                Sat x' -> liftIO $ putStrLn x'
                Unsat  -> liftIO $ putStrLn "Unsat"
                Undef  -> liftIO $ putStrLn "Undef"
-}
              check

            case res of
              Sat _ -> return $! Sat pkgId
              _     -> step ys

      in step . List.reverse . Map.keys

parseDependencies :: [T.Text] -> [Dependency]
parseDependencies = concatMap step where
  step x = [dep | (dep, "") <- readP_to_S Dt.parse (T.unpack x)]

curryApp :: TVar CurrySolverState -> TVar Z3State -> Wai.Application
curryApp stref z3ref req
  | "GET" <- requestMethod req, ["package", pkgName] <- pathInfo req = do
      pkgs <- currySolverGenDesc <$> liftIO (readTVarIO stref)
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
          (res, st', z3s') <- evalCurrySolverT st z3s $ do
            ghcFlag <- getConfVar (PackageName "##global") (Impl GHC anyVersion)
            distVars <- Z3.and_ <$> mapM getDistinctVersion deps'
            depsVars <- Z3.and_ <$> mapM getDependency deps'
            pkgs <- gets currySolverGenDesc
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

  let gpdCurryMap = splitDependMap gpdMap
      packages    = Map.keys gpdMap
      initPackages = do
        return ()
        -- forM_ packages getPackage
        -- forM_ (Map.keys gpdCurryMap) assertDistinctVersion

  z3s <- initZ3State Z3.stdArgs

  (st, z3s') <- runZ3 (execStateT (runCurrySolverT initPackages)
          CurrySolverState
            { currySolverGenDesc = gpdCurryMap
            , currySolverVars = Map.empty
            , currySolverPkgs = Map.empty
            }) z3s

  forM_ (Map.keys (currySolverVars st)) $ \ (CurryConfVar v) -> print v

  z3ref <- newTVarIO z3s'
  stref <- newTVarIO st

  -- Warp.run 7575 $ curryApp st{currySolverGenDesc = Map.empty} z3ref
  Warp.run 7575 $ curryApp stref z3ref