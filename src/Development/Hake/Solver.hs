{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Development.Hake.Solver where

import Control.Monad.Trans
import Control.Monad.State.Strict as State
import qualified Data.List as List
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Monoid
import Distribution.Package (Dependency(..), PackageIdentifier(..), PackageName(..))
import Distribution.PackageDescription (CondTree(..), Condition(..), ConfVar(..), FlagName(..), GenericPackageDescription(condLibrary))
import Distribution.Text (Text, disp)
import Distribution.Version
import Text.PrettyPrint hiding ((<>), ($$))
import Z3.Monad (AST, Z3, Z3Env)
import qualified Z3.Monad as Z3

import Debug.Trace (trace)

renderOneLine :: Text a => a -> String
renderOneLine = renderStyle style{mode=OneLineMode} . disp

renderConfVar :: ConfVar -> String
renderConfVar (OS x) = "os##" ++ renderOneLine x
renderConfVar (Arch x) = "arch##" ++ renderOneLine x
renderConfVar (Flag (FlagName x)) = "flag##" ++ x
renderConfVar (Impl x _) = "impl##" ++ renderOneLine x -- ++ y

newtype OrderedConfVar = OrderedConfVar ConfVar deriving Eq

instance Ord OrderedConfVar where
  l `compare` r | l == r = EQ
  OrderedConfVar l `compare` OrderedConfVar r = case (l, r) of
    (OS     x, OS     y) -> compare x y
    (OS     _,        _) -> LT
    (Arch   x, Arch   y) -> compare x y
    (Arch   _,        _) -> LT
    (Flag   x, Flag   y) -> compare x y
    (Flag   _,        _) -> LT
    (Impl x _, Impl y _) -> compare x y
    (Impl _ _,        _) -> LT

-- | Convert a Cabal condition tree into a Z3 expression
condL :: Z3.MonadZ3 m => Condition AST -> m AST
condL (Var c)     = return c
condL (Lit True)  = Z3.mkTrue
condL (Lit False) = Z3.mkFalse
condL (CNot c)    = Z3.mkNot =<< condL c
condL (COr x y)   = Z3.mkOr =<< traverse condL [x, y]
condL (CAnd x y)  = Z3.mkAnd =<< traverse condL [x, y]

newtype TraversableCondition a = TraversableCondition {unTC :: Condition a}

instance Functor TraversableCondition where
  f `fmap` TraversableCondition a = TraversableCondition (g a) where
    g (Var c) = Var (f c)
    g (Lit c) = Lit c
    g (CNot c) = CNot (g c)
    g (COr c d) = COr (g c) (g d)
    g (CAnd c d) = CAnd (g c) (g d)

instance Foldable TraversableCondition where
  f `foldMap` TraversableCondition a = g a where
    g (Var c) = f c
    g (Lit _) = mempty
    g (CNot c) = g c
    g (COr c d) = g c <> g d
    g (CAnd c d) = g c <> g d

instance Traversable TraversableCondition where
  f `traverse` TraversableCondition a = TraversableCondition <$> g a where
    g (Var c) = Var <$> f c
    g (Lit c) = pure $ Lit c
    g (CNot c) = CNot <$> g c
    g (COr c d) = COr <$> g c <*> g d
    g (CAnd c d) = CAnd <$> g c <*> g d

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
  , "concurrent" -- legacy package
  , "applicative" -- legacy package
  ]

type PackageVersionMap a = Map PackageName (Map Version a)

splitPackageIdentifiers :: Map PackageIdentifier a -> PackageVersionMap a
splitPackageIdentifiers = Map.fromListWith Map.union . fmap step . Map.toList where
  step (k, v) = (pkgName k, Map.singleton (pkgVersion k) v)

packageVersionMapLookup :: PackageIdentifier -> PackageVersionMap a -> Maybe a
packageVersionMapLookup package packages = do
  versions <- Map.lookup (pkgName package) packages
  Map.lookup (pkgVersion package) versions

packageVersionMapInsert :: PackageIdentifier -> a -> PackageVersionMap a -> PackageVersionMap a
packageVersionMapInsert k = Map.insertWith mappend (pkgName k) . Map.singleton (pkgVersion k)

data HakeSolverState = HakeSolverState
  { hakeSolverGenDesc :: !(PackageVersionMap GenericPackageDescription)
  , hakeSolverVars    :: !(Map OrderedConfVar Z3.AST)
  , hakeSolverPkgs    :: !(Map PackageIdentifier Z3.AST)
  }

newtype HakeSolverT m a = HakeSolverT {runHakeSolverT :: StateT HakeSolverState m a}
  deriving (Applicative, Functor, Monad, MonadIO, MonadTrans, MonadState HakeSolverState)

instance Z3.MonadZ3 m => Z3.MonadZ3 (HakeSolverT m) where
  getSolver = lift Z3.getSolver
  getContext = lift Z3.getContext

evalHakeSolverT
  :: HakeSolverState
  -> Z3Env
  -> HakeSolverT Z3 a
  -> IO (a, HakeSolverState)
evalHakeSolverT st env app = do
  let script = runStateT (runHakeSolverT app) st
  Z3.evalZ3WithEnv (Z3.local script) env

getConfVar :: PackageName -> ConfVar -> HakeSolverT Z3 AST
getConfVar pkg k = do
  let k' = OrderedConfVar k
      prefix | Flag _ <- k = renderOneLine pkg ++ "/"
             | otherwise   = "##global/"
  st@HakeSolverState{hakeSolverVars} <- get
  case Map.lookup k' hakeSolverVars of
    Just v -> return v
    Nothing -> do
      v <- Z3.mkFreshBoolVar $ prefix ++ renderConfVar k
      put st{hakeSolverVars = Map.insert k' v hakeSolverVars}
      return v

getCondTree :: PackageName -> CondTree ConfVar [Dependency] a -> HakeSolverT Z3 AST
getCondTree pkg CondNode{condTreeConstraints, condTreeComponents} = do
  deps <- Z3.mkAnd =<< traverse getDependency condTreeConstraints
  components <- forM condTreeComponents $ \ (cond, child, _mchild) -> do
    condVar  <- condL . unTC =<< traverse (getConfVar pkg) (TraversableCondition cond)
    childVar <- getCondTree pkg child
    Z3.mkAnd [condVar, childVar]

  if List.null components
    then return deps
    else do
      c <- Z3.mkOr components
      Z3.mkAnd [deps, c]

getDependency :: Dependency -> HakeSolverT Z3 AST
getDependency (Dependency name verRange)
  | name `elem` builtinPackages = Z3.mkTrue
  | otherwise = do
      pkgs <- gets hakeSolverGenDesc
      case Map.lookup name pkgs of
        Just vers -> do
          let ixs, oxs :: [Version]
              (ixs, oxs) = List.partition (`withinRange` verRange) (Map.keys vers)

          let somePackage :: [Version] -> HakeSolverT Z3 AST
              somePackage xs = do
                let packages = PackageIdentifier name <$> xs
                Z3.mkOr =<< traverse getPackage packages

          -- select at least one package in version range. this will be limited to
          -- one distinct version by an implies assertion in the same scope
          ixs' <- somePackage ixs

          -- avoid all packages out of range
          oxs' <- Z3.mkNot =<< somePackage oxs

          -- and the combined rule
          Z3.mkAnd [ixs', oxs']

        Nothing -> do
          liftIO . putStrLn $ "missing: " ++ show name
          -- TODO: replace with Z3.mkFalse when the entire package database is loaded
          Z3.mkTrue

getPackage :: PackageIdentifier -> HakeSolverT Z3 AST
getPackage pkgId
  -- packages installed with GHC don't have .cabal files in hackage
  -- eventually these should have their cabal files added in so this
  -- special case could be removed
  | pkgName pkgId `elem` builtinPackages = Z3.mkTrue
  | otherwise = do
      mcachedVar <- Map.lookup pkgId <$> gets hakeSolverPkgs
      mgdesc <- packageVersionMapLookup pkgId <$> gets hakeSolverGenDesc
      case (mcachedVar, mgdesc) of
        (Just cachedVar, _) -> return cachedVar
        (Nothing, Nothing) -> trace "wtf2" $ Z3.mkFalse
        (_, Just gdesc)
          | Just condNode <- condLibrary gdesc -> do
              self <- Z3.mkFreshBoolVar $ renderOneLine pkgId
              -- getCondTree may make recursive calls into getPackage. I'm not sure if Cabal internally supports
              -- bidirectional dependencies (parent <=> child) so it may be better to insert a Z3.false constant instead.
              State.modify $ \ s@HakeSolverState{hakeSolverPkgs = pkgs} -> s{hakeSolverPkgs = Map.insert pkgId self pkgs}
              deps <- getCondTree (pkgName pkgId) condNode
              self' <- Z3.mkAnd [self, deps]
              -- other packages should infer our dependencies, make them known
              State.modify $ \ s@HakeSolverState{hakeSolverPkgs = pkgs} -> s{hakeSolverPkgs = Map.insert pkgId self' pkgs}
              return $! self'

          -- pretend we can always build executables (like cpphs) for now
          | otherwise -> Z3.mkTrue


getDistinctVersion :: Dependency -> HakeSolverT Z3 AST
getDistinctVersion (Dependency pkgName _) = do
  pkgs <- splitPackageIdentifiers <$> gets hakeSolverPkgs
  case Map.lookup pkgName pkgs of
    -- the (or (distinct x y) true) assertion is useful for global assertions
    -- to validate that one of two cases will occur:
    -- 1) only a single version of the package is selected, regardless of constraints
    -- 2) no version of the package is selected
    Just k  -> do
      t <- Z3.mkTrue
      e <- Z3.mkDistinct $ Map.elems k
      Z3.mkOr [e, t]
    Nothing -> trace ("assertDistinctVersion couldn't find: " ++ show pkgName) $ Z3.mkFalse

getLatestVersion :: PackageName -> HakeSolverT Z3 (Z3.Result, Maybe PackageIdentifier)
getLatestVersion pkgName = do
  pkgs <- gets hakeSolverGenDesc
  case Map.lookup pkgName pkgs of
    Nothing -> trace "whut" $ return (Z3.Unsat, Nothing)
    Just ve ->
      let step [] = return (Z3.Unsat, Nothing)
          step (pkgVer:ys) = do
            let pkgId = PackageIdentifier pkgName pkgVer
            pkgVar <- getPackage pkgId
            res <- Z3.local $ do
              Z3.assert pkgVar
{-
              liftIO . putStrLn =<< showContext
              x <- showModel
              case x of
                Sat x' -> liftIO $ putStrLn x'
                Unsat  -> liftIO $ putStrLn "Unsat"
                Undef  -> liftIO $ putStrLn "Undef"
-}
              Z3.check

            case res of
              Z3.Sat -> return (Z3.Sat, Just pkgId)
              _      -> step ys

      in step . List.reverse $ Map.keys ve

-- getLatestVersion :: Map x -> HakeSolverT Z3 (Z3.Result PackageIdentifier)
getLatestVersion' :: PackageName -> Map Version a -> HakeSolverT Z3 (Z3.Result, Maybe PackageIdentifier)
getLatestVersion' pkgName =
      let step [] = return (Z3.Unsat, Nothing)
          step (pkgVer:ys) = do
            let pkgId = PackageIdentifier pkgName pkgVer
            pkgVar <- getPackage pkgId
            res <- Z3.local $ do
              Z3.assert pkgVar
{-
              liftIO . putStrLn =<< showContext
              x <- showModel
              case x of
                Sat x' -> liftIO $ putStrLn x'
                Unsat  -> liftIO $ putStrLn "Unsat"
                Undef  -> liftIO $ putStrLn "Undef"
-}
              Z3.check

            case res of
              Z3.Sat -> return (Z3.Sat, Just pkgId)
              _      -> step ys

      in step . List.reverse . Map.keys
