{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

module Development.Hake.Solver where

import Control.Monad.Trans
import Control.Monad.State.Strict as State
import Data.Foldable (for_, traverse_)
import qualified Data.List as List
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Monoid
import Data.Set (Set)
import Data.Traversable
import Distribution.Compiler (CompilerId(..))
import Distribution.Package (Dependency(..), PackageIdentifier(..), PackageName(..))
import Distribution.PackageDescription
import Distribution.System
import Distribution.Text (Text, disp)
import Distribution.Version
import Text.PrettyPrint hiding ((<>), ($$))
import Z3.Monad (AST, Z3, Z3Env)
import qualified Z3.Monad as Z3

import Development.Hake.OrderedConfVar
import Development.Hake.TraversableCondition

import Debug.Trace (trace)

renderOneLine :: Text a => a -> String
renderOneLine = renderStyle style{mode=OneLineMode} . disp

renderConfVar :: ConfVar -> String
renderConfVar (OS x) = "os##" ++ renderOneLine x
renderConfVar (Arch x) = "arch##" ++ renderOneLine x
renderConfVar (Flag (FlagName x)) = "flag##" ++ x
renderConfVar (Impl x _) = "impl##" ++ renderOneLine x -- ++ y

-- | Convert a Cabal condition tree into a Z3 expression
condL :: Z3.MonadZ3 m => Condition AST -> m AST
condL (Var c)     = return c
condL (Lit True)  = Z3.mkTrue
condL (Lit False) = Z3.mkFalse
condL (CNot c)    = Z3.mkNot =<< condL c
condL (COr x y)   = Z3.mkOr =<< traverse condL [x, y]
condL (CAnd x y)  = Z3.mkAnd =<< traverse condL [x, y]

builtinPackages :: [PackageName]
builtinPackages = map PackageName
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

splitPackageIdentifiers
  :: Map PackageIdentifier a
  -> PackageVersionMap a
splitPackageIdentifiers = Map.fromListWith Map.union . fmap step . Map.toList where
  step (k, v) = (pkgName k, Map.singleton (pkgVersion k) v)

packageVersionMapLookup
  :: PackageIdentifier
  -> PackageVersionMap a
  -> Maybe a
packageVersionMapLookup package packages = do
  versions <- Map.lookup (pkgName package) packages
  Map.lookup (pkgVersion package) versions

packageVersionMapInsert
  :: PackageIdentifier
  -> a
  -> PackageVersionMap a
  -> PackageVersionMap a
packageVersionMapInsert k = Map.insertWith mappend (pkgName k) . Map.singleton (pkgVersion k)

data HakeSolverState = HakeSolverState
  { hakeSolverGenDesc :: !(PackageVersionMap GenericPackageDescription)
  , hakeSolverVars    :: !(Map OrderedConfVar AST)
  , hakeSolverPkgs    :: !(Map PackageIdentifier AST)
  }

defaultSolverState :: HakeSolverState
defaultSolverState =
  HakeSolverState
    { hakeSolverGenDesc = Map.empty
    , hakeSolverVars    = Map.empty
    , hakeSolverPkgs    = Map.empty
    }

newtype HakeSolverT m a = HakeSolverT {unHakeSolverT :: StateT HakeSolverState m a}
  deriving (Applicative, Functor, Monad, MonadIO, MonadTrans, MonadState HakeSolverState)

instance Z3.MonadZ3 m => Z3.MonadZ3 (HakeSolverT m) where
  getSolver = lift Z3.getSolver
  getContext = lift Z3.getContext

runHakeSolverT
  :: HakeSolverState
  -> Z3Env
  -> HakeSolverT Z3 a
  -> IO (a, HakeSolverState)
runHakeSolverT st env app = do
  let script = runStateT (unHakeSolverT app) st
  Z3.evalZ3WithEnv script env

execHakeSolverT
  :: HakeSolverState
  -> Z3Env
  -> HakeSolverT Z3 a
  -> IO HakeSolverState
execHakeSolverT st env app = do
  let script = execStateT (unHakeSolverT app) st
  Z3.evalZ3WithEnv script env

runLocalHakeSolverT
  :: HakeSolverState
  -> Z3Env
  -> HakeSolverT Z3 a
  -> IO (a, HakeSolverState)
runLocalHakeSolverT st env app = do
  let script = runStateT (unHakeSolverT app) st
  Z3.evalZ3WithEnv (Z3.local script) env

execLocalHakeSolverT
  :: HakeSolverState
  -> Z3Env
  -> HakeSolverT Z3 a
  -> IO HakeSolverState
execLocalHakeSolverT st env app = do
  let script = execStateT (unHakeSolverT app) st
  Z3.evalZ3WithEnv (Z3.local script) env

getConfVar
  :: PackageName
  -> ConfVar
  -> HakeSolverT Z3 AST
getConfVar pkg k = do
  let (prefix, k')
        | Flag _ <- k = (renderOneLine pkg ++ "/", OrderedConfVar (Just pkg) k)
        | otherwise   = ("##global/", OrderedConfVar Nothing k)
  st@HakeSolverState{hakeSolverVars} <- get
  case Map.lookup k' hakeSolverVars of
    Just v -> return v
    Nothing -> do
      v <- Z3.mkFreshBoolVar $ prefix ++ renderConfVar k
      put st{hakeSolverVars = Map.insert k' v hakeSolverVars}
      return v

-- |
-- Convert a constrained Cabal configuration tree into a Z3 AST
getCondTree
  :: PackageName
  -> CondTree ConfVar [Dependency] a
  -> HakeSolverT Z3 (Maybe AST)
getCondTree pkg CondNode{condTreeConstraints, condTreeComponents} = do
  constraints <- traverse getDependency condTreeConstraints
  components <- for condTreeComponents $ \ (cond, child, _mchild) -> do
    condVar <- condL . unTC =<< traverse (getConfVar pkg) (TraversableCondition cond)
    mchildVar <- getCondTree pkg child
    case mchildVar of
      Just childVar -> Z3.mkAnd [condVar, childVar]
      Nothing -> return condVar
  case constraints <> components of
    [] -> return Nothing
    xs -> Just <$> combineWith Z3.mkAnd xs

combineWith
  :: Applicative f
  => ([a] -> f a)
  -> [a]
  -> f a
combineWith _ [x] = pure x
combineWith f xs = f xs

-- |
-- Generate an `or` constraint that covers all versions of a package that
-- meet the given range constraint. This does not require the solution
-- to be distinct, that will be addressed elsewere.
getDependency
  :: Dependency
  -> HakeSolverT Z3 AST
getDependency (Dependency name verRange)
  | name `elem` builtinPackages = Z3.mkTrue
  | otherwise = do
      pkgs <- gets hakeSolverGenDesc
      case Map.lookup name pkgs of
        Just vers -> do
          -- select at least one package in version range. this will be limited to
          -- one distinct version by other assertion in the same scope
          let somePackage :: [Version] -> HakeSolverT Z3 AST
              somePackage xs = do
                let packages = PackageIdentifier name <$> xs
                combineWith Z3.mkOr =<< traverse getPackage packages

          case List.filter (`withinRange` verRange) (Map.keys vers) of
            [] -> Z3.mkFalse -- no versions within range
            xs -> somePackage xs

        Nothing -> do
          liftIO . putStrLn $ "missing package: " ++ show name
          Z3.mkFalse

getDependencyNodes
  :: Dependency
  -> HakeSolverT Z3 [(PackageIdentifier, AST)]
getDependencyNodes (Dependency name verRange)
  | name `elem` builtinPackages = return []
  | otherwise = do
      pkgs <- gets hakeSolverGenDesc
      case Map.lookup name pkgs of
        Just vers -> do
          let somePackage :: [Version] -> HakeSolverT Z3 [(PackageIdentifier, AST)]
              somePackage xs = do
                let packages = PackageIdentifier name <$> xs
                traverse (\ x -> (x,) <$> getPackage x) packages

          somePackage $ List.filter (`withinRange` verRange) (Map.keys vers)

        Nothing -> do
          liftIO . putStrLn $ "missing package: " ++ show name
          return []

getPackage
  :: PackageIdentifier
  -> HakeSolverT Z3 AST
getPackage pkgId
  | pkgName pkgId `elem` builtinPackages =
      -- packages installed with GHC don't have .cabal files in hackage
      -- eventually these should have their cabal files added in so this
      -- special case could be removed
      Z3.mkTrue

  | otherwise = do
      mcachedVar <- Map.lookup pkgId <$> gets hakeSolverPkgs
      mgdesc <- packageVersionMapLookup pkgId <$> gets hakeSolverGenDesc
      case (mcachedVar, mgdesc) of
        (Just cachedVar, _) -> return cachedVar
        (Nothing, Nothing) -> trace "wtf2" Z3.mkFalse
        (_, Just gdesc)
          | Just condNode <- condLibrary gdesc -> do
              self <- Z3.mkFreshBoolVar $ renderOneLine pkgId
              -- getCondTree may make recursive calls into getPackage. I'm not sure if Cabal internally supports
              -- bidirectional dependencies (parent <=> child) so it may be better to insert a Z3.false constant instead.
              State.modify $ \ s@HakeSolverState{hakeSolverPkgs = pkgs} -> s{hakeSolverPkgs = Map.insert pkgId self pkgs}
              mdeps <- getCondTree (pkgName pkgId) condNode
              traverse_ (Z3.assert <=< Z3.mkImplies self) mdeps
              return self

          -- pretend we can always build executables (like cpphs) for now
          | otherwise -> Z3.mkTrue

getDistinctVersion
  :: Dependency
  -> HakeSolverT Z3 AST
getDistinctVersion (Dependency pkgName _) = do
  pkgs <- splitPackageIdentifiers <$> gets hakeSolverPkgs
  case Map.lookup pkgName pkgs of
    Just k ->
     case Map.elems k of
       [] -> fail "cannot make an empty set distinct?"
       [x] -> return x
       xs -> do
         zero <- Z3.mkInteger 0
         one <- Z3.mkInteger 1
         let distinct l = Z3.mkIte l one zero
         assigned <- Z3.mkAdd =<< traverse distinct xs
         Z3.mkEq assigned one
    Nothing -> trace ("assertDistinctVersion couldn't find: " ++ show pkgName) Z3.mkFalse

getLatestVersion
  :: PackageName
  -> HakeSolverT Z3 (Maybe (PackageIdentifier, AST))
getLatestVersion pkgName = do
  pkgs <- gets hakeSolverGenDesc
  case Map.lookup pkgName pkgs of
    Nothing -> trace "whut" $ return Nothing
    Just ve ->
      let step [] = return Nothing
          step (pkgVer:ys) = do
            let pkgId = PackageIdentifier pkgName pkgVer
            pkgVar <- getPackage pkgId
            res <- Z3.local $ do
              Z3.assert pkgVar
              Z3.check

            case res of
              Z3.Sat -> return $ Just (pkgId, pkgVar)
              _      -> step ys

      -- keys are normally are returned in ascending order
      -- but we want them in descending...
      in step $ Map.foldlWithKey (\ xs k _ -> k:xs) [] ve

data ComponentType
  = Library
  | Executable
  | TestSuite
  | Benchmark

data Component
  = SpecificComponent ComponentType String
  | EveryComponent ComponentType

data InstallationPlan = InstallationPlan
  { packageFlagAssignments :: Map PackageName FlagAssignment
  , packageComponents      :: Map PackageName (Set Component)
  }

-- |
assertGlobalFlags
  :: Platform -- ^ Target Platform
  -> CompilerId -- ^ Target Compiler
  -> HakeSolverT Z3 ()
assertGlobalFlags (Platform arch os) (CompilerId compilerFlavor compilerVersion) = do
  let globalPackage = PackageName "##global"
  osFlag <- getConfVar globalPackage $ OS os
  Z3.assert osFlag

  archFlag <- getConfVar globalPackage $ Arch arch
  Z3.assert archFlag

  compilerFlag <- getConfVar globalPackage . Impl compilerFlavor $ thisVersion compilerVersion
  Z3.assert compilerFlag

-- |
assertAssignedFlags
  :: Map PackageName FlagAssignment
  -> HakeSolverT Z3 ()
assertAssignedFlags flagAssignments =
  for_ (Map.toList flagAssignments) $ \ (package, assignments) ->
    for_ assignments $ \ (flag, assignment) -> do
      var <- getConfVar package (Flag flag)
      if assignment
        then Z3.assert var
        else Z3.assert =<< Z3.mkNot var

getInstallationPlan
  :: Platform -- ^ Target Platform
  -> CompilerId -- ^ Target Compiler
  -> Set PackageIdentifier -- ^ Currently installed packages
  -> Map PackageName FlagAssignment -- ^ Hard assignment for flags, covers both installed and uninstalled packages
  -> Map Dependency (Set Component) -- ^ Packages to install
  -> [PackageName] -- ^ Priority order
  -> HakeSolverT Z3 InstallationPlan
getInstallationPlan platform compiler installedPackages flagAssignments desiredPackages packagePriorities = do
  -- pin down the platform and compiler
  assertGlobalFlags platform compiler

  -- and any user specified flag assignments
  assertAssignedFlags flagAssignments

  -- select a single version for each package, in priority order
  -- note: this should run in better than O(n*m) time because
  -- we're folding over the partially solved constraint set
  for_ packagePriorities $ \ packagePriority -> do
    Just (_, pkgVar) <- getLatestVersion packagePriority
    Z3.assert pkgVar

  -- once the versions have been selected we need to choose a flag
  -- assignment for any unbound flags, with a preference to True...
  -- this logic is pretty arbitrary but it is documented in Cabal

  -- TODO: for executables, tests, benchmarks there is no requirement that
  -- the selected package versions be consistent between eachother, so we'll
  -- fu-malik to find a relaxed set of constraints (additional library versions)
  -- that allow each executable to be compiled

  return $ undefined

resolveGenericPackageDescription
  :: InstallationPlan
  -> GenericPackageDescription
  -> PackageDescription
resolveGenericPackageDescription = error "not implemented"
