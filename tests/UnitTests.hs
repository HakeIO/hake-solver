{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main (main) where

import Control.Arrow ((&&&))
import Control.Monad (filterM, join)
import Control.Monad.State.Lazy (get)
import Data.List (nub, sort)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Map.Lazy as Map
import Z3.Monad as Z3 hiding (Version)

import Distribution.Compiler (CompilerId(..), CompilerFlavor(..))
import Distribution.Types.PackageId (PackageIdentifier(..))
import Distribution.Types.PackageName (PackageName, mkPackageName, unPackageName)
import Distribution.Types.GenericPackageDescription (GenericPackageDescription(..))
import Distribution.Types.ConfVar (ConfVar(..))
import Distribution.Types.PackageDescription (emptyPackageDescription)
import qualified Distribution.Types.PackageDescription as PD
import Distribution.Types.Flag (PackageFlag(..), FlagName, mkFlagName)
import Distribution.Types.Library (emptyLibrary)
import Distribution.Types.Dependency (Dependency, mkDependency)
import Distribution.Types.CondTree (CondTree(..), CondBranch(..))
import Distribution.Types.Condition (Condition(..))
import Distribution.Types.LibraryName (defaultLibName)
import Distribution.System (Platform(..), Arch(..), OS(..))
import Distribution.Types.Version (Version, mkVersion, versionNumbers)
import Distribution.Types.VersionRange (VersionRange, anyVersion, thisVersion, intersectVersionRanges, orLaterVersion, earlierVersion)
import qualified Distribution.Compat.NonEmptySet as NES

import Test.Tasty
import Test.Tasty.HUnit

import Development.Hake.Solver
import Development.Hake.TraversableCondition

-- | Tests inspired by the unit tests for cabal-install's solver
main :: IO ()
main = defaultMain $ testGroup "group"
       [ testCase "test 1" $ test ["p1"] testPackages $ Just [PI "p1" 1, PI "p2" 2, PI "p5" 1, PI "p6" 2]
       , testCase "test 2" $ test ["p5"] testPackages $ Just [PI "p5" 1, PI "p6" 2]
       , testCase "test 3" $ test ["p6"] testPackages $ Just [PI "p6" 2]
       -- , testCase "test 4" $ test ["p4"] testPackages $ Just [PI "p4" 1, PI "p8" 2]
       -- , testCase "test 5" $ test ["p7"] testPackages $ Nothing
       ]

testPackages :: [TestPackage]
testPackages =
  [ Pkg "p1" 1 [Exact "p2" 2]
  , Pkg "p2" 1 [Exact "p3" 2]
  , Pkg "p2" 2 [Any "p5"]
  , Pkg "p3" 2 []
  , Pkg "p3" 1 []
  , Pkg "p4" 1 [Cond (CAnd (Var "flag1") (Var "flag2")) [Exact "p6" 3] [Any "p8"]]
  , Pkg "p5" 1 [Any "p6"]
  , Pkg "p6" 1 []
  , Pkg "p6" 2 []
  , Pkg "p7" 1 [Exact "p8" 1, Exact "p8" 2]
  , Pkg "p8" 1 []
  , Pkg "p8" 2 []
  ]

type TestVersion = Int
type TestPackageName = String
type TestFlagName = String

data TestPackageIdentifier = PI TestPackageName TestVersion
  deriving (Eq, Ord, Show)

data TestPackage = Pkg TestPackageName TestVersion [Dep]
  deriving Show

data Dep = Any TestPackageName
         | Exact TestPackageName TestVersion
         | Range TestPackageName TestVersion TestVersion
         | Cond (Condition TestFlagName) [Dep] [Dep]
  deriving Show

test :: [TestPackageName]
     -> [TestPackage]
     -> Maybe [TestPackageIdentifier]
     -> Assertion
test targets available expected = do
  mInstallPlan <- solve targets available
  getPkgIdentifiers <$> mInstallPlan @?= expected

getPkgIdentifiers :: InstallPlan -> [TestPackageIdentifier]
getPkgIdentifiers installPlan =
  sort $ map getPI $ Set.toList $ installPlanPackages installPlan where
  getPI (PackageIdentifier pn v) = 
    case versionNumbers v of
      (n:_) -> PI (unPackageName pn) n
      [] -> PI (unPackageName pn) 0

solve :: [TestPackageName] -> [TestPackage] -> IO (Maybe InstallPlan)
solve targets available = do
  env <- Z3.newEnv Nothing stdOpts
  (x, _) <- runHakeSolverT st env $ do
        _ <- getInstallationPlan
               (Platform X86_64 Linux)
               (CompilerId GHC $ simpleVersion 7)
               Set.empty
               Map.empty
               targetMap
        getResults
  case x of
    (Sat, Just installPlan) -> return $ Just installPlan
    _ -> return Nothing
  where
    pkgs = splitPackageIdentifiers $ Map.fromList $
           map (getPackageIdentifier &&& genPkgDesc) available

    st = defaultSolverState { hakeSolverGenDesc = pkgs }

    targetMap = Map.fromList
                [(mkDep (mkPackageName pn) anyVersion, libComp) | pn <- targets]

    libComp = Set.singleton $ EveryComponent Development.Hake.Solver.Library

mkDep :: PackageName -> VersionRange -> Dependency
mkDep name vr = mkDependency name vr (NES.singleton defaultLibName)

data InstallPlan = InstallPlan
  { installPlanPackages :: Set.Set PackageIdentifier
  , _installPlanFlags :: Map.Map (PackageIdentifier, FlagName) Bool
  } deriving Show

getResults :: HakeSolverT Z3 (Result, Maybe InstallPlan)
getResults = do
  HakeSolverState{hakeSolverPkgs, hakeSolverPackageIdFlag} <- get
  (res, installPlan) <- Z3.withModel $ \model -> do
    pkgToResult <- mapM (Z3.evalBool model . packageIdentifierVar) hakeSolverPkgs
    let pkgs = Set.fromList . map fst <$> filterM snd (Map.toList pkgToResult)
    flags <- traverse (Z3.evalBool model) hakeSolverPackageIdFlag
    return $ InstallPlan <$> pkgs <*> sequence flags
  return (res, join installPlan)

genPkgDesc :: TestPackage -> GenericPackageDescription
genPkgDesc pkg@(Pkg _ _ deps) =
  GenericPackageDescription {
      packageDescription =
        emptyPackageDescription {
          PD.package = getPackageIdentifier pkg
        , PD.library = Just emptyLibrary
        }
    , gpdScannedVersion = Nothing
    , genPackageFlags = flags
    , condLibrary = Just $ toLibrary deps
    , condSubLibraries = []
    , condForeignLibs = []
    , condExecutables = []
    , condTestSuites = []
    , condBenchmarks = []
    } where
  flags = nub $ map (\fn -> MkPackageFlag (mkFlagName fn) "" True False) $
          concatMap getFlags deps

  getFlags (Cond c ds1 ds2) =
      (:[]) `foldMap` TraversableCondition c
   ++ concatMap getFlags ds1
   ++ concatMap getFlags ds2
  getFlags _ = []

  toLibrary ds = CondNode emptyLibrary (mapMaybe directDep ds)
                                       (mapMaybe components ds) where
    directDep (Any pn) = Just $ mkDep (mkPackageName pn) anyVersion
    directDep (Exact pn v) =
        Just $ mkDep (mkPackageName pn) $ thisVersion $ simpleVersion v
    directDep (Range pn v1 v2) =
        Just $ mkDep (mkPackageName pn) $
        intersectVersionRanges (orLaterVersion $ simpleVersion v1)
                               (earlierVersion $ simpleVersion v2)
    directDep Cond{} = Nothing

    components (Cond cond ds1 ds2) =
        Just $ CondBranch
                 (unTC $ (PackageFlag . mkFlagName) `fmap` TraversableCondition cond)
                 (toLibrary ds1)
                 (Just $ toLibrary ds2)
    components _ = Nothing

simpleVersion :: Int -> Version
simpleVersion v = mkVersion [v]

getPackageIdentifier :: TestPackage -> PackageIdentifier
getPackageIdentifier (Pkg pn v _) =
  PackageIdentifier (mkPackageName pn) (simpleVersion v)
