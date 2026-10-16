{- | Tests of the syntax of "Data.CFTA.Gen.Synthesis" and
"Data.CFTA.Gen.Synthesis.Liquid" on the data of
"Data.CFTA.Gen.Synthesis.HooglePlus" and "Data.CFTA.Gen.Synthesis.HegelBenchmarks".
-}
module Data.CFTA.Gen.SynthesisSpec (spec) where

import Control.Exception (evaluate)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Gen.Synthesis
import Data.CFTA.Gen.Synthesis.HegelBenchmarks
import Data.CFTA.Gen.Synthesis.HooglePlus
import Data.CFTA.Gen.Synthesis.Liquid (LiquidQuery (..), baseOf, componentRoles, parseRType, renderRType)

spec :: Spec
spec = describe "Data.CFTA.Gen.Synthesis" $ do
    saturatedSpec
    it "parses the Hoogle+ data, and the printers give each type and program back" $ do
        let benchmarks = hooglePlusBenchmarks <> stackOverflowBenchmarks
            types =
                map snd (hooglePlusComponents <> augmentedComponents)
                    <> concat [queryGoal query : map snd (queryArguments query) | query <- map benchmarkQuery benchmarks]
            programs = mapMaybe benchmarkSolution benchmarks
        [typ | typ <- types, parseType (Text.pack (renderType typ)) /= Right typ] `shouldBe` []
        [solution | solution <- programs, parseProgram (Text.pack (renderProgram solution)) /= Right solution] `shouldBe` []
    it "parses the Hegel data, and the printer gives each refinement type back" $ do
        let libraries = [listLibrary, pairLibrary, booleanLibrary, lookupLibrary, arrayLibrary, stringLibrary, functionLibrary]
            types =
                map snd (concat libraries)
                    <> concat [liquidGoal query : map snd (liquidArguments query) | query <- map liquidQuery liquidBenchmarks]
        [typ | typ <- types, parseRType (Text.pack (renderRType typ)) /= Right typ] `shouldBe` []
    it "lists the programs of a query in the same order, whatever the process built before" $ do
        -- Each run puts a prefix of its own on the names of the library and
        -- the queries, so that the run builds new edges, in the order of its
        -- queries. The prefix keeps the order of the names.
        let listing prefix name = do
                benchmark <- maybe (fail ("no query " <> name)) pure (find ((== Text.pack name) . benchmarkName) hooglePlusBenchmarks)
                let query =
                        (benchmarkQuery benchmark)
                            { queryArguments = [(prefix <> argument, typ) | (argument, typ) <- queryArguments (benchmarkQuery benchmark)]
                            }
                    programs = map (untag prefix) (solutionsOfSize (tagged prefix hooglePlus) query (benchmarkSize benchmark))
                _ <- evaluate (length (show programs))
                pure programs
            names = historyQueries
        forward <- mapM (listing (Text.pack "a:")) names
        backward <- mapM (listing (Text.pack "b:")) (reverse names)
        forward `shouldBe` reverse backward

{- | The queries of the test of the order: two small Hoogle+ queries. In the
order of the edge identities, each lists its programs in another order when
the other query comes first.
-}
historyQueries :: [String]
historyQueries = ["firstMaybe", "mapMaybes"]

-- | A library with a prefix on each name.
tagged :: Text.Text -> Library -> Library
tagged prefix lib =
    lib
        { libraryGroups = [(prefix <> name, typ, map (prefix <>) members) | (name, typ, members) <- libraryGroups lib]
        , libraryArgumentOnly = [(prefix <> name, typ) | (name, typ) <- libraryArgumentOnly lib]
        , libraryAvoid = [(map (prefix <>) heads, map (prefix <>) <$> arguments) | (heads, arguments) <- libraryAvoid lib]
        }

-- | A program without the prefix on its names.
untag :: Text.Text -> Program -> Program
untag prefix (Var name) = Var (fromMaybe name (Text.stripPrefix prefix name))
untag prefix (App function argument) = App (untag prefix function) (untag prefix argument)

-- | The saturated search space against Hectare's own space.
saturatedSpec :: Spec
saturatedSpec =
    it "lists the programs of Hectare's space in which each head takes all its parameters" $ do
        let sizes name = do
                benchmark <- maybe (fail ("no query " <> name)) pure (find ((== Text.pack name) . liquidName) liquidBenchmarks)
                let components = liquidLibrary benchmark
                    query = liquidQuery benchmark
                    goal = Query [(n, baseOf t) | (n, t) <- liquidArguments query] (baseOf (liquidGoal query))
                    roles = componentRoles components query
                    arities = Map.fromList [(n, k) | (n, k, _) <- roles, k > 0]
                    values = [n | (n, _, True) <- roles]
                    grouped = library [(n, baseOf t) | (n, t) <- components] [] []
                    -- Each component its own group, so that no expansion is needed.
                    single = Library [(n, baseOf t, [n]) | (n, t) <- components] [] [] FirstOrder
                    saturation = Saturation arities values
                    arguments = map fst (queryArguments goal)
                    saturated program = case spine program [] of
                        (n, []) -> n `elem` arguments || n `elem` values
                        (n, xs) -> Map.lookup n arities == Just (length xs) && all saturated xs
                pure
                    [ ( size
                      , Set.fromList (distinctSaturatedSolutionsOfSize saturation single goal size)
                      , Set.fromList (concatMap (filter saturated . expand grouped) (distinctSolutionsOfSize grouped goal size))
                      )
                    | size <- [1 .. 5]
                    ]
        results <- concat <$> mapM sizes ["RevApp1", "Map1"]
        [size | (size, fromSaturated, fromHectare) <- results, fromSaturated /= fromHectare] `shouldBe` []
        sum [Set.size fromSaturated | (_, fromSaturated, _) <- results] `shouldSatisfy` (> 0)
  where
    spine (App function argument) rest = spine function (argument : rest)
    spine (Var n) rest = (n, rest)
