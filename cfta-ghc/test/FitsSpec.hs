{-# LANGUAGE OverloadedStrings #-}

{- | The streamed walk of "Data.CFTA.GHC.Fits" end to end, on five easy
Hoogle+ queries and five queries of higher-kinded types with the Prelude:
each query gives its expected program, or a fit with its normal form, and
GHC accepts every fit as a program of the query's signature. Also: the
fits that ignore an argument are marked, the walk leaves the goal's
unification variables as it found them, and the fast rejects keep three
fits that only the solver can decide (a coercion through a newtype, a given
equality, and a quantified given). The normal forms merge the fits that
respell one program, as @flip filter xs p@ and @filter p xs@, keep the fits
that differ in meaning, and mark the fits that drop an argument. A reduction
that does not end gives no normal form.
-}
module Main (main) where

import Control.Concurrent (threadDelay)
import Control.Exception (evaluate)
import Control.Monad (forM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.Either (isLeft)
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import System.Directory (getTemporaryDirectory, removeFile)
import System.IO (hClose, hPutStr, openTempFile)
import System.Timeout (timeout)
import Test.Hspec (describe, hspec, it, shouldBe, shouldNotBe, shouldReturn, shouldSatisfy)

import Data.CFTA.GHC.Corpus (holeContext, newParser)
import Data.CFTA.GHC.Fits
import Data.CFTA.GHC.HoleFits (PluginOptions (..), readOptions)
import Data.CFTA.GHC.Internal.Check (Leaf (..), complete, newEnvironment, startWalker, step)
import Data.CFTA.GHC.Model (
    FitModel (..),
    fromTerms,
    merge,
    parseFitModel,
    printFitModel,
    symbolOf,
    tokenScore,
    tokenScoreShared,
 )
import Data.CFTA.GHC.NormalForm (Term (TApp, TLam, TVar), normalForm)
import qualified Data.CFTA.GHC.Preference as Preference
import Data.CFTA.GHC.Rank (Ranking (..), defaultRanking, rankFits, rankedFits)
import Data.CFTA.GHC.Session
import Data.CFTA.Gen.Synthesis (Program (..), parseProgram, renderProgram)
import Data.CFTA.Gen.Synthesis.Walk (preorder)
import qualified Data.CFTA.Sized.Prefix.Train as Train
import qualified Data.CFTA.Term as CFTA
import Decision (DecisionModel (..), Option (..), fixedModel)
import GHC.Builtin.Types (mkListTy)
import GHC.Core.Type (liftedTypeKind, mkTyVarTy)
import GHC.Data.Bag (emptyBag)
import GHC.Tc.Utils.TcMType (newFlexiTyVar, readMetaTyVar)
import GHC.Tc.Utils.TcType (isFlexi)

-- | A query: its name, its signature, its argument names, and the expected program.
data Query = Query String String [Text] Program

-- | Five easy Hoogle+ queries; @mergeEither@ has three component leaves.
queries :: [Query]
queries =
    [ query "map" "(a -> b) -> [a] -> [b]" ["f", "xs"] "map f xs"
    , query "firstKey" "[(a, b)] -> a" ["xs"] "fst (head xs)"
    , query "singletonList" "a -> [a]" ["x"] "(:) x []"
    , query "resolveEither" "Either a b -> (a -> b) -> b" ["e", "f"] "either f id e"
    , query "mergeEither" "Either a (Either a b) -> Either a b" ["e"] "either Left id e"
    ]
  where
    query name signature arguments expected = Query name signature arguments (either error id (parseProgram expected))

{- | Queries of higher-kinded types, which need the specializations of
@fmap@, @(>>=)@, and @pure@ at the type heads of the query, under the
signature's givens or by the instances in scope.
-}
higherKinded :: [Query]
higherKinded =
    [ query "join" "Monad m => m (m a) -> m a" ["x"] "(>>=) x id"
    , query "fmapFst" "Functor f => f (a, b) -> f a" ["x"] "fmap fst x"
    , query "joinMaybe" "Maybe (Maybe a) -> Maybe a" ["x"] "(>>=) x id"
    , query "bind" "Monad m => (a -> m b) -> m a -> m b" ["f", "x"] "(>>=) x f"
    , query "pureSingleton" "Applicative f => a -> f [a]" ["x"] "pure ((:) x [])"
    ]
  where
    query name signature arguments expected = Query name signature arguments (either error id (parseProgram expected))

main :: IO ()
main = withSession ["import Prelude", "import Data.Coerce (coerce)", "import Data.Monoid (Sum (..))"] $ \session -> do
    candidates <- candidatesOf session [Import "Prelude" Nothing]
    -- The modules of base with the other components of the laws.
    others <-
        candidatesOf
            session
            [Import name Nothing | name <- ["Data.Tuple", "Data.Function", "Data.Bool", "Data.Maybe", "Data.Either", "Data.List"]]
    coercions <- candidatesOf session [Import "Data.Coerce" Nothing]
    declare session "class Sized a where { sized :: a -> Int }; instance Sized Int where { sized = id }"
    Just sizedType <- typeOfExpression session "sized"
    let
        -- Whether one program fits a signature, by the steps of the walk.
        checks signature arguments program = do
            Just typ <- typeOfExpression session ("undefined :: " <> signature)
            let extra = coercions <> [Candidate "sized" sizedType True False Nothing]
            inSignatureHole session (candidates <> extra) typ arguments $ \hole candidates' goal -> do
                environment <- newEnvironment hole
                let leaves = Map.fromList [(candidateName c, Leaf (candidateName c) (candidateType c) (candidateHeads c)) | c <- candidates']
                    go walker [] = complete environment walker
                    go walker ((name, children) : rest) = case Map.lookup name leaves of
                        Just leaf -> step environment walker leaf children False >>= maybe (pure False) (`go` rest)
                        Nothing -> pure False
                go (startWalker environment (map candidateType candidates') goal) (preorder program)
    hspec $ do
        describe "streamFits" $
            forM_ [(False, ""), (True, ", with the domains of kind Type")] $ \(domains, label) ->
                forM_ (queries <> higherKinded) $ \(Query name signature arguments expected) ->
                    it ("finds the expected program of " <> name <> ", and GHC accepts its fits" <> label) $ do
                        Just typ <- typeOfExpression session ("undefined :: " <> signature)
                        Just normal <- inTypechecker session (normalFormsOf candidates)
                        found <- newIORef []
                        let options = defaultOptions{optionMaximumSize = size expected, optionTypeDomains = domains}
                            -- The expected program, or an earlier fit with its normal form.
                            isExpected program = program == expected || (isJust (normal expected) && normal program == normal expected)
                            record fit = do
                                liftIO (modifyIORef' found (fitProgram fit :))
                                pure (not (isExpected (fitProgram fit)))
                        statistics <- fitsForSignature session options candidates typ arguments record
                        fits <- reverse <$> readIORef found
                        fmap statisticsFits statistics `shouldBe` Just (length fits)
                        fits `shouldSatisfy` any isExpected
                        forM_ (take 10 fits) $ \fit ->
                            accepts session ("(\\" <> unwords (map Text.unpack arguments) <> " -> " <> renderProgram fit <> ") :: " <> signature)
                                `shouldReturn` True
        describe "optionTypeDomains" $ do
            it "proposes no maximum at a rigid goal without a given Ord, and keeps head" $ do
                Just typ <- typeOfExpression session "undefined :: [a] -> a"
                let proposed domains = do
                        traced <- newIORef []
                        let options =
                                defaultOptions
                                    { optionMaximumSize = 2
                                    , optionTypeDomains = domains
                                    , optionTrace = Just (\_ program -> modifyIORef' traced (program :))
                                    }
                        _ <- fitsForSignature session options candidates typ ["xs"] (\_ -> pure True)
                        readIORef traced
                without <- proposed False
                with <- proposed True
                (parse "maximum xs" `elem` without, parse "maximum xs" `elem` with, parse "head xs" `elem` with)
                    `shouldBe` (True, False, True)
            it "follows the instance contexts: no maximum of pairs with a rigid part, a maximum of nested pairs" $ do
                let proposed signature = do
                        Just typ <- typeOfExpression session ("undefined :: " <> signature)
                        traced <- newIORef []
                        let options =
                                defaultOptions
                                    { optionMaximumSize = 2
                                    , optionTypeDomains = True
                                    , optionTrace = Just (\_ program -> modifyIORef' traced (program :))
                                    }
                        _ <- fitsForSignature session options candidates typ ["xs"] (\_ -> pure True)
                        readIORef traced
                rigidPart <- proposed "[(a, Int)] -> (a, Int)"
                nested <- proposed "[((Int, Int), Int)] -> ((Int, Int), Int)"
                (parse "maximum xs" `elem` rigidPart, parse "maximum xs" `elem` nested) `shouldBe` (False, True)
        describe "fitIgnoresPart" $
            it "marks the fits that ignore an argument" $ do
                marks <- forM ignoring $ \(signature, arguments, programs) -> do
                    Just typ <- typeOfExpression session ("undefined :: " <> signature)
                    found <- newIORef []
                    let wanted = map parse programs
                        record fit = liftIO $ do
                            modifyIORef' found (fit :)
                            fits <- readIORef found
                            pure (not (all (`elem` map fitProgram fits) wanted))
                    _ <-
                        fitsForSignature
                            session
                            defaultOptions{optionMaximumSize = 4, optionNormalForms = False}
                            candidates
                            typ
                            arguments
                            record
                    fits <- readIORef found
                    pure [lookup program [(fitProgram fit, fitIgnoresPart fit) | fit <- fits] | program <- wanted]
                marks `shouldBe` [[Just True, Just False], [Just True, Just False]]
        describe "normal forms" $ do
            it "unfold each component of base with a body, one law each" $ do
                Just normal <- inTypechecker session (normalFormsOf (candidates <> others))
                let holds (left, right) = isJust (normal (parse left)) && normal (parse left) == normal (parse right)
                filter (not . holds) laws `shouldBe` []
                -- listToMaybe is foldr, which is recursive, so it does not reduce on a list.
                holds ("listToMaybe ((:) x xs)", "Just x") `shouldBe` False
            it "merge the respellings of one program, and keep the programs that differ" $ do
                Just normal <- inTypechecker session (normalFormsOf candidates)
                let same left right = isJust (normal (parse left)) && normal (parse left) == normal (parse right)
                map (uncurry same) respellings `shouldBe` map (const True) respellings
                map (uncurry same) different `shouldBe` map (const False) different
            it "skip a fit with the normal form of an earlier fit, behind an option" $ do
                Just typ <- typeOfExpression session "undefined :: (a -> Bool) -> [a] -> [a]"
                let fitsWith normalForms = do
                        found <- newIORef []
                        let record fit = True <$ liftIO (modifyIORef' found (fitProgram fit :))
                            options = defaultOptions{optionMaximumSize = 4, optionNormalForms = normalForms}
                        statistics <- fitsForSignature session options candidates typ ["p", "xs"] record
                        fits <- readIORef found
                        pure (fits, maybe 0 statisticsMerged statistics)
                (merged, skipped) <- fitsWith True
                (unmerged, _) <- fitsWith False
                merged `shouldSatisfy` elem (parse "filter p xs")
                merged `shouldSatisfy` notElem (parse "flip filter xs p")
                unmerged `shouldSatisfy` elem (parse "flip filter xs p")
                skipped `shouldSatisfy` (> 0)
                length merged + skipped `shouldBe` length unmerged
            it "mark a fit whose normal form drops an argument" $ do
                Just typ <- typeOfExpression session "undefined :: [a] -> Int -> [a]"
                found <- newIORef []
                -- const xs n is xs, by the body of const.
                let wanted = map parse ["const xs n", "take n xs"]
                    record fit = liftIO $ do
                        modifyIORef' found (fit :)
                        fits <- readIORef found
                        pure (not (all (`elem` map fitProgram fits) wanted))
                _ <- fitsForSignature session defaultOptions{optionMaximumSize = 4} candidates typ ["xs", "n"] record
                fits <- readIORef found
                [lookup program [(fitProgram fit, fitDropsArgument fit) | fit <- fits] | program <- wanted]
                    `shouldBe` [Just True, Just False]
            it "stop a reduction that does not end" $ do
                -- (\x -> x x) (\x -> x x): the term of a newtype fixpoint when the translation erases its casts.
                let selfApply = TLam (TApp (TVar 0) (TVar 0))
                    loop = TApp selfApply selfApply
                timeout 10000000 (evaluate (isNothing (normalForm (const (Just loop)) (Var "loop"))))
                    `shouldReturn` Just True
        describe "ranking" $ do
            let model = fixedModel (\option -> if optionName option == "b" then 2 else 1)
                failing = DecisionModel (const (pure (Left "no server")))
            it "orders the fits by the model's scores, keeps the order of equal scores, and reports a failure" $ do
                ranked' <- rankFits model "a hole" id ["a", "b", "c"]
                fmap (map fst) ranked' `shouldBe` Right ["b", "a", "c"]
                failed <- rankFits failing "a hole" id ["a"]
                fmap (map fst) failed `shouldBe` Left "no server"
            it "orders the pool of a search, keeps the other fits after it, and keeps the order when the model fails" $ do
                let fit ignores text = Fit (parse text) 1 ignores False
                    fits = [fit False "a", fit True "e", fit False "b", fit False "c"]
                    render = Text.pack . renderProgram . fitProgram
                    ranking = defaultRanking{rankingPool = 2}
                (ordered, problem) <- rankedFits model ranking "a hole" render fits
                (map fitProgram ordered, problem) `shouldBe` (map parse ["b", "a", "c", "e"], Nothing)
                (kept, failure) <- rankedFits failing ranking "a hole" render fits
                (map fitProgram kept, failure) `shouldBe` (map parse ["a", "b", "c", "e"], Just "no server")
                -- A model that does not answer in the ranking's time.
                let slow = DecisionModel (\question -> threadDelay 2000000 >> scoreOptions model question)
                (waited, late) <- rankedFits slow ranking{rankingSeconds = 0.05} "a hole" render fits
                (map fitProgram waited, late) `shouldBe` (map parse ["a", "b", "c", "e"], Just "no answer in 5.0e-2 s")
            it "turns the ranking of the plugin on only with the option rank" $ do
                fmap (fmap rankingPool . pluginRanking) (readOptions ["rank", "rank-pool=10"]) `shouldBe` Right (Just 10)
                fmap (fmap rankingPool . pluginRanking) (readOptions []) `shouldBe` Right Nothing
                fmap (fmap rankingPool . pluginRanking) (readOptions ["rank-pool=10"])
                    `shouldBe` Left "rank-pool needs the option rank: the ranking is on only with rank"
        describe "fit models" $ do
            let leaf symbol = CFTA.Node symbol []
                model =
                    fromTerms
                        ["Prelude"]
                        (Map.fromList [("map", 2), ("length", 1)])
                        [ ("top", CFTA.Node "length/1" [CFTA.Node "map/2" [leaf "var/0", leaf "var/0"]])
                        , ("expr", CFTA.Node "map/2" [leaf "var/0", leaf "var/0"])
                        ]
            it "prints a model and reads it back, and merges two models by adding their counts" $ do
                parseFitModel (printFitModel model) `shouldBe` Right model
                fmap (Map.lookup ("map/2", 0, "var/0") . modelContexts) (parseFitModel (printFitModel (merge model model)))
                    `shouldBe` Right (Just 4)
            it "rejects a text that is not a model, with the number of the line" $ do
                parseFitModel "fit-model 2;" `shouldSatisfy` either (const True) (const False)
                parseFitModel "fit-model 1;\ncandidate map;" `shouldBe` Left "fit-model: line 2 is not a record: candidate map;"
            it "scores a token in its context, mixed with the symbol alone, and names a non-candidate var" $ do
                -- The context top 0 has one symbol seen once (mix 1/2); length/1 has
                -- the count 1 among 7 nodes and an alphabet of 20 symbols.
                let score = tokenScore model Set.empty
                score Nothing 0 ("length", 1) `shouldSatisfy` (\value -> abs (value - log (1 / 2 + 1 / 2 * 2 / 27)) < 1e-12)
                score (Just ("length", 1)) 0 ("map 2", 2) `shouldBe` score (Just ("length", 1)) 0 ("map", 2)
                symbolOf model Set.empty ("xs", 0) `shouldBe` "var/0"
                symbolOf model (Set.fromList ["xs"]) ("xs", 0) `shouldBe` "arg/0"
            it "shares the probability of var among the module's names in proportion to their uses" $ do
                let uses = Map.fromList [("helper", 3), ("other", 0)]
                    shared = tokenScoreShared model uses ("top", 0) Set.empty Nothing 0
                    plain = tokenScore model Set.empty Nothing 0
                -- (3 + 1) / (3 + 2 + 1) for helper, (0 + 1) / 6 for other and for an unknown name.
                shared ("helper", 1) - plain ("helper", 1) `shouldSatisfy` (\value -> abs (value - log (4 / 6)) < 1e-12)
                shared ("unknown", 1) - plain ("unknown", 1) `shouldSatisfy` (\value -> abs (value - log (1 / 6)) < 1e-12)
                shared ("length", 1) `shouldBe` plain ("length", 1)
            it "finds the application around a hole, in the parsed module" $ do
                parser <- newParser session
                temporary <- getTemporaryDirectory
                (path, handle) <- openTempFile temporary "Holes.hs"
                let source =
                        [ "module Holes where"
                        , "import Data.Maybe (fromMaybe)"
                        , "firstOr d xs = fromMaybe d _"
                        , "pairs xs ys = zip xs (_)"
                        , "total xs = foldr (+) _ xs"
                        , "whole = _"
                        , "choose b x y = if _ then x else y"
                        , "twice f = map (\\x -> _) f"
                        ]
                hPutStr handle (unlines source) >> hClose handle
                let names = Set.fromList ["fromMaybe", "zip", "foldr", "(+)"]
                    at line = (line, 1 + length (takeWhile (/= '_') (source !! (line - 1))))
                    context line = holeContext parser ["Prelude", "Data.Maybe"] names path (at line)
                mapM context [3, 4, 5, 6, 7, 8]
                    `shouldReturn` [ Just ("fromMaybe/2", 1)
                                   , Just ("zip/2", 1)
                                   , Just ("foldr/3", 1)
                                   , Just ("top", 0)
                                   , Just ("if/3", 0)
                                   , Just ("lambda/1", 0)
                                   ]
                removeFile path
            it "reads the options model, model-search, and hole-context of the plugin" $ do
                fmap pluginModel (readOptions ["model=base.cfta"]) `shouldBe` Right (Just "base.cfta")
                fmap pluginRerank (readOptions ["model=base.cfta"]) `shouldBe` Right True
                fmap pluginRerank (readOptions ["model=base.cfta", "model-search=best-first"]) `shouldBe` Right False
                fmap pluginHoleContext (readOptions ["model=base.cfta", "hole-context=off"]) `shouldBe` Right False
        describe "fit preferences" $ do
            let base =
                    fromTerms
                        ["Prelude"]
                        (Map.fromList [("id", 1), ("reverse", 1)])
                        (replicate 20 ("top", CFTA.Node "id/1" [CFTA.Node "arg/0" []]))
                item =
                    Preference.PreferenceCase
                        "Example.hs"
                        ("top", 0)
                        (Set.singleton "xs")
                        (Map.fromList [("helper", 3), ("other", 1)])
                        (parse "reverse xs")
                        (map parse ["id xs", "reverse xs", "xs"])
                precision = 0.01
                fit = either fail pure . Preference.trainPreferences 200 precision base
                other = item{Preference.caseRoot = ("lambda/1", 0), Preference.casePreferred = parse "id xs"}
            it "matches corpus and plugin score accumulation" $ do
                let unchanged = Preference.fromFitModel base
                    uses = Preference.caseUses item
                    locals = Preference.caseLocals item
                forM_ [("top", 0), ("map/2", 1), ("lambda/1", 0)] $ \root ->
                    forM_ [Nothing, Just ("reverse", 1), Just ("helper", 2)] $ \parent ->
                        forM_ [0, 1] $ \position ->
                            forM_ [("id", 1), ("xs", 0), ("helper", 2), ("unknown", 0)] $ \token ->
                                Preference.tokenScoreShared unchanged uses root locals parent position token
                                    `shouldBe` tokenScoreShared base uses root locals parent position token
                let score = tokenScoreShared base uses (Preference.caseRoot item) locals
                    expected = score Nothing 0 ("reverse", 1) + score (Just ("reverse", 1)) 0 ("id", 1) + score (Just ("id", 1)) 0 ("xs", 0)
                Preference.scoreProgram unchanged item (parse "reverse (id xs)") - expected
                    `shouldSatisfy` ((< 1e-12) . abs)
                let context = item{Preference.caseLocals = Set.fromList ["xs", "ys"], Preference.caseUses = Map.empty}
                    original = tokenScoreShared base Map.empty (Preference.caseRoot context) (Preference.caseLocals context)
                    nodes = [(Nothing, 0, ("const", 2)), (Just ("const", 2), 0, ("xs", 0)), (Just ("const", 2), 1, ("ys", 0))]
                    keys = [("top", 0, "var/2"), ("var/2", 0, "arg/0"), ("var/2", 1, "arg/0")] :: [Preference.Feature]
                    adjustments =
                        [ Text.pack $ show (parent, position, symbol, target - original above index token)
                        | ((above, index, token), (parent, position, symbol), target) <- zip3 nodes keys [1e16, -1e16, 1 :: Double]
                        ]
                    serialized = Text.unlines ("fit-preferences 1;" : "groups []" : adjustments) <> printFitModel base
                corrected <- either fail pure $ Preference.parsePreferenceModel serialized
                let correctedScore = Preference.tokenScoreShared corrected Map.empty (Preference.caseRoot context) (Preference.caseLocals context)
                    own = correctedScore Nothing 0 ("const", 2)
                    left = correctedScore (Just ("const", 2)) 0 ("xs", 0)
                    right = correctedScore (Just ("const", 2)) 1 ("ys", 0)
                    pluginScore = own + sum [left, right]
                (own + left) + right `shouldNotBe` pluginScore
                Preference.scoreProgram corrected context (parse "const xs ys") `shouldBe` pluginScore
            it "improves preferred probabilities and reports the externally scored conditional objective" $ do
                let items = [item, other]
                    initial = Preference.fromFitModel base
                (trained, report) <- fit items
                exp (preferenceLogProbability trained item)
                    `shouldSatisfy` (> exp (preferenceLogProbability initial item) + 0.1)
                Train.stepObjective (Train.fitFinalStep report) - preferenceObjective precision trained items
                    `shouldSatisfy` ((< 1e-10) . abs)
                (_, first) <- either fail pure $ Preference.trainPreferences 1 precision base items
                Train.stepObjective (Train.fitFinalStep first) - preferenceObjective precision initial items
                    `shouldSatisfy` ((< 1e-10) . abs)
            it "retains each distinct program's mass when their correction features are identical" $ do
                let emptyBase = FitModel [] Map.empty Map.empty Map.empty
                    aliases =
                        item
                            { Preference.caseLocals = Set.empty
                            , Preference.casePreferred = Var "a"
                            , Preference.caseCandidates = map Var ["a", "b", "c"]
                            }
                forM_ [(Map.empty, 1 / 3), (Map.fromList [("a", 9), ("b", 1)], 10 / 13)] $ \(uses, expected) -> do
                    let chosen = aliases{Preference.caseUses = uses}
                    (trained, report) <- either fail pure $ Preference.trainPreferences 200 precision emptyBase [chosen]
                    exp (preferenceLogProbability trained chosen) - expected `shouldSatisfy` ((< 1e-12) . abs)
                    Train.stepObjective (Train.fitFinalStep report) - log expected `shouldSatisfy` ((< 1e-12) . abs)
            it "does not give duplicate candidate programs additional training mass" $ do
                (trained, _) <- fit [item, other]
                let repeated = item{Preference.caseCandidates = Preference.caseCandidates item <> replicate 12 (parse "id xs")}
                (withDuplicates, _) <- fit [repeated, other]
                withDuplicates `shouldBe` trained
            it "rejects missing preferences, invalid contexts, invalid counts, and invalid fitting controls" $ do
                forM_
                    [ []
                    , [item{Preference.casePreferred = Var "absent"}]
                    , [item{Preference.caseCandidates = []}]
                    , [item{Preference.caseCandidates = replicate 2 (Preference.casePreferred item)}]
                    , [item{Preference.caseRoot = ("", 0)}]
                    , [item{Preference.caseRoot = ("top", -1)}]
                    , [item{Preference.caseUses = Map.singleton "helper" (-1)}]
                    ]
                    $ \items -> Preference.trainPreferences 200 precision base items `shouldSatisfy` isLeft
                forM_ [0, -1, 0 / 0, 1 / 0] $ \invalid ->
                    Preference.trainPreferences 200 invalid base [item] `shouldSatisfy` isLeft
                forM_ [0, -1] $ \limit ->
                    Preference.trainPreferences limit precision base [item] `shouldSatisfy` isLeft
            it "round-trips cases, corrections, and legacy corpus files" $ do
                let second = other{Preference.caseGroup = "Other.hs"}
                (trained, _) <- fit [item, second, item]
                Preference.preferenceGroups trained `shouldBe` Set.fromList ["Example.hs", "Other.hs"]
                Preference.parsePreferenceModel (Preference.printPreferenceModel trained) `shouldBe` Right trained
                Preference.parsePreferenceModel (printFitModel base) `shouldBe` Right (Preference.fromFitModel base)
                Preference.preferenceGroups (Preference.fromFitModel base) `shouldBe` Set.empty
                Preference.parsePreferenceCases (Preference.printPreferenceCases [item, other]) `shouldBe` Right [item, other]
            it "requires a well-formed groups record in a preference file" $ do
                forM_ [[], ["groups"], ["groups ["], ["groups [1]"], ["groups \"Example.hs\""]] $ \records ->
                    Preference.parsePreferenceModel (Text.unlines ("fit-preferences 1;" : records) <> printFitModel base)
                        `shouldSatisfy` isLeft
            it "rejects duplicate correction keys and invalid correction fields" $ do
                let text records = Text.unlines ("fit-preferences 1;" : "groups []" : records) <> printFitModel base
                    valid = "(\"top\",0,\"reverse/1\",0.5)"
                forM_
                    [ [valid, valid]
                    , ["(\"top\",-1,\"reverse/1\",0.5)"]
                    , ["(\"\",0,\"reverse/1\",0.5)"]
                    , ["(\"top\",0,\"\",0.5)"]
                    , ["(\"top\",0,\"reverse/1\",NaN)"]
                    , ["(\"top\",0,\"reverse/1\",Infinity)"]
                    , ["(\"top\",0,\"reverse/1\",1e999)"]
                    ]
                    $ \records -> Preference.parsePreferenceModel (text records) `shouldSatisfy` isLeft
            it "rejects invalid case fields and duplicate module-use names" $ do
                forM_
                    [ item{Preference.caseRoot = ("", 0)}
                    , item{Preference.caseRoot = ("top", -1)}
                    , item{Preference.caseUses = Map.singleton "helper" (-1)}
                    ]
                    $ \invalid ->
                        Preference.parsePreferenceCases (Preference.printPreferenceCases [invalid]) `shouldSatisfy` isLeft
                let invalidUses =
                        "fit-preference-cases 1;\n(\"group\",(\"top\",0),[],[(\"helper\",1),(\"helper\",2)],Var \"a\",[Var \"a\",Var \"b\"])\n"
                Preference.parsePreferenceCases invalidUses `shouldSatisfy` isLeft
            it "preserves specialized labels, operators, and nested applications as AST data" $ do
                let specialized = App (App (Var "fmap 2") (Var "f")) (Var "xs")
                    operator = App (App (Var "(\\\\)") specialized) (App (Var "reverse") (Var "ys"))
                    valid = item{Preference.casePreferred = operator, Preference.caseCandidates = [operator, specialized, Var "xs"]}
                Preference.parsePreferenceCases (Preference.printPreferenceCases [valid]) `shouldBe` Right [valid]
            it "rejects raw Haskell expressions where a serialized Program is required" $ do
                forM_
                    [ "(\"group\",(\"top\",0),[],[],\"reverse xs\",[\"reverse xs\",\"xs\"])"
                    , "(\"group\",(\"top\",0),[],[],reverse xs,[reverse xs,xs])"
                    , "(\"group\",(\"top\",0),[],[],x + y,[x + y,x])"
                    ]
                    $ \record ->
                        Preference.parsePreferenceCases (Text.unlines ["fit-preference-cases 1;", record]) `shouldSatisfy` isLeft
        describe "the fast rejects" $
            forM_ soundness $ \(name, signature, arguments, program) ->
                it ("keep the fit of " <> name) $
                    checks signature arguments (parse program) `shouldReturn` Just True
        describe "synthesizeFits" $
            it "leaves the unification variables of the goal as it found them" $ do
                result <- inTypechecker session $ do
                    variable <- newFlexiTyVar liftedTypeKind
                    let hole = TypedHole{th_relevant_cts = emptyBag, th_implics = [], th_hole = Nothing}
                    fits <-
                        synthesizeFits
                            defaultOptions{optionMaximumSize = 2, optionFits = 3}
                            hole
                            candidates
                            (mkListTy (mkTyVarTy variable))
                    details <- readMetaTyVar variable
                    pure (length fits, isFlexi details)
                result `shouldBe` Just (3, True)
  where
    -- Two signatures, each with a fit that ignores an argument and one that does not.
    ignoring =
        [ ("[a] -> Int -> [a]", ["xs", "n"], ["const xs n", "take n xs"])
        , ("(a -> Bool) -> [a] -> Int", ["p", "xs"], ["const (length xs) p", "length (filter p xs)"])
        ]
    -- Fits that the solver accepts and a careless fast reject would not.
    soundness =
        [ ("a coercion through a newtype", "[Sum Int] -> [Int]", ["xs"], "coerce xs")
        , ("a given equality", "(a ~ Int) => a -> Int", ["x"], "x")
        , ("a quantified given", "(forall x. Sized (f x)) => f Bool -> Int", ["y"], "sized y")
        ]
    {- One law for each component of base that has a body from its unfolding
    in GHC 9.14 (the constructors of pairs, lists, Bool, Maybe, and Either
    occur in them). A GHC release that drops or changes an unfolding breaks
    its law.
    -}
    laws =
        [ ("fst ((,) x y)", "x")
        , ("snd ((,) x y)", "y")
        , ("curry f x y", "f ((,) x y)")
        , ("uncurry f ((,) x y)", "f x y")
        , ("swap ((,) x y)", "(,) y x")
        , ("id x", "x")
        , ("const x y", "x")
        , ("flip f x y", "f y x")
        , ("(.) f g x", "f (g x)")
        , ("($) f x", "f x")
        , ("(&) x f", "f x")
        , ("on g f x y", "g (f x) (f y)")
        , ("otherwise", "True")
        , ("not True", "False")
        , ("(&&) True b", "b")
        , ("(||) False b", "b")
        , ("bool f t True", "t")
        , ("maybe n f (Just x)", "f x")
        , ("fromMaybe d (Just x)", "x")
        , ("isJust (Just x)", "True")
        , ("isNothing Nothing", "True")
        , ("fromJust (Just x)", "x")
        , ("maybeToList (Just x)", "(:) x []")
        , ("either f g (Left x)", "f x")
        , ("fromLeft d (Left x)", "x")
        , ("fromRight d (Right x)", "x")
        , ("isLeft (Left x)", "True")
        , ("isRight (Right x)", "True")
        , ("head ((:) x xs)", "x")
        , ("tail ((:) x xs)", "xs")
        , ("uncons ((:) x xs)", "Just ((,) x xs)")
        ]
    -- Programs that respell one program, from the probe of the merges.
    respellings =
        [ ("flip filter xs p", "filter p xs")
        , ("curry snd n (f x)", "f x")
        , ("(.) length reverse xs", "length (reverse xs)")
        , ("uncurry id p", "fst p (snd p)")
        , ("maybe n f (Just x)", "f x")
        , ("either f g (Left x)", "f x")
        , ("(,) (fst p) (snd p)", "p")
        , ("not (not b)", "b")
        , -- Unsaturated components with a body merge by eta-expansion.
          ("foldr (flip const) z xs", "foldr (const id) z xs")
        ]
    -- Programs that differ in meaning.
    different =
        [ ("filter p xs", "takeWhile p xs")
        , ("fst p", "snd p")
        , ("flip f x y", "f x y")
        , ("maybe n f m", "f m")
        ]
    parse = either error id . parseProgram
    size program = case program of
        Var _ -> 1
        App function argument -> size function + size argument

-- | Normalize public program scores over a nonempty supplied candidate pool.
preferenceLogProbability :: Preference.PreferenceModel -> Preference.PreferenceCase -> Double
preferenceLogProbability model item =
    Preference.scoreProgram model item (Preference.casePreferred item) - largest - log (sum masses)
  where
    scores = map (Preference.scoreProgram model item) $ Set.toList $ Set.fromList $ Preference.caseCandidates item
    largest = maximum scores
    masses = map (exp . subtract largest) scores

-- | Check the reported objective through complete program probabilities and the exposed corrections.
preferenceObjective :: Double -> Preference.PreferenceModel -> [Preference.PreferenceCase] -> Double
preferenceObjective precision model items =
    sum (map (preferenceLogProbability model) items) / fromIntegral (length items)
        - precision / 2 * sum (map (^ (2 :: Int)) $ Map.elems $ Preference.preferenceWeights model)
