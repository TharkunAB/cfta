{-# LANGUAGE OverloadedStrings #-}

-- | Differences and three-way merges of languages by their stable names.
module Data.CFTA.MergeSpec (spec) where

import Control.Monad (forM)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck (
    Gen,
    Property,
    counterexample,
    elements,
    forAll,
    frequency,
    oneof,
    shuffle,
    sublistOf,
    suchThatMap,
    tabulate,
    vectorOf,
    (===),
 )
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint (..), Guard (Bottom), equalityConstraint, noConstraint)
import qualified Data.CFTA.Document as D
import Data.CFTA.Equality.Constraint (EqConstraints (EqConstraints), mkEqConstraints)
import Data.CFTA.Language (Exclusion (..), Language (..))
import qualified Data.CFTA.Language as L
import Data.CFTA.Merge (Conflict (..), DiffError (..), MergeError (..), Versions (..))
import qualified Data.CFTA.Merge as Merge
import Data.CFTA.Path (path)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..))

spec :: Spec
spec = describe "differences and merges" $ do
    modifyMaxSuccess (const 500) $ do
        it "diff gives the update and the patch from one language to the other"
            $ forAll ((,) <$> randomLanguage <*> QC.oneof [randomLanguage, randomLanguage >>= mutate])
            $ uncurry diffLaw
        it "merge3 keeps the change of one side, and the same change of both sides" $
            forAll (randomLanguage >>= \original -> (original,) <$> mutate original) $ \(original, other) ->
                Merge.merge3 original original other === Right other
                    QC..&&. Merge.merge3 original other original === Right other
                    QC..&&. Merge.merge3 original other other === Right other
        it "merge3 is symmetric, except for the order of new productions" $
            forAll (randomLanguage >>= \original -> (original,,) <$> mutate original <*> mutate original) $ \(original, left, right) ->
                symmetric original left right

    describe "conflicts" $ do
        it "name a changed initial state" $
            Merge.merge3 fixture (restart "a" fixture) (restart "b" fixture)
                `shouldBe` Left (Conflicts [StartConflict $ Versions (Just "s") (Just "a") (Just "b")])
        it "name a row that one side deletes and the other side changes" $ do
            let left = changed fixture $ L.editSource (D.DeleteRow "b")
                right = changed fixture $ L.define (L.at "b" "u") "one" []
            Merge.merge3 fixture left right
                `shouldBe` Left (Conflicts [RowConflict "b" $ Versions (rowOf "b" fixture) Nothing (rowOf "b" right)])
        it "name a production whose constructor the two sides change, or that one side deletes" $ do
            let left = changed fixture $ L.define (L.at "s" "q") "wrap" ["a"] <> L.remove (L.at "a" "t")
                right = changed fixture $ L.define (L.at "s" "q") "pair" ["s", "s"] <> L.require (L.at "a" "t") "g" impossible
            Merge.merge3 fixture left right
                `shouldBe` Left
                    ( Conflicts
                        [ ProductionConflict (L.at "a" "t") $ Versions (productionOf "a" "t" fixture) Nothing (productionOf "a" "t" right)
                        , ProductionConflict (L.at "s" "q") $
                            Versions (productionOf "s" "q" fixture) (productionOf "s" "q" left) (productionOf "s" "q" right)
                        ]
                    )
        it "name a fact" $ do
            let left = changed fixture $ L.require (L.at "s" "p") "f" impossible
                right = changed fixture $ L.require (L.at "s" "p") "f" equal
            Merge.merge3 fixture left right
                `shouldBe` Left (Conflicts [FactConflict (L.at "s" "p") "f" $ Versions (Just noConstraint) (Just impossible) (Just equal)])
        it "name an order of the productions of a row that the two sides change in different ways" $ do
            let left = reorder "a" ["t", "r", "v"] fixture
                right = reorder "a" ["r", "v", "t"] fixture
            Merge.merge3 fixture left right
                `shouldBe` Left
                    (Conflicts [OrderConflict "a" $ Versions (Just ["r", "t", "v"]) (Just ["t", "r", "v"]) (Just ["r", "v", "t"])])
        it "name an exclusion, and report every conflict" $ do
            let left = changed fixture $ L.without "x" (Anywhere $ TemplateNode "leaf" []) <> L.require (L.at "s" "p") "f" impossible
                right = changed fixture $ L.restore "x" <> L.require (L.at "s" "p") "f" equal
            Merge.merge3 fixture left right
                `shouldBe` Left
                    ( Conflicts
                        [ FactConflict (L.at "s" "p") "f" $ Versions (Just noConstraint) (Just impossible) (Just equal)
                        , ExclusionConflict "x" $ Versions (Just $ AtRoot Hole) (Just $ Anywhere $ TemplateNode "leaf" []) Nothing
                        ]
                    )
        it "report a merge of the keys that is not a valid document" $ do
            let left = changed fixture $ L.editSource (D.DeleteRow "b")
                right = changed fixture $ L.define (L.at "s" "n") "wrap" ["b"]
            Merge.merge3 fixture left right `shouldBe` Left (InvalidMerge $ D.InvalidGraph $ FTA.DanglingState "b")

    describe "merges without conflicts" $ do
        it "combine changes to different keys of one production" $ do
            let left = changed fixture $ L.require (L.at "s" "p") "f" impossible
                right = changed fixture $ L.require (L.at "s" "p") "g" equal <> L.define (L.at "s" "q") "wrap" ["a"]
            Merge.merge3 fixture left right
                `shouldBe` Right
                    ( changed fixture $
                        L.require (L.at "s" "p") "f" impossible <> L.require (L.at "s" "p") "g" equal <> L.define (L.at "s" "q") "wrap" ["a"]
                    )
        it "keep a production that one side inserts in the middle of a row" $ do
            let left =
                    changed fixture
                        $ L.editSource
                        $ D.PutRow "a" [named "r" "leaf" [], named "u" "one" [], named "t" "one" [], named "v" "leaf" []]
                right = changed fixture $ L.without "y" (AtRoot Hole)
            fmap (rowOf "a") (Merge.merge3 fixture left right) `shouldBe` Right (rowOf "a" left)
        it "put the new productions of the left side before those of the right side" $ do
            let left = changed fixture $ L.define (L.at "a" "u") "one" [] <> L.remove (L.at "a" "v")
                right = changed fixture $ L.define (L.at "a" "w") "leaf" []
                names = fmap (map (D.annotationName . FTA.transitionConstraint) . concat . rowOf "a")
            names (Merge.merge3 fixture left right) `shouldBe` Right ["r", "t", "u", "w"]
            names (Merge.merge3 fixture right left) `shouldBe` Right ["r", "t", "w", "u"]
        it "give the difference of two languages with other initial states as an error" $
            Merge.diff fixture (restart "a" fixture) `shouldBe` Left (DifferentStart "s" "a")

-- | 'diff' and 'Merge.diffDocument' give the second language from the first, or report other initial states.
diffLaw :: Language String -> Language String -> Property
diffLaw before after = case Merge.diff before after of
    Left (DifferentStart old new) ->
        tabulate "difference" ["other initial state"] $ (old, new) === (start before, start after)
    Right changes ->
        tabulate "difference" [kind changes] $
            L.update before changes === Right after
                QC..&&. (D.applyPatch <$> Merge.diffDocument (source before) (source after) <*> pure (source before))
                    === Right (Right $ source after)
  where
    kind (L.Update operations)
        | null operations = "none"
        | or [Map.member state (rows before) | L.EditSource (D.PutRow state _) <- operations] = "a row with a new order"
        | otherwise = "edits by name"

-- | 'Merge.merge3' with the sides exchanged gives the same result, or the same conflicts with the sides exchanged.
symmetric :: Language String -> Language String -> Language String -> Property
symmetric original left right = case (Merge.merge3 original left right, Merge.merge3 original right left) of
    (Right merged, Right exchanged) ->
        tabulate "merge" ["merged"]
            $ counterexample (show (merged, exchanged))
            $ (start merged, exclusions merged, Map.map byName (rows merged), Map.mapWithKey oldOrder (rows merged))
                === (start exchanged, exclusions exchanged, Map.map byName (rows exchanged), Map.mapWithKey oldOrder (rows exchanged))
    (Left (Conflicts conflicts), Left (Conflicts exchanged)) ->
        tabulate "merge" ["conflict"] $ map exchange conflicts === exchanged
    (Left (InvalidMerge _), Left (InvalidMerge _)) -> tabulate "merge" ["invalid"] True
    results -> counterexample (show results) False
  where
    byName row = Map.fromList [(D.annotationName $ FTA.transitionConstraint production, production) | production <- row]
    baseNames = Map.map (map $ D.annotationName . FTA.transitionConstraint) (rows original)
    oldOrder state row =
        [ name
        | production <- row
        , let name = D.annotationName $ FTA.transitionConstraint production
        , name `elem` Map.findWithDefault [] state baseNames
        ]
    exchange conflict = case conflict of
        StartConflict versions -> StartConflict $ sides versions
        RowConflict state versions -> RowConflict state $ sides versions
        ProductionConflict ref versions -> ProductionConflict ref $ sides versions
        FactConflict ref fact versions -> FactConflict ref fact $ sides versions
        OrderConflict state versions -> OrderConflict state $ sides versions
        ExclusionConflict name versions -> ExclusionConflict name $ sides versions
    sides (Versions old left' right') = Versions old right' left'

-- | The base language of the conflict tests.
fixture :: Language String
fixture =
    Language
        ( must $
            D.mkDocument
                "s"
                [ ("s", [withFacts "p" "pair" ["a", "a"] [("f", noConstraint)], named "q" "wrap" ["s"]])
                , ("a", [named "r" "leaf" [], named "t" "one" [], named "v" "leaf" []])
                , ("b", [named "k" "leaf" []])
                ]
        )
        (Map.singleton "x" $ AtRoot Hole)

-- | Apply an update that must be valid.
changed :: Language String -> L.Update String -> Language String
changed language = must . L.update language

-- | Give a language another initial state, which no update can do.
restart :: String -> Language String -> Language String
restart state language = language{source = must $ D.mkDocument state $ Map.toAscList $ rows language}

-- | Give a row the productions with these names, in this order.
reorder :: String -> [Text] -> Language String -> Language String
reorder state names language =
    changed language $ L.editSource $ D.PutRow state [production | name <- names, Just production <- [lookup name byName]]
  where
    byName = [(D.annotationName $ FTA.transitionConstraint production, production) | production <- concat $ rowOf state language]

-- | The row of a state.
rowOf :: String -> Language String -> Maybe [Merge.Production String]
rowOf state = Map.lookup state . rows

-- | A production of a state by its name.
productionOf :: String -> Text -> Language String -> Maybe (Merge.Production String)
productionOf state name language = lookup name [(D.annotationName $ FTA.transitionConstraint p, p) | p <- concat $ rowOf state language]

-- | A production without facts.
named :: Text -> Symbol -> [String] -> Merge.Production String
named name symbol children = withFacts name symbol children []

-- | A production with facts.
withFacts :: Text -> Symbol -> [String] -> [(Text, Constraint)] -> Merge.Production String
withFacts name symbol children facts = FTA.Transition symbol children $ D.Annotation name $ Map.fromList facts

-- | The initial state of a language.
start :: Language String -> String
start = FTA.initialState . D.sourceGraph . source

-- | The rows of a language.
rows :: Language String -> Map String [Merge.Production String]
rows = FTA.transitionTable . D.sourceGraph . source

-- | A constraint that no term satisfies.
impossible :: Constraint
impossible = Constraint (EqConstraints []) Bottom

-- | The two children are equal.
equal :: Constraint
equal = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]

-- | Stop a test on an unexpected error.
must :: (Show failure) => Either failure value -> value
must = either (error . show) id

{- | A random language: the initial state @s@, some of the states @a@ and @b@,
rows with distinct production names in a random order, random facts, and
random exclusions. Each symbol has one arity, so each language is valid.
-}
randomLanguage :: Gen (Language String)
randomLanguage = do
    others <- sublistOf ["a", "b"]
    let present = "s" : others
    table <- forM present $ \state -> (state,) <$> (shuffle productionNames >>= sublistOf >>= mapM (randomProduction present))
    Language (must $ D.mkDocument "s" table) <$> exclusionMap

-- | A random production with a name, whose children are some of the given states.
randomProduction :: [String] -> Text -> Gen (Merge.Production String)
randomProduction present name = do
    (symbol, arity) <- elements symbols
    children <- vectorOf arity (elements present)
    facts <- sublistOf factNames >>= mapM (\fact -> (fact,) <$> elements constraints)
    pure $ withFacts name symbol children facts

-- | Random exclusions.
exclusionMap :: Gen (Map L.ExclusionName Exclusion)
exclusionMap = Map.fromList <$> (sublistOf ["x", "y"] >>= mapM (\name -> (name,) <$> elements exclusionValues))

{- | One to three random changes of a language: a new order of a row, a new
production at any place, a deleted production, a new constructor, a new or
removed fact, a new or deleted state, new exclusions, or a new initial state.
A change that gives an invalid document is drawn again.
-}
mutate :: Language String -> Gen (Language String)
mutate original = do
    count <- QC.chooseInt (1, 3)
    go count original
  where
    go 0 current = pure current
    go count current = step current `suchThatMap` valid >>= go (count - 1 :: Int)
    valid (initial, table, excluded) = either (const Nothing) (\document -> Just $ Language document excluded) $ D.mkDocument initial (Map.toAscList table)
    step current = do
        let table = rows current
            present = Map.keys table
            unchanged = (start current, table, exclusions current)
            inRow f = do
                state <- elements present
                row <- f (Map.findWithDefault [] state table)
                pure (start current, Map.insert state row table, exclusions current)
            atProduction f = inRow $ \row ->
                if null row
                    then pure row
                    else do
                        index <- QC.chooseInt (0, length row - 1)
                        changedOne <- f (row !! index)
                        pure $ take index row <> [changedOne] <> drop (index + 1) row
        frequency
            [ (2, inRow shuffle)
            ,
                ( 3
                , inRow $ \row -> case filter (`notElem` map nameOf row) productionNames of
                    [] -> pure row
                    free -> do
                        new <- elements free >>= randomProduction present
                        index <- QC.chooseInt (0, length row)
                        pure $ take index row <> [new] <> drop index row
                )
            ,
                ( 2
                , inRow $ \row ->
                    if null row then pure row else (\index -> take index row <> drop (index + 1) row) <$> QC.chooseInt (0, length row - 1)
                )
            ,
                ( 2
                , atProduction $ \old -> (\new -> new{FTA.transitionConstraint = FTA.transitionConstraint old}) <$> randomProduction present (nameOf old)
                )
            ,
                ( 3
                , atProduction $ \old -> do
                    fact <- elements factNames
                    constraint <- elements constraints
                    pure $
                        withFacts
                            (nameOf old)
                            (FTA.transitionSymbol old)
                            (FTA.transitionChildren old)
                            (Map.toList $ Map.insert fact constraint $ factsOf old)
                )
            ,
                ( 2
                , atProduction $ \old -> do
                    fact <- elements factNames
                    pure $
                        withFacts
                            (nameOf old)
                            (FTA.transitionSymbol old)
                            (FTA.transitionChildren old)
                            (Map.toList $ Map.delete fact $ factsOf old)
                )
            ,
                ( 1
                , oneof [pure unchanged, (\state -> (start current, Map.delete state table, exclusions current)) <$> elements present]
                )
            ,
                ( 1
                , (\table' -> (start current, table', exclusions current))
                    <$> ( Map.union table . Map.fromList
                            <$> forM ["a", "b"] (\state -> (state,) <$> (sublistOf productionNames >>= mapM (randomProduction ("a" : "b" : present))))
                        )
                )
            , (2, (\excluded -> (start current, table, excluded)) <$> exclusionMap)
            , (1, (\initial -> (initial, table, exclusions current)) <$> elements present)
            ]
    nameOf = D.annotationName . FTA.transitionConstraint
    factsOf = D.annotationFacts . FTA.transitionConstraint

-- | The states of the random languages are @s@, @a@, and @b@; the production names are these.
productionNames :: [Text]
productionNames = ["p", "q", "r", "t"]

-- | The symbols of the random languages, each with one arity.
symbols :: [(Symbol, Int)]
symbols = [("leaf", 0), ("one", 0), ("wrap", 1), ("pair", 2)]

-- | The fact names of the random languages.
factNames :: [Text]
factNames = ["f", "g"]

-- | The constraints of the random facts.
constraints :: [Constraint]
constraints = [noConstraint, impossible, equal]

-- | The exclusions of the random languages.
exclusionValues :: [Exclusion]
exclusionValues = [AtRoot Hole, Anywhere $ TemplateNode "leaf" []]
