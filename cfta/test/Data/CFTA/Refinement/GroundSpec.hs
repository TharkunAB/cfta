{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Ground evaluation on integer lists that @nil@ and @cons@ build, with
Haskell interpretations of @append@, @reverse@, @sorted@, and @member@.
-}
module Data.CFTA.Refinement.GroundSpec (spec) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (fromString)
import Test.Hspec

import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement (
    Entailment (entails),
    Node (Node),
    Symbol (RefinedSymbol),
    Verdict (..),
    denotationAtMost,
    entailsWithBindings,
    fallback,
    noConstraint,
    pattern Transition,
 )
import Data.CFTA.Refinement.Definition (Definition (..), Definitions)
import Data.CFTA.Refinement.Expression (predicate, refinementFormula, true, uninterpreted, (.==), (.>=))
import Data.CFTA.Refinement.Ground (Interpretations (..), Value (..), groundEntailment)
import qualified Data.CFTA.Refinement.Guard as Guard
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Refinement.TestSupport (unusedEntailment)
import Data.CFTA.Symbol (valueName)
import qualified Data.CFTA.Term as Term

-- | The sort of integer lists.
list :: Sort
list = NamedSort "List" [IntSort]

-- | The value name of a refinement.
value :: Name
value = fromString valueName

-- | The term of a list.
listTerm :: [Integer] -> Term
listTerm = foldr (\x rest -> App "cons" [Lit x, rest]) (App "nil" [])

-- | The value of a list.
listValue :: [Integer] -> Value
listValue = foldr (\x rest -> DataValue "cons" [IntValue x, rest]) (DataValue "nil" [])

-- | The list of a value, if @nil@ and @cons@ build it.
valueList :: Value -> Maybe [Integer]
valueList = \case
    DataValue "nil" [] -> Just []
    DataValue "cons" [IntValue x, rest] -> (x :) <$> valueList rest
    _ -> Nothing

-- | Whether a list is in ascending order.
ascending :: [Integer] -> Bool
ascending xs = and (zipWith (<=) xs (drop 1 xs))

-- | A list value, two list names, and the sorts of the list functions.
declarations :: [(Name, Sort)]
declarations =
    [ (value, list)
    , ("xs", list)
    , ("ys", list)
    , ("nil", list)
    , ("cons", FunctionSort [IntSort, list] list)
    , ("append", FunctionSort [list, list] list)
    , ("reverse", FunctionSort [list] list)
    ]

-- | Haskell meanings of the list functions and predicates.
lists :: Interpretations
lists =
    Interpretations
        { interpretedFunctions =
            Map.fromList
                [ ("nil", \case [] -> Just (listValue []); _ -> Nothing)
                , ("cons", \case [IntValue x, rest] -> listValue . (x :) <$> valueList rest; _ -> Nothing)
                , ("append", \case [xs, ys] -> listValue <$> ((<>) <$> valueList xs <*> valueList ys); _ -> Nothing)
                , ("reverse", \case [xs] -> listValue . reverse <$> valueList xs; _ -> Nothing)
                ]
        , interpretedPredicates =
            Map.fromList
                [ ("sorted", ([list], \case [xs] -> ascending <$> valueList xs; _ -> Nothing))
                , ("member", ([IntSort, list], \case [IntValue x, xs] -> elem x <$> valueList xs; _ -> Nothing))
                ]
        , inhabitedSorts = Set.fromList [list]
        }

-- | @between x lo hi@ on integers, and @hasBoth@ on lists through an interpreted predicate.
definitions :: Definitions
definitions =
    Map.fromList
        [
            ( "between"
            , Definition
                [("x", IntSort), ("lo", IntSort), ("hi", IntSort)]
                (And [Atom Le (Var "lo") (Var "x"), Atom Le (Var "x") (Var "hi")])
            )
        ,
            ( "hasBoth"
            , Definition [("l", list)] (And [Predicate "member" [Lit 1, Var "l"], Predicate "member" [Lit 2, Var "l"]])
            )
        ]

spec :: Spec
spec = do
    let ground = groundEntailment lists definitions declarations []
        integers = groundEntailment lists definitions [(value, IntSort)] []
        is xs = Atom Eq (Var value) (listTerm xs)
        computes term = Atom Eq (Var value) term
        sorted = Predicate "sorted" [Var value]
        member x = Predicate "member" [Lit x, Var value]

    describe "groundEntailment" $ do
        it "decides a predicate of a computed list" $ do
            entails ground (computes (App "append" [listTerm [1], listTerm [2]])) sorted >>= (`shouldBe` Yes)
            entails ground (computes (App "append" [listTerm [2], listTerm [1]])) sorted >>= (`shouldBe` No)
            entails ground (computes (App "reverse" [listTerm [1, 2]])) (member 1) >>= (`shouldBe` Yes)
            entails ground (computes (App "reverse" [listTerm [1, 2]])) sorted >>= (`shouldBe` No)

        it "solves a chain of equalities with fresh names" $ do
            let chain left right =
                    And [computes (App "append" [Var "a", Var "b"]), Atom Eq (Var "a") (listTerm left), Atom Eq (Var "b") (listTerm right)]
                bindings = [("a", value), ("b", value)]
            entailsWithBindings ground bindings (chain [1] [2]) sorted >>= (`shouldBe` Yes)
            entailsWithBindings ground bindings (chain [2] [1]) sorted >>= (`shouldBe` No)

        it "uses the assumptions" $ do
            let assuming = groundEntailment lists definitions declarations [Atom Eq (Var "xs") (listTerm [2, 1])]
            entails assuming (computes (App "reverse" [Var "xs"])) sorted >>= (`shouldBe` Yes)

        it "gives Unknown for a value that is not ground" $
            entails ground (computes (App "append" [Var "xs", Var "ys"])) sorted >>= (`shouldBe` Unknown)

        it "decides a formula when the unknown parts do not change its truth" $ do
            entails ground (is [1]) (Or [member 1, Predicate "sorted" [Var "xs"]]) >>= (`shouldBe` Yes)
            entails ground (And [is [1], Predicate "sorted" [Var "xs"]]) (member 2) >>= (`shouldBe` Unknown)

        it "gives Unknown for a quantifier" $
            entails ground Top (Forall [("zs", list)] (Atom Eq (App "reverse" [App "reverse" [Var "zs"]]) (Var "zs")))
                >>= (`shouldBe` Unknown)

        it "gives Unknown for a predicate without a definition or an interpretation" $
            entails ground (is [1]) (Predicate "mystery" [Var value]) >>= (`shouldBe` Unknown)

        it "gives Unknown for a query that fails the sort check" $
            entails ground (Atom Eq (Var value) (Lit 3)) (Atom Eq (Var value) (Lit 3)) >>= (`shouldBe` Unknown)

        it "gives No only when each declared named sort has a value" $ do
            let unknownSorts = groundEntailment lists{inhabitedSorts = Set.empty} definitions declarations []
            entails unknownSorts (is [2, 1]) sorted >>= (`shouldBe` Unknown)
            entails unknownSorts (is [1, 2]) sorted >>= (`shouldBe` Yes)

        it "needs no value for the sort of an interpreted function" $ do
            let stream = NamedSort "Stream" []
                next = \case [IntValue x, rest] -> Just (DataValue "next" [IntValue x, rest]); _ -> Nothing
                streams = lists{interpretedFunctions = Map.insert "next" next (interpretedFunctions lists)}
                withNext extra = groundEntailment streams definitions (declarations <> [("next", FunctionSort [IntSort, stream] stream)] <> extra) []
            entails (withNext []) (is [2, 1]) sorted >>= (`shouldBe` No)
            entails (withNext [("s", stream)]) (is [2, 1]) sorted >>= (`shouldBe` Unknown)

        it "unfolds a defined predicate" $ do
            let between lo hi = Predicate "between" [Var value, Lit lo, Lit hi]
            entails integers (Atom Eq (Var value) (Lit 2)) (between 0 3) >>= (`shouldBe` Yes)
            entails integers (Atom Eq (Var value) (Lit 5)) (between 0 3) >>= (`shouldBe` No)

        it "interprets the predicates in the body of a definition" $ do
            entails ground (is [2, 1]) (Predicate "hasBoth" [Var value]) >>= (`shouldBe` Yes)
            entails ground (is [2]) (Predicate "hasBoth" [Var value]) >>= (`shouldBe` No)

    describe "fallback" $ do
        let positive = refinementFormula (.>= 1)
            natural = refinementFormula (.>= 0)

        it "asks Z3 when ground evaluation gives Unknown" $
            withZ3 [(value, IntSort)] $ \z3 -> do
                entails integers positive natural >>= (`shouldBe` Unknown)
                entails (fallback integers z3) positive natural >>= (`shouldBe` Yes)

        it "keeps a verdict of the first solver" $
            entails (fallback integers unusedEntailment) (refinementFormula (.== 2)) natural >>= (`shouldBe` Yes)

    describe "a guard decided by ground evaluation" $
        it "accepts the pairs of list leaves that a Haskell filter accepts" $ do
            let chunks = [[], [1], [2], [1, 2], [2, 1]]
                leaf xs = RefinedSymbol (fromString ("chunk " <> show xs)) (is xs)
                leaves = Node [Transition (fromString ("chunk " <> show xs)) (is xs) [] noConstraint | xs <- chunks]
                root =
                    either (error . show) (\edge -> Node [edge])
                        $ Guard.transition "pair" (const true) [leaves, leaves]
                        $ Guard.contract (\x y -> predicate "sorted" [uninterpreted "append" [x, y]])
                pair xs ys = Term.Node (RefinedSymbol "pair" true) [Term.Node (leaf xs) [], Term.Node (leaf ys) []]
                expected = [pair xs ys | xs <- chunks, ys <- chunks, ascending (xs <> ys)]
            accepted <- denotationAtMost ground 1 root
            case accepted of
                Left err -> expectationFailure (show err)
                Right terms -> do
                    terms `shouldMatchList` expected
                    length terms `shouldBe` 12
