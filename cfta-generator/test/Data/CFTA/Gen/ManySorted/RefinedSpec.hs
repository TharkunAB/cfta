{-# LANGUAGE OverloadedStrings #-}

{- | Refinements in a run-time signature, against a brute-force enumeration
that evaluates the measures and the preconditions on integers, with the Z3
solver.
-}
module Data.CFTA.Gen.ManySorted.RefinedSpec (spec) where

import Data.List (sort)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.ManySorted
import Data.CFTA.Gen.ManySorted.Refined
import Data.CFTA.Index (Cardinality (..), everyRank)
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Refinement.Expression ((./=), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Term (Term (Node))

data Sort = Int | Quot | Level | Tag
    deriving (Eq, Ord, Show)

codec :: ValueCodec Sort Symbol
codec =
    ValueCodec
        { injectInteger = \n -> Symbol (Text.pack ('#' : show n))
        , projectInteger = \(Symbol text) -> case Text.unpack text of
            '#' : digits | [(n, "")] <- reads digits -> Just n
            _ -> Nothing
        , valueSymbol = \s -> Symbol (Text.pack ('<' : show s <> ">"))
        }

-- | Int has the integers 0 to the bound except 3, add, and sub when the first is not less. Quot has divide by a nonzero integer.
division :: Integer -> Int -> RefinedSignature Sort
division high nesting =
    RefinedSignature
        { refinedBase =
            SortedSignature
                { sortedSorts = [Int, Quot]
                , sortedFunctions =
                    [ SortedFunction "add" [Int, Int] Int
                    , SortedFunction "sub" [Int, Int] Int
                    , SortedFunction "divide" [Int, Int] Quot
                    ]
                , sortedRoots = [Int, Quot]
                , sortedValues = [ValueSort Int (Interval 0 high)]
                }
        , refinedSemantics =
            [ ("add", FunctionSemantics (Just (binary (+))) Nothing)
            , ("sub", FunctionSemantics (Just (binary (-))) (Just (binary (.>=))))
            , ("divide", FunctionSemantics Nothing (Just (binary (\_ b -> b ./= 0))))
            ]
        , refinedConditions = [(Int, \v -> v ./= 3)]
        , refinedNesting = nesting
        }

-- | The terms of the signature, with the integer 3 allowed, by the nesting. Optionally only the valid terms.
terms :: Bool -> Integer -> Int -> [(Sort, Term Symbol)]
terms onlyValid high nesting = [(Quot, t) | t <- quots nesting] <> [(Int, t) | t <- ints nesting]
  where
    ints 0 = [Node (injectInteger codec n) [] | n <- [0 .. high], not onlyValid || n /= 3]
    ints level =
        ints 0
            <> [Node "add" [l, r] | l <- below, r <- below]
            <> [Node "sub" [l, r] | l <- below, r <- below, not onlyValid || measure l >= measure r]
      where
        below = ints (level - 1)
    quots 0 = []
    quots level = [Node "divide" [l, r] | l <- ints (level - 1), r <- ints (level - 1), not onlyValid || measure r /= 0]

-- | Pools: Level has the integers 10, 20, and 30 without 20, and Tag has two symbols without integers.
pools :: Int -> RefinedSignature Sort
pools nesting =
    RefinedSignature
        { refinedBase =
            SortedSignature
                { sortedSorts = [Int, Level, Tag, Quot]
                , sortedFunctions = [SortedFunction "shift" [Level, Int] Int, SortedFunction "label" [Tag, Int] Quot]
                , sortedRoots = [Int, Quot]
                , sortedValues =
                    [ ValueSort Int (Interval 0 5)
                    , ValueSort Level (Pool ["#10", "#20", "#30"])
                    , ValueSort Tag (Pool ["red", "blue"])
                    ]
                }
        , refinedSemantics =
            [ ("shift", FunctionSemantics (Just (binary (+))) (Just (binary (\_ b -> b .>= 1))))
            , ("label", FunctionSemantics Nothing (Just (binary (\_ b -> b .>= 1))))
            ]
        , refinedConditions = [(Int, \v -> v ./= 3), (Level, \v -> v ./= 20)]
        , refinedNesting = nesting
        }

-- | The terms of the pool signature, with the values that the conditions drop allowed, by the nesting. Optionally only the valid terms.
poolTerms :: Bool -> Int -> [Term Symbol]
poolTerms onlyValid nesting = quots nesting <> ints nesting
  where
    levels = [Node l [] | l <- ["#10", "#20", "#30"], not onlyValid || l /= "#20"]
    tags = [Node t [] | t <- ["red", "blue"]]
    ints 0 = [Node (injectInteger codec n) [] | n <- [0 .. 5], not onlyValid || n /= 3]
    ints level = ints 0 <> [Node "shift" [l, i] | l <- levels, i <- ints (level - 1), not onlyValid || measure i >= 1]
    quots 0 = []
    quots level = [Node "label" [t, i] | t <- tags, i <- ints (level - 1), not onlyValid || measure i >= 1]

-- | The first node in preorder where the brute-force semantics of the pool signature fails.
poolFailure :: Term Symbol -> Maybe (RefinedTypeError Sort)
poolFailure = go []
  where
    go reversed (Node symbol children)
        | Just n <- projectInteger codec symbol, null children, n == 3 || n == 20 = Just (ConditionFailed here symbol)
        | symbol == "shift" || symbol == "label", [_, i] <- children, measure i < 1 = Just (PreconditionFailed here symbol)
        | otherwise = firstOf [go (index : reversed) child | (index, child) <- zip [0 ..] children]
      where
        here = path (map ChildIndex (reverse reversed))
    firstOf (Just failure : _) = Just failure
    firstOf (Nothing : rest) = firstOf rest
    firstOf [] = Nothing

-- | The integer of a term of Int.
measure :: Term Symbol -> Integer
measure (Node (Symbol text) children) = case (Text.unpack text, map measure children) of
    ('#' : digits, []) | [(n, "")] <- reads digits -> n
    ("add", [a, b]) -> a + b
    ("sub", [a, b]) -> a - b
    ("shift", [a, b]) -> a + b
    _ -> error "measure"

-- | The first node in preorder where the brute-force semantics fails, with its path.
firstFailure :: Term Symbol -> Maybe (RefinedTypeError Sort)
firstFailure = go []
  where
    go reversed (Node symbol children)
        | Just n <- projectInteger codec symbol, null children = if n == 3 then Just (ConditionFailed here symbol) else Nothing
        | symbol == "sub", [a, b] <- children, measure a < measure b = Just (PreconditionFailed here symbol)
        | symbol == "divide", [_, b] <- children, measure b == 0 = Just (PreconditionFailed here symbol)
        | otherwise = firstOf [go (index : reversed) child | (index, child) <- zip [0 ..] children]
      where
        here = path (map ChildIndex (reverse reversed))
    firstOf (Just failure : _) = Just failure
    firstOf (Nothing : rest) = firstOf rest
    firstOf [] = Nothing

spec :: Spec
spec = describe "Data.CFTA.Gen.ManySorted.Refined" $ do
    it "generates the terms whose preconditions hold, and counts them" $
        withZ3 [] $ \solver -> do
            result <- refinedGen solver codec (division 5 2)
            case result of
                Left err -> expectationFailure (either show show err)
                Right generator -> do
                    let expected = [t | (_, t) <- terms True 5 2]
                        generated = either (error . show) id (Gen.values generator)
                    sort generated `shouldBe` sort expected
                    Gen.cardinality generator `shouldBe` Right (Cardinality (fromIntegral (length expected)))

    it "counts a million values without listing them" $
        withZ3 [] $ \solver -> do
            result0 <- refinedGen solver codec (division 999999 0)
            result1 <- refinedGen solver codec (division 999999 1)
            let n = 999999 :: Integer
            cardinalityOf result0 `shouldBe` Right (Cardinality n)
            cardinalityOf result1 `shouldBe` Right (Cardinality (n + n * n + n * (n + 1) `div` 2 + n * (n - 1)))

    it "type checks exactly the valid terms, and reports the first failure with its path" $
        withZ3 [] $ \solver -> do
            let signature = division 5 1
                everyTerm = [t | (_, t) <- terms False 5 1]
            mapM_
                ( \term -> do
                    verdict <- refinedTypeCheck solver codec signature term
                    case firstFailure term of
                        Nothing -> verdict `shouldBe` Right (if isQuot term then Quot else Int)
                        Just failure -> verdict `shouldBe` Left failure
                )
                everyTerm

    it "reports a failed precondition at the path of the function" $
        withZ3 [] $ \solver -> do
            verdict <-
                refinedTypeCheck solver codec (division 5 2) (Node "divide" [Node "#4" [], Node "sub" [Node "#1" [], Node "#1" []]])
            verdict `shouldBe` Left (PreconditionFailed (path []) "divide")
            nested <-
                refinedTypeCheck solver codec (division 5 2) (Node "add" [Node "#1" [], Node "sub" [Node "#1" [], Node "#2" []]])
            nested `shouldBe` Left (PreconditionFailed (path [ChildIndex 1]) "sub")

    it "keeps an unknown verdict apart from a failed one" $
        withZ3 [] $ \solver -> do
            -- The divisor has no measure, so the solver can neither prove nor refute the precondition.
            let unmeasured =
                    (division 5 2)
                        { refinedSemantics =
                            [ ("add", FunctionSemantics Nothing Nothing)
                            , ("divide", FunctionSemantics Nothing (Just (binary (\_ b -> b ./= 0))))
                            ]
                        }
            verdict <-
                refinedTypeCheck solver codec unmeasured (Node "divide" [Node "#4" [], Node "add" [Node "#1" [], Node "#1" []]])
            verdict `shouldBe` Left (PreconditionUnknown (path []) "divide")

    it "reports a nesting over the bound and an invalid signature" $
        withZ3 [] $ \solver -> do
            exceeded <-
                refinedTypeCheck solver codec (division 5 1) (Node "add" [Node "add" [Node "#1" [], Node "#1" []], Node "#1" []])
            exceeded `shouldBe` Left (NestingExceeded (path [ChildIndex 0]) "add")
            bad <- refinedGen solver codec (division 5 (-1))
            either Just (const Nothing) bad `shouldBe` Just (Left (NegativeNesting (-1)))
    it "has pool sorts with measures, conditions, and entries without integers" $
        withZ3 [] $ \solver -> do
            result <- refinedGen solver codec (pools 2)
            case result of
                Left err -> expectationFailure (either show show err)
                Right generator -> do
                    let expected = poolTerms True 2
                    sort (either (error . show) id (Gen.values generator)) `shouldBe` sort expected
                    Gen.cardinality generator `shouldBe` Right (Cardinality (fromIntegral (length expected)))
            mapM_
                ( \term -> do
                    verdict <- refinedTypeCheck solver codec (pools 1) term
                    case poolFailure term of
                        Nothing -> verdict `shouldBe` Right (if isLabel term then Quot else Int)
                        Just failure -> verdict `shouldBe` Left failure
                )
                (poolTerms False 1)

    it "keeps the engine ranks of the compiled generator inverse to its terms" $
        withZ3 [] $ \solver -> do
            result <- refinedGen solver codec (division 5 2)
            case result of
                Left err -> expectationFailure (either show show err)
                Right generator -> do
                    let total = either (const 0) (\(Cardinality n) -> n) (Gen.cardinality generator)
                    mapM_
                        ( \rank -> do
                            Gen.unrank generator rank `shouldSatisfy'` either (const False) (const True)
                            (Gen.termAt generator rank >>= Gen.rankOf generator) `shouldBe` Right rank
                        )
                        (everyRank (Cardinality total))
  where
    shouldSatisfy' x p = if p x then pure () else expectationFailure "unrank failed"
    isLabel (Node symbol _) = symbol == "label"
    isQuot (Node symbol _) = symbol == "divide"
    cardinalityOf = either (const (error "no generator")) Gen.cardinality
