{-# LANGUAGE OverloadedStrings #-}

-- | Compile list programs whose results are sorted permutations of @[1,2]@.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.Char (ord)
import Data.List (sort, sortOn)
import Data.String (fromString)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), Term (..), renderFormula)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Index (Cardinality (..), everyRank)
import qualified Data.CFTA.Lean as Lean
import Data.CFTA.Refinement (noConstraint)
import Data.CFTA.Refinement.Expression (Expr, fromExpr, toExpr)
import Data.CFTA.Refinement.Verdict (Entailment (entails), Verdict (..))
import Data.CFTA.Symbol (valueName)

-- | A list program. 'Answer' applies the required result refinement.
data Program
    = Chunk [Int]
    | Append Program Program
    | Reverse Program
    | Answer Program
    deriving (Eq, Show)

-- | Evaluate a program independently of its logical refinement.
evaluate :: Program -> [Int]
evaluate program = case program of
    Chunk xs -> xs
    Append left right -> evaluate left <> evaluate right
    Reverse inner -> reverse (evaluate inner)
    Answer inner -> evaluate inner

-- | The value type of every program in the logical interpretation.
listInt :: Sort
listInt = NamedSort "List" [IntSort]

-- | List operations use Lean definitions. The interval predicate is portable.
theory :: Lean.Theory
theory =
    [ ("List", Lean.TypeConstructor 1 "List")
    , ("nil", Lean.Function [] listInt "([] : List Int)")
    , ("cons", Lean.Function [IntSort, listInt] listInt "List.cons")
    , ("append", Lean.Function [listInt, listInt] listInt "List.append")
    , ("reverse", Lean.Function [listInt] listInt "List.reverse")
    , ("sorted", Lean.Predicate [listInt] "(fun xs : List Int => xs.Pairwise (· ≤ ·))")
    , ("permutation", Lean.Predicate [listInt] "(fun xs : List Int => xs.Perm [1,2])")
    ,
        ( "between"
        , Lean.Defined
            [("x", IntSort), ("low", IntSort), ("high", IntSort)]
            (And [Atom Ge (Var "x") (Var "low"), Atom Le (Var "x") (Var "high")])
        )
    ]

-- | Logical program values are lists.
listDeclarations :: [(Name, Sort)]
listDeclarations = [(fromString valueName, listInt)]

-- | The interval example has an integer domain that both solvers support.
scalarDeclarations :: [(Name, Sort)]
scalarDeclarations = [("x", IntSort)]

-- | Encode a concrete list with the same constructors used by the theory.
listTerm :: [Int] -> Term
listTerm = foldr (\element rest -> App "cons" [Lit (toInteger element), rest]) (App "nil" [])

-- | Require a sorted list with the same elements and multiplicities as @[1,2]@.
solution :: Expr -> Formula
solution value =
    And
        [ Predicate "sorted" [fromExpr value]
        , Predicate "permutation" [fromExpr value]
        ]

-- | The five leaf values from which candidate programs are constructed.
chunks :: [[Int]]
chunks = [[], [1], [2], [1, 2], [2, 1]]

-- | State every leaf's exact list value in its refinement.
chunkSource :: LTAGen.LTAGen Program
chunkSource =
    LTAGen.oneof
        [ LTAGen.leaf (Chunk xs) (fromString ("chunk " <> show xs)) $
            \value -> Atom Eq (fromExpr value) (listTerm xs)
        | xs <- chunks
        ]

-- | Interpret the result of a reverse constructor as a Lean list expression.
reverseMeasure :: Expr -> Expr
reverseMeasure value = toExpr (App "reverse" [fromExpr value])

-- | Interpret the result of an append constructor as a Lean list expression.
appendMeasure :: Expr -> Expr -> Expr
appendMeasure left right = toExpr (App "append" [fromExpr left, fromExpr right])

-- | Construct 35 programs, then require the result refinement at the root.
language :: LTAGen.LTAGen Program
language =
    LTAGen.measured "answer" solution (id :: Expr -> Expr) $
        Answer
            <$> LTAGen.oneof
                [ chunkSource
                , LTAGen.measuredNode "reverse" noConstraint reverseMeasure (Reverse <$> chunkSource)
                , LTAGen.measuredNode "append" noConstraint appendMeasure (Append <$> chunkSource <*> chunkSource)
                ]

-- | Enumerate the candidate syntax independently of the generator.
candidates :: [Program]
candidates =
    map Answer $
        map Chunk chunks
            <> [Reverse (Chunk xs) | xs <- chunks]
            <> [Append (Chunk xs) (Chunk ys) | xs <- chunks, ys <- chunks]

-- | Check the result with Haskell list operations.
accepted :: Program -> Bool
accepted program =
    let result = evaluate program
     in result == sort result && sort result == [1, 2]

-- | Report construction errors without dropping candidates.
rightOrFail :: (Show err) => Either err a -> IO a
rightOrFail = either (fail . show) pure

-- | Require the exact solver verdict, including a checked negative result.
expectVerdict :: String -> Verdict -> IO Verdict -> IO ()
expectVerdict label expected query = do
    actual <- query
    unless (actual == expected) $
        fail (label <> ": expected " <> show expected <> ", got " <> show actual)
    putStrLn (label <> ": " <> show actual)

-- | Exercise exact scalar lowering and the refusal to approximate native lists.
checkSolvers :: Entailment -> Entailment -> IO ()
checkSolvers lean lowered = do
    let interval = Predicate "between" [Var "x", Lit 0, Lit 3]
        nonnegative = Atom Ge (Var "x") (Lit 0)
        native = Predicate "sorted" [listTerm [2, 1]]
    portable <- rightOrFail (Lean.lower theory scalarDeclarations interval)
    putStrLn ("lowered interval: " <> renderFormula portable)
    expectVerdict "interval via Z3" Yes (entails lowered interval nonnegative)
    expectVerdict "interval via Kimina" Yes (entails lean interval nonnegative)
    case Lean.lower theory scalarDeclarations native of
        Left reason -> putStrLn ("native list lowering refused: " <> reason)
        Right unexpected -> fail ("native list was lowered: " <> show unexpected)
    expectVerdict "native list via lowering" Unknown (entails lowered Top native)
    expectVerdict "unsorted list via Kimina" No (entails lean Top native)
    let xs = Var "xs"
        involution = Forall [("xs", listInt)] (Atom Eq (App "reverse" [App "reverse" [xs]]) xs)
    expectVerdict "reverse twice on any list" Yes (entails lean Top involution)

-- | Check the accepted syntax, every rank, and reproducible sampling.
checkLanguage :: Entailment -> IO ()
checkLanguage solver = do
    compiled <- LTAGen.compileWith solver language >>= rightOrFail
    actual <- rightOrFail (LTAGen.values compiled)
    total <- rightOrFail (LTAGen.cardinality compiled)
    let expected = filter accepted candidates
        ranks = everyRank total
    unless (length candidates == 35 && length expected == 5 && total == Cardinality 5) $
        fail ("unexpected candidate or accepted count: " <> show (length candidates, length expected, total))
    unless (sortOn show actual == sortOn show expected) $
        fail ("the LTA and Haskell evaluator disagree: " <> show (actual, expected))
    unless (actual == expected) $
        fail ("the rank order differs from the source order: " <> show actual)
    putStrLn ("candidates: " <> show (length candidates) <> "; accepted: " <> show total)
    forM_ (zip ranks actual) $ \(rank, program) -> do
        term <- rightOrFail (LTAGen.termAt compiled rank)
        recovered <- rightOrFail (LTAGen.rankOf compiled term)
        decoded <- rightOrFail (LTAGen.unrank compiled rank)
        unless (recovered == rank && decoded == program && accepted decoded) $
            fail ("rank round trip failed: " <> show rank)
        putStrLn (show rank <> ": " <> show program <> " => " <> show (evaluate program))
    let sample = QC.vectorOf 32 (LTAGen.toGenWithRank compiled)
        first = unGen sample (mkQCGen 20261020) 30
        repeated = unGen sample (mkQCGen 20261020) 30
    unless (first == repeated) $
        fail "a fixed sampling seed gave different results"
    forM_ first $ \(LTAGen.RankedValue rank program) -> do
        decoded <- rightOrFail (LTAGen.unrank compiled rank)
        unless (decoded == program && accepted program) $
            fail ("a sampled program failed replay: " <> show (rank, program))
    putStrLn ("sample ranks: " <> show [rank | LTAGen.RankedValue rank _ <- first])
    putStrLn ("sample checksum: " <> show (checksum (show first)))

-- | A deterministic checksum of the printed sample, for separate process runs.
checksum :: String -> Integer
checksum = foldl' (\acc character -> (33 * acc + toInteger (ord character)) `mod` 2147483647) 5381

-- | Run the example against the local Kimina service and the exact Z3 lowering.
main :: IO ()
main = do
    Lean.withTheory Lean.defaultOptions theory scalarDeclarations [] $ \lean ->
        Lean.withLowering theory scalarDeclarations [] $ \lowered ->
            checkSolvers lean lowered
    Lean.withTheory Lean.defaultOptions theory listDeclarations [] $ \lean ->
        Lean.withLowering theory listDeclarations [] $ \lowered ->
            checkLanguage (Lean.fallback lowered lean)
