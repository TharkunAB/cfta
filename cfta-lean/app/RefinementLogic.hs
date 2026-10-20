{-# LANGUAGE OverloadedStrings #-}

-- | Save and reload a language of sorted list programs with its Lean theory.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.Char (ord)
import Data.List (sort, sortOn)
import qualified Data.Map.Strict as Map
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.Environment (getArgs)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Text.Read (readEither)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (Satisfies), noConstraint, semanticConstraint)
import qualified Data.CFTA.Document as Document
import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), Term (..), renderFormula)
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size)
import qualified Data.CFTA.Language as Language
import qualified Data.CFTA.Lean as Lean
import Data.CFTA.Lean.Serialization (Context (..), Snapshot (..), parseSnapshot, printSnapshot)
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Verdict (Entailment (entails), Verdict (..))
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol (RefinedSymbol), symbolText, valueName)
import qualified Data.CFTA.Term as Tree

-- | The source states. Their identities and order survive serialization.
data State = ResultState | CandidateState | ChunkState [Int]
    deriving (Eq, Ord, Show, Read)

-- | A list program. 'Answer' applies the required result refinement.
data Program = Chunk [Int] | Append Program Program | Reverse Program | Answer Program
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

-- | The five leaf values from which candidate programs are constructed.
chunks :: [[Int]]
chunks = [[], [1], [2], [1, 2], [2, 1]]

-- | Encode a list with the constructors stored in the theory.
listTerm :: [Int] -> Term
listTerm = foldr (\element rest -> App "cons" [Lit (toInteger element), rest]) (App "nil" [])

-- | Store the complete logical value in a symbol refinement.
exactSymbol :: Text -> Term -> Symbol
exactSymbol label value = RefinedSymbol (fromString $ Text.unpack label) (Atom Eq (Var $ fromString valueName) value)

-- | A named source production without additional facts.
production :: Text -> Symbol -> [State] -> FTA.Transition State Symbol Document.Annotation
production name symbol children = FTA.Transition symbol children (Document.Annotation name Map.empty)

-- | A leaf stores its concrete list and its decoder label.
chunkProduction :: [Int] -> FTA.Transition State Symbol Document.Annotation
chunkProduction xs = production label (exactSymbol label $ listTerm xs) []
  where
    label = Text.pack ("chunk " <> show xs)

-- | Require one predicate of the child list at the answer constructor.
resultFact :: Name -> Constraint
resultFact predicate = semanticConstraint $ Satisfies (path [0]) (Predicate predicate [Var $ fromString valueName])

{- | Store all 35 candidates before solving their result requirements.
The operation productions specialize their logical values to their children.
The snapshot contains data rather than generator measure functions.
-}
sourceLanguage :: IO (Language.Language State)
sourceLanguage = do
    source <- rightOrFail $ Document.mkDocument ResultState rows
    rightOrFail
        $ Language.update (Language.fromDocument source)
        $ Language.require (Language.at ResultState "answer") "sorted" (resultFact "sorted")
            <> Language.require (Language.at ResultState "answer") "permutation" (resultFact "permutation")
  where
    rows =
        [ (ResultState, [production "answer" "answer" [CandidateState]])
        , (CandidateState, candidateProductions)
        ]
            <> [(ChunkState xs, [chunkProduction xs]) | xs <- chunks]
    numbered = zip [0 :: Int ..] chunks
    candidateProductions =
        map chunkProduction chunks
            <> [ production
                    (Text.pack $ "reverse " <> show index)
                    (exactSymbol "reverse" $ App "reverse" [listTerm xs])
                    [ChunkState xs]
               | (index, xs) <- numbered
               ]
            <> [ production
                    (Text.pack $ "append " <> show left <> " " <> show right)
                    (exactSymbol "append" $ App "append" [listTerm xs, listTerm ys])
                    [ChunkState xs, ChunkState ys]
               | (left, xs) <- numbered
               , (right, ys) <- numbered
               ]

-- | Construct the complete source and solver context for a new snapshot.
initialSnapshot :: IO (Snapshot State)
initialSnapshot = Snapshot (Context theory listDeclarations []) <$> sourceLanguage

-- | Enumerate the candidate syntax independently of the stored source.
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

-- | Decode constructor syntax without restoring a Haskell closure.
decodeProgram :: Tree.Term Symbol -> Either String Program
decodeProgram (Tree.Node symbol children) = case (symbolText symbol, children) of
    ("answer", [inner]) -> Answer <$> decodeProgram inner
    ("reverse", [inner]) -> Reverse <$> decodeProgram inner
    ("append", [left, right]) -> Append <$> decodeProgram left <*> decodeProgram right
    (label, []) | Just value <- Text.stripPrefix "chunk " label -> Chunk <$> readEither (Text.unpack value)
    _ -> Left ("unknown program constructor or arity: " <> show (symbolText symbol, length children))

-- | Report malformed source and query failures without dropping candidates.
rightOrFail :: (Show err) => Either err a -> IO a
rightOrFail = either (fail . show) pure

-- | Require the exact solver verdict, including a checked negative result.
expectVerdict :: String -> Verdict -> IO Verdict -> IO ()
expectVerdict label expected query = do
    actual <- query
    unless (actual == expected) $ fail (label <> ": expected " <> show expected <> ", got " <> show actual)
    putStrLn (label <> ": " <> show actual)

-- | Show portable lowering separately from the list-valued source context.
checkSolvers :: Context -> Entailment -> Entailment -> IO ()
checkSolvers context lean lowered = do
    let interval = Predicate "between" [Var "x", Lit 0, Lit 3]
        native = Predicate "sorted" [listTerm [2, 1]]
    portable <- rightOrFail $ Lean.lower (contextTheory context) [("x", IntSort)] interval
    putStrLn ("lowered interval: " <> renderFormula portable)
    Lean.withLowering (contextTheory context) [("x", IntSort)] [] $ \scalar ->
        expectVerdict "interval via Z3" Yes (entails scalar interval $ Atom Ge (Var "x") (Lit 0))
    case Lean.lower (contextTheory context) [] native of
        Left reason -> putStrLn ("native list lowering refused: " <> reason)
        Right _ -> fail "native list semantics were lost during lowering"
    expectVerdict "native list via lowering" Unknown (entails lowered Top native)
    expectVerdict "unsorted list via Kimina" No (entails lean Top native)
    let xs = Var "xs"
        involution = Forall [("xs", listInt)] (Atom Eq (App "reverse" [App "reverse" [xs]]) xs)
    expectVerdict "reverse twice on any list" Yes (entails lean Top involution)

-- | All source programs have at most four constructor nodes.
maximumSize :: Size
maximumSize = 4

-- | Check the direct graph's accepted terms, inverse ranks, and uniform samples.
checkLanguage :: Entailment -> Language.Language State -> IO ()
checkLanguage solver source = do
    let graph = Language.compileGraph source
        sizes = [1 .. maximumSize]
    -- This separate count ignores requirements only to count source candidates.
    unconstrained <- rightOrFail $ Sized.sized (FTA.mapConstraints (const noConstraint) graph)
    sourcePrograms <- rightOrFail $ traverse decodeProgram $ concatMap (Sized.termsOfSize unconstrained) sizes
    unless (sortOn show sourcePrograms == sortOn show candidates && length sourcePrograms == 35) $
        fail "the saved source does not contain the 35 expected candidate programs"
    sized <- Sized.sizedUpTo solver maximumSize graph >>= rightOrFail
    let entries = [(size, ClassRank index, term) | size <- sizes, (index, term) <- zip [0 ..] (Sized.termsOfSize sized size)]
        total = sum [Sized.countOfSize sized size | size <- sizes]
        expected = filter accepted candidates
    actual <- rightOrFail $ traverse (decodeProgram . (\(_, _, term) -> term)) entries
    unless (sortOn show actual == sortOn show expected && total == Cardinality 5 && length entries == 5) $
        fail ("the saved LTA and Haskell evaluator disagree: " <> show (actual, expected, total))
    putStrLn ("candidates: " <> show (length sourcePrograms) <> "; accepted: " <> show total)
    forM_ (zip [0 :: Int ..] entries) $ \(rank, (size, classRank, term)) -> do
        unless
            ( Sized.rankOfSize sized term == Just (size, classRank)
                && Sized.unrankOfSize sized size classRank == Just term
            )
            $ fail ("structural rank round trip failed: " <> show (size, classRank))
        program <- rightOrFail (decodeProgram term)
        putStrLn
            ( show rank
                <> " (size "
                <> show size
                <> ", class "
                <> show classRank
                <> "): "
                <> show program
                <> " => "
                <> show (evaluate program)
            )
        putStrLn ("  term: " <> show term)
    let sampleRanks = unGen (QC.vectorOf 32 $ QC.chooseInt (0, length entries - 1)) (mkQCGen 20261020) 30
    samples <- traverse (sampleAt sized entries) sampleRanks
    putStrLn ("sample ranks: " <> show sampleRanks)
    putStrLn ("sample checksum: " <> show (checksum $ show samples))
  where
    sampleAt sized entries rank = do
        let (size, classRank, expected) = entries !! rank
        term <- maybe (fail "a sampled rank is absent") pure (Sized.unrankOfSize sized size classRank)
        program <- rightOrFail (decodeProgram term)
        unless (term == expected && accepted program && Sized.rankOfSize sized term == Just (size, classRank)) $
            fail ("a sampled program failed replay: " <> show rank)
        pure (rank, size, classRank, program)

-- | A deterministic checksum for comparison across separate processes.
checksum :: String -> Integer
checksum = foldl' (\acc character -> (33 * acc + toInteger (ord character)) `mod` 2147483647) 5381

-- | Use only the loaded source and loaded logical context for all language queries.
reportSnapshot :: Snapshot State -> IO ()
reportSnapshot snapshot = do
    putStrLn ("snapshot checksum: " <> show (checksum $ Text.unpack $ printSnapshot snapshot))
    let context = snapshotContext snapshot
    Lean.withTheory Lean.defaultOptions (contextTheory context) (contextDeclarations context) (contextAssumptions context) $ \lean ->
        Lean.withLowering (contextTheory context) (contextDeclarations context) (contextAssumptions context) $ \lowered -> do
            checkSolvers context lean lowered
            checkLanguage (Lean.fallback lowered lean) (snapshotLanguage snapshot)

-- | Read and validate the complete saved snapshot.
loadSnapshot :: FilePath -> IO (Snapshot State)
loadSnapshot file = Text.readFile file >>= rightOrFail . parseSnapshot

-- | Dump and reload before reporting, or report a snapshot from another process.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["dump", file] -> do
            original <- initialSnapshot
            Text.writeFile file (printSnapshot original)
            restored <- loadSnapshot file
            unless (restored == original) $ fail "the saved snapshot did not round trip exactly"
            reportSnapshot restored
        ["reload", file] -> loadSnapshot file >>= reportSnapshot
        _ -> fail "usage: refinement-logic-spike dump FILE | refinement-logic-spike reload FILE"
