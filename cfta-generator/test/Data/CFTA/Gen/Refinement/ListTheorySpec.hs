{-# LANGUAGE OverloadedStrings #-}

{- | One theory of integer lists decides a language of 35 list programs in two
ways: by ground evaluation, and by Z3 with the SMT-LIB text of the theory.

The programs are the chunks @[]@, @[1]@, @[2]@, @[1,2]@, and @[2,1]@, the
reverse of a chunk, and the append of two chunks. The @answer@ production
requires that the value of its program is sorted and a permutation of
@[1,2]@. Both solvers accept the same five programs, with the same ranks.

Z3 runs as one process for all queries ('withZ3Theory'). A second route
starts one process for each query with the complete script
('entailmentScript'). It gives the same verdict for each query.
-}
module Data.CFTA.Gen.Refinement.ListTheorySpec (spec) where

import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import System.Process (readProcessWithExitCode)
import Test.Hspec

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (Satisfies), conjoinConstraints, noConstraint, semanticConstraint)
import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), Term (..))
import Data.CFTA.Index (ClassRank (..), Size)
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Ground (groundEntailment)
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..))
import Data.CFTA.Refinement.SmtLib (entailmentScript)
import Data.CFTA.Refinement.Theory
import Data.CFTA.Refinement.Verdict (Entailment (entails), Verdict (..), entailmentWithBindings, entailsWithBindings)
import Data.CFTA.Refinement.Z3Process (withZ3Theory, withZ3TheoryTimeout)
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol (RefinedSymbol), symbolText, valueName)
import qualified Data.CFTA.Term as Tree

-- | The sort of integer lists.
list :: Sort
list = NamedSort "List" [IntSort]

-- | Split a list: the body for the empty list, then the body for a head @h@ and a tail @t@.
onList :: Name -> Body a -> Body a -> Body a
onList scrutinee empty nonEmpty = Split scrutinee [Branch "nil" [] empty, Branch "cons" ["h", "t"] nonEmpty]

{- | Integer lists with append, reverse, sorted, and a permutation of
@[1,2]@ without quantifiers: @perm(xs, ys)@ removes each element of @xs@
from @ys@.
-}
listTheory :: Theory
listTheory =
    either (error . show) id $
        theory
            [Datatype list [Constructor "nil" [], Constructor "cons" [("head", IntSort), ("tail", list)]]]
            [ function "append" [("xs", list), ("ys", list)] list $
                onList "xs" (Expression (Var "ys")) (Expression (App "cons" [Var "h", App "append" [Var "t", Var "ys"]]))
            , function "reverse" [("xs", list)] list $
                onList "xs" (Expression nil) (Expression (App "append" [App "reverse" [Var "t"], App "cons" [Var "h", nil]]))
            , predicate "below" [("x", IntSort), ("xs", list)] $
                onList "xs" (Expression Top) (Expression (And [Atom Le (Var "x") (Var "h"), Predicate "below" [Var "x", Var "t"]]))
            , predicate "sorted" [("xs", list)] $
                onList "xs" (Expression Top) (Expression (And [Predicate "below" [Var "h", Var "t"], Predicate "sorted" [Var "t"]]))
            , predicate "member" [("x", IntSort), ("xs", list)] $
                onList "xs" (Expression Bottom) (Expression (Or [Atom Eq (Var "x") (Var "h"), Predicate "member" [Var "x", Var "t"]]))
            , function "remove" [("x", IntSort), ("xs", list)] list
                $ onList "xs" (Expression nil)
                $ Expression (Ite (Atom Eq (Var "x") (Var "h")) (Var "t") (App "cons" [Var "h", App "remove" [Var "x", Var "t"]]))
            , predicate "perm" [("xs", list), ("ys", list)]
                $ onList "xs" (Expression (Atom Eq (Var "ys") nil))
                $ Expression (And [Predicate "member" [Var "h", Var "ys"], Predicate "perm" [Var "t", App "remove" [Var "h", Var "ys"]]])
            , predicate "permutation" [("xs", list)] (Expression (Predicate "perm" [Var "xs", listTerm [1, 2]]))
            ]
  where
    nil = App "nil" []
    function name parameters result body = (name, FunctionDefinition parameters result body)
    predicate name parameters body = (name, PredicateDefinition parameters body)

-- | The term of a list.
listTerm :: [Integer] -> Term
listTerm = foldr (\x rest -> App "cons" [Lit x, rest]) (App "nil" [])

-- | The value name of a refinement.
value :: Name
value = fromString valueName

-- | The declarations of the queries: the theory, and the list value of a refinement.
declarations :: [(Name, Sort)]
declarations = theoryDeclarations listTheory <> [(value, list)]

-- | Ground evaluation with the meanings from the theory.
ground :: Entailment
ground = groundEntailment (theoryInterpretations listTheory) Map.empty declarations []

{- | Z3 with the complete SMT-LIB script of each query, one process for each
query, with a time limit in milliseconds.
-}
z3Script :: Int -> Entailment
z3Script milliseconds = entailmentWithBindings $ \bindings antecedent consequent ->
    case entailmentScript listTheory Map.empty declarations [] bindings antecedent consequent of
        Left _ -> pure Unknown
        Right script -> do
            (_, output, errors) <-
                readProcessWithExitCode
                    "z3"
                    ["-in", "-t:" <> show milliseconds, "-T:" <> show (milliseconds `div` 1000 + 10)]
                    (Text.unpack script)
            case lines output of
                ["unsat"] -> pure Yes
                ["sat"] -> pure No
                ["unknown"] -> pure Unknown
                ["timeout"] -> pure Unknown
                _ -> ioError (userError ("z3 rejected a query: " <> output <> errors))

-- | The source states.
data State = ResultState | CandidateState | ChunkState [Integer]
    deriving (Eq, Ord, Show)

-- | The five chunks.
chunks :: [[Integer]]
chunks = [[], [1], [2], [1, 2], [2, 1]]

-- | A production whose symbol states the exact value of its program.
production :: Text -> Term -> [State] -> FTA.Transition State Symbol Constraint
production label exact children =
    FTA.Transition
        (RefinedSymbol (fromString (Text.unpack label)) (Atom Eq (Var value) exact))
        children
        noConstraint

-- | A chunk leaf.
chunk :: [Integer] -> FTA.Transition State Symbol Constraint
chunk xs = production label (listTerm xs) []
  where
    label = Text.pack ("chunk " <> show xs)

-- | A requirement on the value of the program of the answer.
requirement :: Name -> Constraint
requirement name = semanticConstraint $ Satisfies (path [0]) (Predicate name [Var value])

-- | The 35 candidate programs under an answer that requires both predicates.
language :: FTA.PlainFTA State Symbol
language =
    either (error . show) id
        $ FTA.mkFTA ResultState
        $ [ (ResultState, [FTA.Transition "answer" [CandidateState] answer])
          , (CandidateState, map chunk chunks <> reversals <> appends)
          ]
            <> [(ChunkState xs, [chunk xs]) | xs <- chunks]
  where
    answer = conjoinConstraints (requirement "permutation") (requirement "sorted")
    reversals = [production "reverse" (App "reverse" [listTerm xs]) [ChunkState xs] | xs <- chunks]
    appends =
        [ production "append" (App "append" [listTerm xs, listTerm ys]) [ChunkState xs, ChunkState ys]
        | xs <- chunks
        , ys <- chunks
        ]

-- | Record the verdict of each query, in the order of the queries.
recording :: IORef [Verdict] -> Entailment -> Entailment
recording verdicts solver = entailmentWithBindings $ \bindings antecedent consequent -> do
    verdict <- entailsWithBindings solver bindings antecedent consequent
    modifyIORef' verdicts (verdict :)
    pure verdict

-- | The accepted programs up to size four, with their sizes and class ranks.
accepted :: Entailment -> IO [(Size, ClassRank, Text)]
accepted solver = do
    sized <- either (error . show) id <$> Sized.sizedUpTo solver 4 language
    pure
        [(size, ClassRank index, render term) | size <- [1 .. 4], (index, term) <- zip [0 ..] (Sized.termsOfSize sized size)]
  where
    render (Tree.Node symbol children) =
        symbolText symbol <> if null children then "" else "(" <> Text.intercalate ", " (map render children) <> ")"

-- | The five programs whose value is sorted and a permutation of @[1,2]@, with their sizes and class ranks.
expected :: [(Size, ClassRank, Text)]
expected =
    [ (2, ClassRank 0, "answer(chunk [1,2])")
    , (3, ClassRank 0, "answer(reverse(chunk [2,1]))")
    , (4, ClassRank 0, "answer(append(chunk [1,2], chunk []))")
    , (4, ClassRank 1, "answer(append(chunk [1], chunk [2]))")
    , (4, ClassRank 2, "answer(append(chunk [], chunk [1,2]))")
    ]

spec :: Spec
spec = describe "a theory of integer lists" $ do
    it "decides the 35 programs by ground evaluation" $
        accepted ground >>= (`shouldBe` expected)

    it "decides the 35 programs with one Z3 process" $
        withZ3Theory listTheory declarations [] accepted >>= (`shouldBe` expected)

    it "decides the 35 programs with one Z3 process for each query" $
        accepted (z3Script 10000) >>= (`shouldBe` expected)

    it "gives the same verdict for each query with one process and with a process for each query" $ do
        persistent <- newIORef []
        perQuery <- newIORef []
        _ <- withZ3Theory listTheory declarations [] (accepted . recording persistent)
        _ <- accepted (recording perQuery (z3Script 10000))
        verdicts <- readIORef persistent
        length verdicts `shouldBe` 45
        readIORef perQuery >>= (`shouldBe` verdicts)

    it "does not decide reverse(reverse(xs)) == xs for all lists" $ do
        let involution = Forall [("xs", list)] (Atom Eq (App "reverse" [App "reverse" [Var "xs"]]) (Var "xs"))
        entails ground Top involution >>= (`shouldBe` Unknown)
        withZ3TheoryTimeout 2000 listTheory declarations [] $ \z3 ->
            entails z3 Top involution `shouldThrow` (== TimeLimitReached 2000)
