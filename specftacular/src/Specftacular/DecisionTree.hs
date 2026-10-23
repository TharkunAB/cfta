{- | Decision trees of terms, as in QuickSpec. A tree holds the
representatives of the terms of one type. Each branch stores a test case
that separates representatives. A leaf stores an evaluator instead of a
list of values. Two terms are equal when their values agree on all test
cases.
-}
module Specftacular.DecisionTree (
    DecisionTree,
    Evaluator (Evaluator),
    Inserted (..),
    empty,
    leaf,
    leafWith,
    insert,
    insertWith,
    size,
) where

import qualified Data.Map.Strict as Map
import Specftacular.Types (Case (..), Sig, Term, TestCase, Value, VarVals, testCaseValues)

{- | A term evaluator and the generators of its variables, or an evaluator
on the test case. A representative from an earlier phase can have
variables that the test cases of the current phase do not have.
-}
data Evaluator
    = Evaluator Sig (VarVals -> Value)
    | PerCase (TestCase -> Value)

-- | A decision tree of terms.
data DecisionTree
    = -- | No representatives.
      Empty
    | -- | A representative and its evaluator.
      Leaf Term Evaluator
    | -- | A test case and the children for its distinct values.
      Branch Case [(Value, DecisionTree)]

-- | The result of an insertion.
data Inserted
    = -- | The term is a new representative, in this tree.
      Distinct DecisionTree
    | -- | Tests or the supplied predicate equate the term with this representative.
      EqualTo Term
    | -- | A comparison threw, so the term cannot be tested.
      Untested

-- | The tree with no representatives.
empty :: DecisionTree
empty = Empty

-- | The tree with one representative and its evaluator.
leaf :: Term -> (TestCase -> Value) -> DecisionTree
leaf t eval = Leaf t (PerCase eval)

-- | A representative with explicit generators for shared test inputs.
leafWith :: Term -> Evaluator -> DecisionTree
leafWith = Leaf

-- | The number of representatives in a tree.
size :: DecisionTree -> Int
size Empty = 0
size (Leaf _ _) = 1
size (Branch _ children) = sum (map (size . snd) children)

{- | Insert a term and its evaluator into a tree. Compare a candidate with
a representative on the complete test schedule. The first counterexample
creates a branch. Retain values only for test cases that separate terms.
The equality gives Nothing when a comparison throws.
-}
insert ::
    (Value -> Value -> IO (Maybe Bool)) ->
    [Case] ->
    Term ->
    (TestCase -> Value) ->
    DecisionTree ->
    IO Inserted
insert equal cases t eval = insertWith (const (const False)) equal cases t (PerCase eval)

{- | Insert a term, but skip the test schedule when the predicate proves
that it equals the representative. Branch comparisons still select the
representative. New equalities still use the complete test schedule.
-}
insertWith ::
    (Term -> Term -> Bool) ->
    (Value -> Value -> IO (Maybe Bool)) ->
    [Case] ->
    Term ->
    Evaluator ->
    DecisionTree ->
    IO Inserted
insertWith known equal cases t eval = go
  where
    go Empty = return (Distinct (Leaf t eval))
    go (Branch tc children) = find [] children
      where
        v = evaluateWith eval tc
        find before [] = return $ Distinct $ Branch tc $ reverse before ++ [(v, Leaf t eval)]
        find before (child@(w, sub) : after) = do
            e <- equal w v
            case e of
                Nothing -> return Untested
                Just False -> find (child : before) after
                Just True ->
                    below (\sub' -> Branch tc (reverse before ++ (w, sub') : after))
                        <$> go sub
    go (Leaf y evalY)
        | known t y = return (EqualTo y)
        | otherwise = compareCases cases
      where
        compareCases [] = return (EqualTo y)
        compareCases (tc : rest) = do
            let w = evaluateWith evalY tc
                v = evaluateWith eval tc
            e <- equal w v
            case e of
                Nothing -> return Untested
                Just False -> return $ Distinct $ Branch tc [(w, Leaf y evalY), (v, Leaf t eval)]
                Just True -> compareCases rest

-- | Evaluate on the values of a test case, or with a caller's case evaluator.
evaluateWith :: Evaluator -> Case -> Value
evaluateWith (Evaluator required eval) testcase = eval (inputs required testcase)
evaluateWith (PerCase eval) testcase = eval (caseTest testcase)

{- | The values of the variables of an evaluator on a test case: the shared
values of the case, and the values that the generators of the evaluator
give for the variables that the case does not have.
-}
inputs :: Sig -> Case -> VarVals
inputs required testcase
    | Map.null missing = caseValues testcase
    | otherwise = caseValues testcase `Map.union` testCaseValues missing (caseTest testcase)
  where
    missing = required `Map.difference` caseValues testcase

-- | Put the tree of a new representative in its place in the parent.
below :: (DecisionTree -> DecisionTree) -> Inserted -> Inserted
below place (Distinct sub) = Distinct (place sub)
below _ result = result
