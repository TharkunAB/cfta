{- | Decision trees of terms, as in QuickSpec. A tree holds the
representatives of the terms of one type. Each branch stores a test case
that separates representatives. A leaf stores an evaluator instead of a
list of values. Two terms are equal when their values agree on all test
cases.
-}
module Specftacular.DecisionTree (
    DecisionTree,
    Inserted (..),
    empty,
    leaf,
    insert,
    size,
) where

import Specftacular.Types (Term, TestCase, Value)

-- | A decision tree of terms.
data DecisionTree
    = -- | No representatives.
      Empty
    | -- | A representative and its evaluator.
      Leaf Term (TestCase -> Value)
    | -- | A test case and the children for its distinct values.
      Branch TestCase [(Value, DecisionTree)]

-- | The result of an insertion.
data Inserted
    = -- | The term is a new representative, in this tree.
      Distinct DecisionTree
    | -- | The term has the values of this representative on all test cases.
      EqualTo Term
    | -- | A comparison threw, so the term cannot be tested.
      Untested

-- | The tree with no representatives.
empty :: DecisionTree
empty = Empty

-- | The tree with one representative and its evaluator.
leaf :: Term -> (TestCase -> Value) -> DecisionTree
leaf = Leaf

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
    [TestCase] ->
    Term ->
    (TestCase -> Value) ->
    DecisionTree ->
    IO Inserted
insert equal cases t eval = go
  where
    go Empty = return (Distinct (Leaf t eval))
    go (Branch tc children) = find [] children
      where
        v = eval tc
        find before [] = return $ Distinct $ Branch tc $ reverse before ++ [(v, Leaf t eval)]
        find before (child@(w, sub) : after) = do
            e <- equal w v
            case e of
                Nothing -> return Untested
                Just False -> find (child : before) after
                Just True ->
                    below (\sub' -> Branch tc (reverse before ++ (w, sub') : after))
                        <$> go sub
    go (Leaf y evalY) = compareCases cases
      where
        compareCases [] = return (EqualTo y)
        compareCases (tc : rest) = do
            let w = evalY tc
                v = eval tc
            e <- equal w v
            case e of
                Nothing -> return Untested
                Just False -> return $ Distinct $ Branch tc [(w, Leaf y evalY), (v, Leaf t eval)]
                Just True -> compareCases rest

-- | Put the tree of a new representative in its place in the parent.
below :: (DecisionTree -> DecisionTree) -> Inserted -> Inserted
below place (Distinct sub) = Distinct (place sub)
below _ result = result
