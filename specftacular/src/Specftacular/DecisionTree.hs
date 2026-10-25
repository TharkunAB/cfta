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

import Control.Concurrent (forkIO, getNumCapabilities, killThread)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Exception (SomeException, mask, onException, throwIO, try)
import Control.Monad (when)
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
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
insert equal cases t eval = insertWith Nothing (const (const False)) equal cases t (PerCase eval)

{- | Insert a term, but skip the test schedule when the predicate proves
that it equals the representative. Branch comparisons still select the
representative. New equalities still use the complete test schedule.
With Just n, a comparison at a leaf tests the cases after the first n in
parallel chunks, one for each capability. The first chunk in order that does
not agree decides, so the result is the same as in order.
-}
insertWith ::
    Maybe Int ->
    (Term -> Term -> Bool) ->
    (Value -> Value -> IO (Maybe Bool)) ->
    [Case] ->
    Term ->
    Evaluator ->
    DecisionTree ->
    IO Inserted
insertWith parallelAfter known equal cases t eval = go
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
        | Nothing <- parallelAfter = maybe (EqualTo y) decide <$> firstDifference (pure False) cases
        | Just sequential <- parallelAfter = do
            capabilities <- getNumCapabilities
            let (first, rest) = splitAt sequential cases
            prefix <- firstDifference (pure False) first
            case prefix of
                Just found -> pure (decide found)
                Nothing
                    | capabilities <= 1 || null rest -> maybe (EqualTo y) decide <$> firstDifference (pure False) rest
                    | otherwise -> do
                        -- A chunk stops when a chunk before it has found a
                        -- difference, because its result cannot decide then.
                        earliest <- newIORef (maxBound :: Int)
                        let chunk i cs = do
                                found <- firstDifference ((< i) <$> readIORef earliest) cs
                                when (isJust found) $ atomicModifyIORef' earliest (\j -> (min i j, ()))
                                pure found
                        found <- inParallel (zipWith chunk [0 ..] (chunks capabilities rest))
                        either throwIO (pure . maybe (EqualTo y) decide) (firstOf found)
      where
        -- The first case on which the two terms do not agree, with the values
        -- that the comparison forced, unless the action stops it first.
        firstDifference _ [] = pure Nothing
        firstDifference stopped (tc : more) = do
            stop <- stopped
            if stop
                then pure Nothing
                else do
                    let w = evaluateWith evalY tc
                        v = evaluateWith eval tc
                    e <- equal w v
                    case e of
                        Just True -> firstDifference stopped more
                        _ -> pure (Just (tc, w, v, e))
        decide (_, _, _, Nothing) = Untested
        decide (tc, w, v, _) = Distinct $ Branch tc [(w, Leaf y evalY), (v, Leaf t eval)]
        firstOf [] = Right Nothing
        firstOf (Left exception : _) = Left exception
        firstOf (Right Nothing : more) = firstOf more
        firstOf (Right found : _) = Right found

-- | Split a list into at most n chunks of about equal length, in order.
chunks :: Int -> [a] -> [[a]]
chunks n xs = go xs
  where
    size = max 1 ((length xs + n - 1) `div` n)
    go [] = []
    go ys = let (c, more) = splitAt size ys in c : go more

-- | Run the actions in their own threads, and give their results in order. An exception of the caller stops them.
inParallel :: [IO a] -> IO [Either SomeException a]
inParallel actions = mask $ \restore -> do
    started <-
        mapM
            (\action -> do var <- newEmptyMVar; thread <- forkIO (try (restore action) >>= putMVar var); pure (thread, var))
            actions
    restore (mapM (takeMVar . snd) started) `onException` mapM_ (killThread . fst) started

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
