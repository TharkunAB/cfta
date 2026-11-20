{-# LANGUAGE OverloadedStrings #-}

-- | Discover a function equation on an integer interval and apply it within that interval.
module Main (main) where

import Control.Monad (unless)
import qualified Data.CFTA.Gen.Refinement as LTA
import Data.CFTA.Refinement.Symbolic (Symbolic (..), (.&&))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isNothing)
import qualified Data.Set as Set
import qualified Specftacular.DecisionTree as Tree
import qualified Specftacular.FiniteLaw as Finite
import Specftacular.Types (Case (..), Term, TestCase (ValidationCase), apply, toValue, valuesEqual)
import qualified Specftacular.Types as Spec

{- | Compare abs with id on every integer in the closed interval. A discovered
rewrite checks the same interval at each use. An empty interval gives no evidence.
-}
discover :: Integer -> Integer -> IO ([Integer], Maybe (Integer -> Maybe Integer))
discover lower upper = do
    compiled <- LTA.compile (LTA.every `LTA.satisfying` inRange)
    case LTA.values compiled of
        Left LTA.EmptyGenerator -> pure ([], Nothing)
        Left err -> fail (show err)
        Right [] -> pure ([], Nothing)
        Right inputs -> do
            let cases = zipWith (\i x -> Case (ValidationCase i 0) (Map.singleton "x" (toValue x))) [0 ..] inputs
            found <- Tree.insertWith Nothing (==) equal cases absolute (observe abs) (Tree.leafWith identity (observe replacement))
            case found of
                Tree.EqualTo term | term == identity -> do
                    law <- either fail pure (checkScope inputs)
                    pure (inputs, Just (Finite.applyAt law . Map.singleton "x"))
                Tree.Distinct _ -> pure (inputs, Nothing)
                _ -> fail "could not compare abs and id"
  where
    inRange :: (Symbolic e) => e -> Truth e
    inRange x = fromInteger lower .<= x .&& x .<= fromInteger upper
    replacement = id :: Integer -> Integer
    identity, absolute :: Term
    identity = call "id"
    absolute = call "abs"
    call name = Spec.Term "app" [num, Spec.Term name [endo], Spec.Term "x" [num]]
    num = Spec.Term "Integer" []
    endo = Spec.Term "->" [Spec.Term "(->)" [], num, num]
    -- Include negative controls and every result of the two functions.
    checkScope inputs = do
        let values = Set.fromList (inputs ++ map negate inputs)
            functions = [(0, replacement), (1, abs)]
            carriers = Map.fromList [(num, Map.fromSet id values), (endo, Map.fromList [(i, i) | (i, _) <- functions])]
            constant i = Finite.Operation [] endo (Map.singleton [] i)
            rows = Map.fromList [([i, x], f x) | (i, f) <- functions, x <- Set.toList values]
            ops = Map.fromList [("id", constant 0), ("abs", constant 1), ("app", Finite.Operation [endo, num] num rows)]
        theory <- Finite.finiteTheory carriers ops
        Finite.proveOn theory (Map.singleton "x" num) (fmap inRange . Map.lookup "x") absolute identity
    equal = valuesEqual (toValue ((==) :: Integer -> Integer -> Bool))
    observe :: (Integer -> Integer) -> Tree.Evaluator
    observe f = Tree.Evaluator Map.empty (\values -> apply (toValue f) (values Map.! "x"))

-- | Check the discovered rewrite, both interval boundaries, and a domain that distinguishes the functions.
main :: IO ()
main = do
    (nonnegative, law) <- discover 0 4
    rewrite <- maybe (fail "missing equation on [0,4]") pure law
    unless (nonnegative == [0 .. 4] && map rewrite nonnegative == map (Just . abs) nonnegative) $
        fail "the guarded rewrite changed a result on [0,4]"
    unless (isNothing (rewrite (-1)) && isNothing (rewrite 5)) $
        fail "the rewrite escaped its interval"
    (signed, unrestrictedLaw) <- discover (-4) 4
    unless (signed == [-4 .. 4] && isNothing unrestrictedLaw) $
        fail "the signed inputs failed to distinguish abs and id"
    let applyAt x = fromMaybe (abs x) (rewrite x)
    unless (map applyAt signed == map abs signed) $
        fail "applying the guarded rewrite changed a value"
    (empty, vacuousLaw) <- discover 1 0
    unless (null empty && isNothing vacuousLaw) $
        fail "an empty interval produced a rewrite"
    putStrLn $ "abs x == id x on " ++ show nonnegative ++ " (" ++ show (length nonnegative) ++ " inputs)"
    let witnesses = filter (\x -> abs x /= x) signed
    putStrLn $ "Signed control: abs and id differ on " ++ show witnesses ++ " of " ++ show (length signed) ++ " inputs"
    putStrLn $ "x = -1: rewrite = " ++ show (rewrite (-1)) ++ ", result = " ++ show (applyAt (-1))
    putStrLn $ "x = 5: rewrite = " ++ show (rewrite 5) ++ " (outside the observed interval)"
