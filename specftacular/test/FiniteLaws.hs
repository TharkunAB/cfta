{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Monad (forM_, unless)
import Data.Either (isLeft, isRight)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import qualified Data.Set as Set

import qualified Data.CFTA.EGraph as EG
import Data.CFTA.Symbol (Symbol)
import qualified Specftacular.FiniteLaw as F
import Specftacular.Types (Term, pattern Term)

-- | Check the boundary between observations, scoped laws, and rewrites.
main :: IO ()
main = do
    let bool = Term "Bool" []
        pair = Term "Pair" []
        num = Term "Signed3" []
        atom sort name = Term name [sort]
        app sort name arg = Term name [sort, arg]
        p = atom pair "p"
        q = atom pair "q"
        x = atom num "x"
        apply = app bool "fst"
        classes = Map.fromList [(pair, Map.fromList (zip [0 .. 3] [0, 0, 1, 1])), (bool, Map.fromList [(0, 0), (1, 1)])]
        projection f = F.Operation [pair] bool (Map.fromList [([i], f i) | i <- [0 .. 3]])
        ops = Map.fromList [("p", constant pair 0), ("q", constant pair 1), ("fst", projection (`div` 2))]
        everywhere _ = Just True
        check label ok = unless ok (fail label)
        get result = either fail pure result
    base <- get (F.finiteTheory classes ops)
    observed <- get (F.proveOn base Map.empty everywhere p q)
    check "different trees share the same observation" (p /= q && F.applyAt observed Map.empty == Just 1)
    before <- get (F.derives EG.defaultLimits base (apply p) (apply q))
    checked <- get (F.promote observed)
    after <- get (F.derives EG.defaultLimits checked (apply p) (apply q))
    check "the e-graph uses a promoted equation in context" (not before && after)
    let sndP = app bool "snd" p
        sndQ = app bool "snd" q
    check "a certificate is confined to its checked signature" (isLeft (F.derives EG.defaultLimits checked sndP sndQ))
    withSnd <- get (F.finiteTheory classes (Map.insert "snd" (projection (`mod` 2)) ops))
    local <- get (F.proveOn withSnd Map.empty everywhere p q)
    check "snd invalidates contextual promotion" (isLeft (F.promote local))
    check "snd distinguishes the pair values" (isLeft (F.proveOn withSnd Map.empty everywhere sndP sndQ))
    let partial = F.Operation [pair] bool (Map.singleton [0] 0)
    check "a missing operation row blocks certification" (isLeft (F.finiteTheory classes (Map.insert "fst" partial ops)))
    check
        "a result outside its carrier blocks certification"
        (isLeft (F.finiteTheory classes (Map.insert "p" (constant pair 4) ops)))
    let endo = Term "->" [Term "(->)" [], num, num]
        identity values = Map.fromList [(i, i) | i <- values]
        numbers = Map.fromList [(num, identity [-1 .. 1]), (endo, identity [0, 1])]
        application = F.Operation [endo, num] num (Map.fromList [([f, i], op i) | (f, op) <- [(0, id), (1, abs)], i <- [-1 .. 1]])
        signature =
            Map.fromList [("id", constant endo 0), ("abs", constant endo 1), ("app", application), ("minusOne", constant num (-1))]
        call f arg = Term "app" [num, atom endo f, arg]
        var = Map.singleton ("x" :: Symbol)
        absX = call "abs" x
        idX = call "id" x
    signed <- get (F.finiteTheory numbers signature)
    guarded <- get (F.proveOn signed (var num) (fmap (>= 0) . Map.lookup "x") absX idX)
    check "the guard is retained at use" (F.applyAt guarded (var 1) == Just 1 && isNothing (F.applyAt guarded (var (-1))))
    check "guarded equality cannot be installed globally" (isLeft (F.promote guarded))
    check
        "no certificate for an unevaluated or empty guard"
        (all (\g -> isLeft (F.proveOn signed (var num) g absX x)) [const Nothing, const (Just False)])
    check "the full domain contains a counterexample" (isLeft (F.proveOn signed (var num) everywhere absX idX))
    same <- get (F.proveOn signed (var num) everywhere (call "abs" absX) absX)
    withAbs <- get (F.promote same)
    let ground = call "abs" (atom num "minusOne")
    proved <- get (F.derives EG.defaultLimits withAbs (call "abs" ground) ground)
    check "the admitted variable rule rewrites a ground application" proved
    contextualObservations
    putStrLn "Finite observational law checks passed."

-- | Compare partition refinement with explicit compositions of finite contexts.
contextualObservations :: IO ()
contextualObservations = do
    let source = Term "Source" []
        middle = Term "Middle" []
        bit = Term "Bit" []
        sourceValues = [0 .. 3]
        middleValues = [0 .. 2]
        bits = [0, 1]
        alone sort name = Term name [sort]
        checked theory sort a b = F.proveOn theory Map.empty (const $ Just True) (alone sort a) (alone sort b)
        pack value = min 2 value
        inspect left value right = if left == 1 && value == 1 && right == 0 then 1 else 0
        carriers = Map.fromList [(source, coarse sourceValues), (middle, coarse middleValues), (bit, Map.fromList [(0, 0), (1, 1)])]
        coarse values = Map.fromList [(value, 0) | value <- values]
        named =
            [ (source, zip ["a", "b", "c", "d"] sourceValues)
            , (middle, zip ["m0", "m1", "m2"] middleValues)
            , (bit, zip ["bit0", "bit1"] bits)
            ]
        ops =
            Map.fromList $
                [(name, constant sort value) | (sort, values) <- named, (name, value) <- values]
                    <> [ ("pack", F.Operation [source] middle (Map.fromList [([i], pack i) | i <- sourceValues]))
                       ,
                           ( "inspect"
                           , F.Operation [bit, middle, bit] bit (Map.fromList [([l, i, r], inspect l i r) | l <- bits, i <- middleValues, r <- bits])
                           )
                       , ("flip", F.Operation [bit] bit (Map.fromList [([i], 1 - i) | i <- bits]))
                       ]
        -- Exhaust the reachable pair states with an independent context interpreter.
        distinguishable sort left right = visit Set.empty [(sort, left, right)]
        visit _ [] = False
        visit seen (pairState@(sort, left, right) : pending)
            | sort == bit && left /= right = True
            | Set.member pairState seen = visit seen pending
            | otherwise =
                visit (Set.insert pairState seen) $
                    [(result, operation left, operation right) | (result, operation) <- contexts sort] <> pending
        contexts sort
            | sort == source = [(middle, pack)]
            | sort == middle = [(bit, \v -> inspect l v r) | l <- bits, r <- bits]
            | otherwise =
                [(bit, (1 -))]
                    <> [(bit, \v -> inspect v i r) | i <- middleValues, r <- bits]
                    <> [(bit, inspect l i) | l <- bits, i <- middleValues]
    original <- either fail pure (F.finiteTheory carriers ops)
    let refined = F.refineObservations original
    forM_ named $ \(sort, values) ->
        forM_ values $ \(a, i) ->
            forM_ values $ \(b, j) ->
                unless (isRight (checked refined sort a b) == not (distinguishable sort i j)) $
                    fail "partition refinement disagrees with brute-force context composition"
    case F.distinguishingContext original source 0 1 of
        Right (Just [F.ContextFrame "pack" [] [], F.ContextFrame "inspect" [1] [0]]) -> pure ()
        other -> fail ("wrong shortest distinguishing context: " <> show other)
    case F.distinguishingContext original source 0 2 of
        Right Nothing -> pure ()
        other -> fail ("invented a distinguishing context: " <> show other)
    unless (F.distinguishingContext original bit 0 1 == Right (Just [])) $
        fail "different observations require no enclosing operation"
    before <- either fail pure (checked original source "a" "c")
    unless (isLeft $ F.promote before) (fail "the original partition overlooks a distinguishing operation")
    scoped <- either fail pure (checked refined source "a" "c")
    _ <- either fail pure (F.promote scoped)
    pure ()

-- | A total nullary operation.
constant :: Term -> Integer -> F.Operation
constant sort value = F.Operation [] sort (Map.singleton [] value)
