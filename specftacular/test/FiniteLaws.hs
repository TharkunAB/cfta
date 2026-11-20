{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Monad (unless)
import Data.Either (isLeft)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)

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
    putStrLn "Finite observational law checks passed."

-- | A total nullary operation.
constant :: Term -> Integer -> F.Operation
constant sort value = F.Operation [] sort (Map.singleton [] value)
