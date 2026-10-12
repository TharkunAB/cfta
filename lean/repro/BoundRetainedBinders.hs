-- | Bound retained epsilon cycles and check productive depth-indexed ranks.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_, unless)
import qualified Data.CFTA.Equality as Equality
import qualified Data.CFTA.Gen as Generator
import qualified Data.CFTA.Interned as Interned
import qualified Data.CFTA.Term as Term
import Data.List (sort)
import qualified Data.Set as Set
import System.Timeout (timeout)

-- | The common leaf of both productive recursive branches.
leaf :: Equality.Node String
leaf = Equality.Node [Equality.Edge "a" []]

-- | Nested binders with epsilon references and two productive unary constructors.
productive :: Equality.Node String
productive = Equality.createMu $ \outer -> Equality.createMu $ \inner ->
    Equality.union [outer, inner, leaf, Equality.Node [Equality.Edge "f" [outer], Equality.Edge "g" [inner]]]

-- | Force bounded construction and check every rank of the productive finite language.
main :: IO ()
main = do
    let empty =
            [ ("retained self", Interned.createMuDontCleanup id)
            , ("ordinary self", Equality.createMu id)
            , ("retained nested", Interned.createMuDontCleanup $ \outer -> Interned.createMuDontCleanup $ \_inner -> outer)
            ] ::
                [(String, Equality.Node String)]
    forM_ empty $ \(name, root) -> do
        rows <- timeout 1000000 $ evaluate $ length $ Equality.nodeEdges root
        bounded <- timeout 1000000 $ evaluate $ Equality.nodeCount $ Equality.boundDepth 0 root
        print (name, Set.null $ Equality.freeVars root, rows, bounded)
        unless (Set.null (Equality.freeVars root) && rows == Just 0 && bounded == Just 0) $
            fail "An empty retained binder did not produce a finite empty depth bound."
    let expected depth
            | depth < 0 = []
            | otherwise = Term.Node "a" [] : [Term.Node symbol [child] | symbol <- ["f", "g"], child <- expected (depth - 1)]
    forM_ [0 .. 3] $ \depth -> do
        let generator = Generator.fromAutomatonUpToDepth depth productive
            wanted = expected depth
        case Generator.values generator of
            Left err -> fail $ show err
            Right values -> do
                print (depth, Generator.cardinality generator, length values)
                unless (sort values == sort wanted && Generator.cardinality generator == Right (fromIntegral $ length wanted)) $
                    fail "A productive nested binder changed its bounded language or count."
                forM_ (zip [0 ..] values) $ \(rank, value) ->
                    unless (Generator.rankOfTerm generator value == Right rank && Generator.unrank generator rank == Right value) $
                        fail "A bounded recursive term did not retain its distinct rank."
