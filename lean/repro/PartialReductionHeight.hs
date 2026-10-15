{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Equality
import qualified Data.Set as Set
import System.Timeout (timeout)

-- | Count ordinary layers and stop at recursive or union records.
height :: Node String -> Int
height EmptyNode = 0
height (Mu _) = 0
height (InternedUnion _) = 0
height (Node edges) = 1 + maximum (0 : map height (concatMap edgeChildren edges))
height (Rec _) = 0

-- | Refute an ordinary-height measure with the actual closed local prefix.
main :: IO ()
main = do
    let same = mkEqConstraints [[path [0], path [1]]]
        leaf = Node [Edge "a" []] :: Node String
        raw name = createMuDontCleanup $ \_ ->
            Node [Edge name [], mkEdge "p" [leaf, leaf] (equalityConstraint same)]
        wrap node = Node [Edge "w" [node]]
        original = Node [mkEdge "root" [wrap (raw "left"), wrap (raw "right")] (equalityConstraint same)]
    case nodeEdges original of
        [edge] -> do
            let narrowed = reduceEdgeIntersection EmptyConstraints edge
                children = edgeChildren narrowed
                final = reducePartially original
                observed =
                    ( height original
                    , maximum (map height (edgeChildren edge))
                    , maximum (map height children)
                    , height final
                    )
                innerPayloads =
                    [ equalities (edgeConstraint innerEdge)
                    | child <- children
                    , wrapper <- nodeEdges child
                    , inner <- edgeChildren wrapper
                    , innerEdge <- nodeEdges inner
                    ]
            result <-
                timeout 3000000
                    $ evaluate
                    $ observed == (2, 1, 3, 4)
                        && Set.null (freeVars original)
                        && innerPayloads == [same, same]
                        && Node [narrowed] == final
            print observed
            print result
            unless (result == Just True) (fail "closed partial-reduction height boundary")
        _ -> fail "expected one original edge"
