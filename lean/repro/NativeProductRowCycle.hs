module Main (main) where

import qualified Data.CFTA.Interned as I
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | Construct the nullary source leaf.
leaf :: I.Node String
leaf = I.Node [I.Edge "a" []]

-- | Construct the closed recursive source with the selected Mu policy.
source :: Bool -> I.Node String
source smart = (if smart then I.createMu else I.createMuDontCleanup) $ \self ->
    I.Node [I.Edge "a" [], I.Edge "f" [I.Node [I.Edge "a" [], I.Edge "f" [I.createUnion [self, leaf]]]]]

-- | Construct the source child exposed below one f edge.
right :: I.Node String -> I.Node String
right left = I.Node [I.Edge "a" [], I.Edge "f" [I.createUnion [left, leaf]]]

-- | Check the unary a/f term at one finite depth.
acceptsDepth :: Int -> I.Node String -> Bool
acceptsDepth depth value = any accepted (I.nodeEdges value)
  where
    accepted edge = case (I.edgeSymbol edge, I.edgeChildren edge) of
        ("a", []) -> depth == 0
        ("f", [child]) -> depth > 0 && acceptsDepth (depth - 1) child
        _ -> False

-- | Print the literal row mismatch and finite acceptance checks.
check :: Bool -> IO ()
check smart = do
    let left = source smart
        second = right left
        actual = I.intersect left second
        expected =
            I.Node
                [ I.Edge (I.edgeSymbol a) children
                | a <- I.nodeEdges left
                , b <- I.nodeEdges second
                , I.edgeSymbol a == I.edgeSymbol b
                , length (I.edgeChildren a) == length (I.edgeChildren b)
                , let children = zipWith I.intersect (I.edgeChildren a) (I.edgeChildren b)
                , all (/= I.EmptyNode) children
                ]
        rows = Set.fromList . I.nodeEdges
        shape edge = (I.edgeSymbol edge, map I.stateOf (I.edgeChildren edge))
    print ("smart", smart, "literal rows equal", rows actual == rows expected)
    print ("right is an original source state", Map.member (I.stateOf second) (I.toRows left))
    let enclosing = I.Node [I.Edge "g" [left], I.Edge "g" [second]]
    print ("overlapping g alternatives", length (I.nodeEdges enclosing))
    print ("actual", map shape (Set.toList (rows actual)))
    print ("expected", map shape (Set.toList (rows expected)))
    print
        ( "unary depths 0..24 equal input intersection"
        , and
            [ acceptsDepth depth actual
                == (acceptsDepth depth left && acceptsDepth depth second)
            | depth <- [0 .. 24]
            ]
        )
    print ("all depths 0..24 accepted", and [acceptsDepth depth actual | depth <- [0 .. 24]])

-- | Compare the smart and raw Mu constructors.
main :: IO ()
main = mapM_ check [True, False]
