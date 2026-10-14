module Main (main) where

import qualified Data.CFTA as F
import Data.CFTA.Constraint (noConstraint)
import qualified Data.CFTA.Interned as I
import qualified Data.Map.Strict as Map

-- | Construct one source leaf alternative for each supplied symbol.
leaves :: [String] -> I.Node String
leaves names = I.Node [I.Edge name [] | name <- names]

-- | Print the actual complete rows and the independently requested child intersection.
main :: IO ()
main = do
    let first = leaves ["a", "b"]
        second = leaves ["b", "c"]
        ordinary = I.Node [I.Edge "f" [first], I.Edge "f" [second]]
        recursive = I.createMu $ \self -> I.Node [I.Edge "h" [self]]
        combined = I.createUnion [ordinary, recursive]
        actual = I.intersect combined ordinary
        enclosing = I.Node [I.Edge "g" [combined], I.Edge "g" [ordinary]]
        shape edge = (F.transitionSymbol edge, map show (F.transitionChildren edge))
        rows value = [(show state, map shape edges) | (state, edges) <- Map.toAscList (I.toRows value)]
    print ("actual returns original ordinary node", actual == ordinary)
    print ("combined differs from ordinary", combined /= ordinary)
    print
        ("both roots are original exposed states", all (`Map.member` I.toRows enclosing) (map I.stateOf [combined, ordinary]))
    print ("enclosing", rows enclosing)
    print
        ( "all guards are noConstraint"
        , all ((== noConstraint) . F.transitionConstraint) (concat (Map.elems (I.toRows enclosing)))
        )
    print ("combined", rows combined)
    print ("actual", rows actual)
    print ("source children", map I.stateOf [first, second])
    print ("separate child intersection", rows (I.intersect first second))
