-- Source-only example. This file has not been compiled or executed.
-- The recursive child has a real bound occurrence, so createMu retains Mu.
import qualified Data.CFTA.Equality as E
import Data.CFTA.Enumeration (runs, truncatedTerms)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Interned as I
import Data.CFTA.Path (path)
import qualified Data.CFTA.Term as T

leaf :: String -> I.Node String
leaf symbol = I.Node [I.mkEdge symbol [] I.noConstraint]

recursiveChild :: I.Node String
recursiveChild = I.Mu $ \self -> I.Node
  [ I.mkEdge "h" [leaf "a"] I.noConstraint
  , I.mkEdge "again" [self] I.noConstraint
  ]

root :: I.Node String
root = I.Node [I.mkEdge "p" [recursiveChild, leaf "b"]
  (I.equalityConstraint (mkEqConstraints [[path [0, 0], path [1]]]))]

main :: IO ()
main = do
  -- Source prediction: p has an opaque recursive child, not a checked h child.
  print (take 1 (truncatedTerms root))
  print (take 1 (runs "cut" root))
  -- This fully concrete term violates the root equality a = b.
  print (E.accepts root (T.Node "p" [T.Node "h" [T.Node "a" []], T.Node "b" []]))
