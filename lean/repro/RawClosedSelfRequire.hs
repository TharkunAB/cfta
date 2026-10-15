module Main (main) where

import Control.Exception (evaluate)
import Data.CFTA.Enumeration (unconstrained)
import Data.CFTA.Equality.Constraint
import Data.CFTA.Equality.Operations (reduceEqConstraints)
import Data.CFTA.Interned
import Data.CFTA.Path
import System.Timeout (timeout)

-- | Check the exported raw self binder before the required-path worker.
main :: IO ()
main = do
    let loop = createMuDontCleanup id :: Node Int
        paths = map (Path . map ChildIndex) [[0, 0], [1, 0]]
        classes = mkEqConstraints [paths]
        reduced = reduceEqConstraints classes EmptyConstraints [loop, loop]
    print (null (freeVars loop), unconstrained loop, unfoldOuterRec loop == loop)
    answer <- timeout 2000000 $ evaluate $ case reduced of
        [] -> True
        node : _ -> node == EmptyNode
    case answer of
        Nothing -> putStrLn "raw closed self binder: reduction timed out after 2 seconds"
        Just result -> error ("unexpected completed reduction: " ++ show result)
