module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Equality
import Data.CFTA.Path (unPath)
import qualified Data.Set as Set
import System.Timeout (timeout)

-- | Check actual inherited path growth with one fixed normalized local payload.
main :: IO ()
main = do
    let own = mkEqConstraints [[path [0], path [1, 0, 0]], [path [0, 1], path [1, 0, 1]]]
        next inherited = eqConstraintsDescend (combineEqConstraints inherited own) 1
        payloads = take 8 (iterate next EmptyConstraints)
        classes = map (Set.toAscList . unPathEClass) . unsafeGetEclasses
        expected 0 = []
        expected steps = [[path (replicate zeros 0 ++ [1]) | zeros <- reverse [1 .. steps + 1]]]
        maxLength constraints = maximum (0 : map (length . unPath) (concat (classes constraints)))
        observed = map maxLength payloads
        checked =
            map classes payloads == map expected [0 .. 7]
                && maxLength own == 4
                && observed == [0, 3, 4, 5, 6, 7, 8, 9]
    result <- timeout 3000000 (evaluate checked)
    print result
    unless (result == Just True) (fail "fixed local inherited-payload growth")
    print observed
