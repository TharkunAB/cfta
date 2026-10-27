import Control.Monad (unless)
import qualified Data.CFTA.Internal.UnionFind as UF

main :: IO ()
main = do
    let uv = UF.intToUVar
        initial = UF.withInitialValues (map uv [0, 1, 1, 2, 3])
        requests = [(0, 1), (2, 3), (2, 0), (8, 9), (8, 2), (10, 2), (10, 10)]
        states = scanl (\forest (left, right) -> UF.union (uv left) (uv right) forest) initial requests
        roots forest = map (\variable -> UF.uvarToInt (UF.root (uv variable) forest)) [0 .. 10]
        unchanged = and [snd (UF.find (uv variable) forest) == forest | forest <- states, variable <- [0 .. 11]]
        duplicate = initial == UF.withInitialValues (map uv [0, 1, 2, 3])
        absent = roots (UF.withInitialValues []) == [0 .. 10]
    unless (unchanged && duplicate && absent) (error "union-find lookup or initialization mismatch")
    print (map roots states)
    print (unchanged, duplicate, absent)
    print (last states)
