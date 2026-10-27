{-# LANGUAGE PatternSynonyms #-}

import Control.Exception (evaluate)
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint)
import qualified Data.CFTA.EGraph as EG
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import Data.CFTA.Term (pattern Node)
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdout)
import System.Timeout (timeout)

-- Maximum is monotone. Advancing its second component exceeds every child.
measure :: String -> [(Integer, Integer)] -> (Integer, Integer)
measure symbol children =
    let (major, minor) = maximum ((if symbol == "good" then (1, 0) else (0, 0)) : children)
     in (major, minor + 1)

cost :: EG.ClassId -> String -> [EG.ClassId] -> [(Integer, Integer)] -> (Integer, Integer)
cost _ symbol _ children = measure symbol children

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    let leaf symbol = Node symbol []
        (a, g1) = EG.addTerm (leaf "a") (EG.emptyEGraph :: EG.EGraph () String)
        (u, g2) = EG.addTerm (Node "u" [leaf "a"]) g1
        Just g3 = EG.merge a u g2
        (z, g4) = EG.addTerm (leaf "z") g3
        constraint = equalityConstraint (mkEqConstraints [[path [0], path [1]]])
        (bad, g5) = EG.addConstrained constraint "bad" [a, z] g4
        (good, g6) = EG.addTerm (leaf "good") g5
        Just graph = EG.merge bad good g6
    print (fmap (`FTA.accepts` leaf "good") (EG.classAutomaton graph bad))
    print (EG.extract (\_ _ _ children -> 1 + sum children :: Int) graph bad)
    print (EG.analyse measure min graph bad)
    result <- timeout 2000000 (evaluate (EG.extract cost graph bad))
    case result of
        Nothing -> putStrLn "lexicographic extraction timed out after 2000000 microseconds"
        Just answer -> print answer
