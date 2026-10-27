{-# LANGUAGE PatternSynonyms #-}

-- Unexecuted witness. Run in a separate capped process.
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint)
import Data.CFTA.EGraph
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import Data.CFTA.Term (Term, pattern Node)
import Data.Maybe (fromMaybe)
import System.IO (hFlush, stdout)

cost :: ClassId -> String -> [ClassId] -> [(Integer, Integer)] -> (Integer, Integer)
cost _ symbol _ children =
    let base = if symbol == "good" then (1, 0) else (0, 0)
        (priority, rank) = maximum (base : children)
     in (priority, rank + 1)

leaf :: String -> Term String
leaf symbol = Node symbol []

main :: IO ()
main = do
    let (a, g1) = addTerm (leaf "a") (emptyEGraph :: EGraph () String)
        (ua, g2) = addTerm (Node "u" [leaf "a"]) g1
        g3 = fromMaybe (error "same-sort cycle merge failed") (merge a ua g2)
        (z, g4) = addTerm (leaf "z") g3
        equalChildren = equalityConstraint (mkEqConstraints [[path [0], path [1]]])
        (bad, g5) = addConstrained equalChildren "bad" [a, z] g4
        (good, g6) = addTerm (leaf "good") g5
        graph = fromMaybe (error "same-sort root merge failed") (merge bad good g6)
        root = find graph bad
        automaton = either (error . show) id (classAutomaton graph root)
    print (FTA.accepts automaton (leaf "good"), FTA.accepts automaton (Node "bad" [leaf "a", leaf "z"]))
    hFlush stdout
    -- The predicted first line is (True,False). Extraction then starves.
    print (extract cost graph root)
