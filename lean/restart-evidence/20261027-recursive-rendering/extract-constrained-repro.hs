{-# LANGUAGE PatternSynonyms #-}

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint)
import qualified Data.CFTA.EGraph as EG
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import Data.CFTA.Term (Term, pattern Node)

-- Every constructor cost exceeds each child cost and is monotone.
cost :: String -> [Int] -> Int
cost symbol children = (if symbol == "h" then 2 else 1) + sum children

main :: IO ()
main = do
    let leaf symbol = Node symbol []
        (ga, g1) = EG.addTerm (Node "g" [leaf "a"]) (EG.emptyEGraph :: EG.EGraph () String)
        (hb, g2) = EG.addTerm (Node "h" [leaf "b"]) g1
        Just g3 = EG.merge ga hb g2
        Just b = EG.lookupTerm (leaf "b") g3
        equalPaths = equalityConstraint (mkEqConstraints [[path [0, 0], path [1]]])
        (parent, g4) = EG.addConstrained equalPaths "p" [ga, b] g3
        good :: Term String
        good = Node "p" [Node "h" [leaf "b"], leaf "b"]
    print (EG.extract cost g4 parent)
    print (take 1 (EG.termsByCost cost g4 parent))
    print (fmap (`FTA.accepts` good) (EG.classAutomaton g4 parent))

-- Source-derived expected outputs at c168a952d779a72294c34d9c8fd5afd0e308c5ab:
-- Nothing
-- [(5, p(h(b), b))]  (with the library's Term Show representation)
-- Right True
-- This source has not been compiled or executed by its author.
