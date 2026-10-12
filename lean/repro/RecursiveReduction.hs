-- | Check that equality reduction retains recursive domains and their constraints.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import qualified Data.CFTA.Equality as Equality
import qualified Data.CFTA.Term as Term
import qualified Data.Set as Set
import System.Timeout (timeout)

-- | The base case of both recursive languages.
leaf :: Equality.Node String
leaf = Equality.Node [Equality.Edge "a" []]

-- | One unary constructor above a domain.
step :: Equality.Node String -> Equality.Node String
step child = Equality.Node [Equality.Edge "f" [child]]

-- | An explicit epsilon self-reference does not add finite accepted terms.
withEpsilon :: Equality.Node String
withEpsilon = Equality.createMu $ \self -> Equality.union [leaf, step self, self]

-- | The same language without the epsilon alternative.
withoutEpsilon :: Equality.Node String
withoutEpsilon = Equality.createMu $ \self -> Equality.union [leaf, step self]

-- | The root accepts three equal terms from the common recursive language.
root :: Equality.Node String
root =
    Equality.Node
        [ Equality.mkEdge
            "triple"
            [withEpsilon, withoutEpsilon, withEpsilon]
            (Equality.equalityConstraint $ Equality.mkEqConstraints [[Equality.path [0], Equality.path [1], Equality.path [2]]])
        ]

-- | Force the public reduction and check both accepted and unequal triples.
main :: IO ()
main = do
    let base = Term.Node "a" []
        accepted = Term.Node "triple" [base, base, base]
        rejected = Term.Node "triple" [base, Term.Node "f" [base], base]
    print (Set.null $ Equality.freeVars root)
    print (Equality.accepts root accepted, Equality.accepts root rejected)
    result <- timeout 3000000 $ do
        let reduced = Equality.fixUnbounded Equality.reducePartially root
        _ <- evaluate (Equality.nodeCount reduced)
        pure reduced
    case result of
        Nothing -> fail "Recursive equality reduction did not finish."
        Just reduced -> do
            print (reduced == root)
            print (Equality.accepts reduced accepted, Equality.accepts reduced rejected)
            let bounded node = Set.fromList $ Equality.terms $ Equality.boundDepth 4 node
            unless
                ( reduced == root
                    && bounded reduced == bounded root
                    && Equality.accepts reduced accepted
                    && not (Equality.accepts reduced rejected)
                ) $
                fail "Reduction changed the recursive equality language."
