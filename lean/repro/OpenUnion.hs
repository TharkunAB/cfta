{-# LANGUAGE OverloadedStrings #-}

-- | Compare an enclosing recursive reference with the declared grammar union.
module Main (main) where

import qualified Data.CFTA.Equality as E
import qualified Data.CFTA.Term as Term

-- | The grammar A = a | wrap(B), B = A | b must contain wrap(a).
main :: IO ()
main = do
    let grammar :: E.Node String
        grammar = E.Mu $ \outer ->
            E.Node
                [ E.Edge "a" []
                , E.Edge "wrap" [E.Mu $ \_ -> E.union [outer, E.Node [E.Edge "b" []]]]
                ]
        wanted = Term.Node "wrap" [Term.Node "a" []]
    putStrLn "The declared grammar contains wrap(a); source union discards the enclosing reference."
    print $ E.plainTermsAtMost 2 grammar
    print $ E.accepts grammar wanted
    if E.accepts grammar wanted
        then error "The recorded union limitation no longer reproduces."
        else pure ()
