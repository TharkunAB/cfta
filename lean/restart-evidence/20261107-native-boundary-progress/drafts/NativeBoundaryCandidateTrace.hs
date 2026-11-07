{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (SomeException, evaluate, throwIO, try)
import Data.CFTA.Enumeration (noExpansionPreference, termsPruneWith)
import Data.CFTA.Equality
import Data.IORef
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)
import System.Timeout (timeout)

{- | Record a bounded diagnostic prefix from the canonical-order engine.
This draft does not prove divergence or interned-order correspondence.
-}
main :: IO ()
main = do
    steps <- newIORef ([] :: [(String, String)])
    let oracle st uv view =
            let tick = unsafePerformIO $ do
                    seen <- readIORef steps
                    if length seen >= 12 then throwIO (userError "diagnostic trace limit") else pure ()
                    let label = either (const "after") (show . nodeIdentity) view
                    writeIORef steps ((show uv, label) : seen)
             in tick `seq` pure (False, st)
        same = equalityConstraint (mkEqConstraints [[path [0], path [1]], [path [0, 0], path [1, 0]]])
        p x = Node [mkEdge "p" [x, x] same]
        a = Mu $ \x -> Node [Edge "a" [], mkEdge "p" [x, x] same, mkEdge "p" [p x, p x] same]
        b = Mu $ \x -> Node [Edge "a" [], mkEdge "p" [x, a] same]
        root :: Node String
        root = Node [mkEdge "p" [b, a] same]
    prepared <-
        timeout
            5000000
            (evaluate (let n = nodeCount root; e = edgeCount root; c = Set.null (freeVars root) in n `seq` e `seq` c `seq` (n, e, c)))
    print ("construction", prepared)
    case prepared of
        Nothing -> pure ()
        Just _ -> do
            result <-
                try (timeout 8000000 (evaluate (length (take 1 (termsPruneWith "Mu" () noExpansionPreference oracle root))))) ::
                    IO (Either SomeException (Maybe Int))
            print ("canonical_engine_trace", result)
            readIORef steps >>= print . reverse
