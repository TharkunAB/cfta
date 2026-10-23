{-# LANGUAGE ScopedTypeVariables #-}

import Control.Exception (SomeException, displayException, evaluate, try)
import Control.Monad (unless)
import Data.List (isInfixOf)
import Specftacular
import Specftacular.Utils (mtauWithin)
import System.Environment (withArgs)
import System.Exit (ExitCode (..))

main :: IO ()
main = do
    bad <- try (withArgs ["3", "4", "--type-depth", "-1"] parseOptions)
    case bad of
        Left (ExitFailure _) -> putStrLn "PASS: parser rejects a negative type depth"
        _ -> fail "parser accepted a negative type depth"
    zero <- withArgs ["3", "4", "--type-depth", "0"] parseOptions
    unless (searchTypeDepth zero == Just 0) $ fail "parser rejected depth zero"
    grammar <- try (evaluate (mtauWithin (Just (-1)) []))
    case grammar of
        Left (err :: SomeException)
            | "type depth must be a nonnegative integer" `isInfixOf` displayException err ->
                putStrLn "PASS: grammar rejects a negative type depth immediately"
        _ -> fail "grammar did not reject a negative type depth"
    _ <- evaluate (mtauWithin (Just 0) [])
    public <- try (experimentalPhases ((defaultOptions 3 4){searchTypeDepth = Just (-1)}) (const Nothing) [])
    case public of
        Left (err :: SomeException)
            | "type depth must be a nonnegative integer" `isInfixOf` displayException err ->
                putStrLn "PASS: public search rejects a negative type depth immediately"
        _ -> fail "public search did not reject a negative type depth"
    let options = (defaultOptions 3 4){searchTests = 20, searchTypeDepth = Just 1, searchRecheck = 4}
        signature = [con "reverse" (reverse :: [A] -> [A]), con "[]" ([] :: [A])]
    serial <- experimentalPhases options (const Nothing) signature
    parallel <- experimentalPhases (options{searchParallel = True}) (const Nothing) signature
    ahead <- experimentalPhases (options{searchEnumerateAhead = True}) (const Nothing) signature
    unless (not (null serial) && serial == parallel && serial == ahead) $
        fail "phase 4 serial, parallel and enumerate-ahead results differ"
    putStrLn "PASS: phase 4 runs with incremental typing, depth bound and rechecking"
    putStrLn "PASS: serial, parallel and enumerate-ahead runs return identical laws for this signature"
