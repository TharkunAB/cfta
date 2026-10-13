module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Interned.Type

-- | Check an identity observation and fail when it does not hold.
check :: String -> Bool -> IO ()
check label holds = do
    putStrLn (label ++ ": " ++ show holds)
    unless holds (fail label)

-- | Replay ordered union identities and the shared two-probe Mu key.
main :: IO ()
main = do
    let depth = Rec RecDepth :: Node String
        ordinary = Rec (RecUnint 0) :: Node String
        forward = createUnion [depth, ordinary]
        reverseOrder = createUnion [ordinary, depth]
        first = createMu (const forward)
        second = createMu (const reverseOrder)
    _ <- evaluate (nodeIdentity forward)
    _ <- evaluate (nodeIdentity reverseOrder)
    check "reversed unions have distinct identities" (forward /= reverseOrder)
    _ <- evaluate (nodeIdentity first)
    _ <- evaluate (nodeIdentity second)
    check "first body retains forward order" (first == forward)
    check "second body returns the first cached order" (second == forward)
    check "second body differs from its raw reversed body" (second /= reverseOrder)
