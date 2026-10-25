module Main where
import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar, readMVar)
import Control.Exception (SomeException, evaluate, mask, onException, throwIO, try)
import Control.Monad (unless)
import Data.List (isInfixOf)
import Data.Maybe (isJust)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem (getAllocationCounter, setAllocationCounter)
import System.Timeout (timeout)
decideInParallel :: (a -> Maybe b) -> [a] -> [Maybe b]
{-# NOINLINE decideInParallel #-}
decideInParallel f xs = unsafePerformIO $ mask $ \restore -> do
    started <-
        mapM
            (\x -> do var <- newEmptyMVar; thread <- forkIO (try (restore (measured (f x))) >>= putMVar var); pure (thread, var))
            xs
    results <- restore (mapM (takeMVar . snd) started) `onException` mapM_ (killThread . fst) started
    decided <- either (throwIO :: SomeException -> IO a) pure (sequence results)
    let (dropped, taken) = break (isJust . fst) decided
    left <- getAllocationCounter
    setAllocationCounter (left - sum (map snd (dropped ++ take 1 taken)))
    pure (map fst decided)
  where
    measured y = do
        before <- getAllocationCounter
        result <- evaluate y
        after <- getAllocationCounter
        pure (result, before - after)


main :: IO ()
main = do
  let decision :: Int -> Maybe ()
      decision 0 = Just ()
      decision _ = error "discarded suffix"
  serial <- evaluate (head (map decision [0,1]))
  concurrent <- try (evaluate (head (decideInParallel decision [0,1]))) :: IO (Either SomeException (Maybe ()))
  unless (serial == Just ()) (error "serial prefix failed")
  case concurrent of
    Left exception | "discarded suffix" `isInfixOf` show exception -> putStrLn "unused suffix exception: confirmed"
    _ -> error "expected unused suffix exception"
  gate <- newEmptyMVar
  let blocking :: Int -> Maybe ()
      blocking 0 = Just ()
      blocking _ = unsafePerformIO (readMVar gate)
  serialBlocked <- evaluate (head (map blocking [0,1]))
  concurrentBlocked <- timeout 500000 (evaluate (head (decideInParallel blocking [0,1])))
  unless (serialBlocked == Just () && concurrentBlocked == Nothing) (error "expected prefix timeout difference")
  putStrLn "unused blocked suffix: confirmed (500 ms timeout)"
