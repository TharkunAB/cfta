{-# LANGUAGE OverloadedStrings #-}
module Main where
import Control.Exception (SomeException, try)
import Control.Monad (unless, forM_)
import Specftacular
main :: IO ()
main = do
  let options = defaultOptions 4 1
      signature = [con "reverse" (reverse :: [A] -> [A]), con "[]" ([] :: [A]), con "null" (null :: [A] -> Bool), con "True" True, con "False" False]
  unless (searchCompletionFuel options == 15 && searchParallelTests options == Nothing && searchSpeculation options == 0) (error "unexpected defaults")
  original <- experimentalPhases options (const Nothing) signature
  parallel <- experimentalPhases options {searchParallelTests = Just 0, searchSpeculation = 2} (const Nothing) signature
  unless (original == parallel) (error "optional parallel flags changed complete law sequence")
  putStrLn ("parallel flag comparison: equal, " ++ show (length original) ++ " laws")
  forM_ [-1,63] $ \fuel -> do
    result <- try (experimentalPhases options {searchCompletionFuel = fuel} (const Nothing) signature) :: IO (Either SomeException [String])
    case result of
      Left _ -> putStrLn ("invalid completion exponent rejected: " ++ show fuel)
      Right _ -> error "invalid completion exponent accepted"
