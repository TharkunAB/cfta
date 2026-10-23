import Control.Exception (SomeException, evaluate, try)
import Specftacular.Utils (mtauWithin)
import System.Timeout (timeout)

main :: IO ()
main = do
    result <- timeout 200000 (try (evaluate (mtauWithin (Just (-1)) [])))
    case result of
        Nothing -> putStrLn "REPRODUCED: negative type depth did not return within 200 ms"
        Just (Left err) -> putStrLn ("REPRODUCED: negative type depth raised " ++ show (err :: SomeException))
        Just (Right _) -> fail "Negative type depth returned; inspect the reproduction"
