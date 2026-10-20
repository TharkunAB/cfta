{-# LANGUAGE OverloadedStrings #-}

-- The monad laws for lists.
import Control.Monad
import Specftacular

main = do
    [s, p] <- map read <$> programArguments
    -- ftacularSpec' 7 3 extraReps [
    res <-
        experimentalPhases
            s
            p
            (const Nothing)
            [ con "return" (return :: A -> [A])
            , con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B])
            , con "++" ((++) :: [A] -> [A] -> [A])
            , con ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C])
            ]
    mapM_ print res
    print (length res)
