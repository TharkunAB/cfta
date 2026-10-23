{-# LANGUAGE OverloadedStrings #-}

-- The monad laws for lists.
import Control.Monad
import Specftacular

main = do
    options <- parseOptions
    -- ftacularSpec' 7 3 extraReps [
    res <-
        experimentalPhases
            options
            (const Nothing)
            [ con "return" (return :: A -> [A])
            , con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B])
            , con "++" ((++) :: [A] -> [A] -> [A])
            , con ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C])
            ]
    mapM_ print res
    print (length res)
