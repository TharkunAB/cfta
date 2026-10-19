{-# LANGUAGE OverloadedStrings #-}

-- The monad laws for lists.
import Control.Monad
import Specftacular

main =
    ftacularSpec
        [ con "return" (return :: A -> [A])
        , con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B])
        , con "++" ((++) :: [A] -> [A] -> [A])
        , con ">=>" ((>=>) :: (A -> [B]) -> (B -> [C]) -> A -> [C])
        ]
