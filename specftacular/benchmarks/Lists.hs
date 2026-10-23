-- Some usual list functions.
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Specftacular

main = do
    options <- parseOptions
    -- ftacularSpec' 7 3 extraReps [
    res <-
        experimentalPhases
            options
            (const Nothing)
            [ con "reverse" (reverse :: [A] -> [A])
            , con "++" ((++) :: [A] -> [A] -> [A])
            , con "[]" ([] :: [A])
            , con "map" (map :: (A -> B) -> [A] -> [B])
            , con "length" (length :: [A] -> Int)
            , con "concat" (concat :: [[A]] -> [A])
            , -- Add some numeric functions to get more laws about length.
              arith (Proxy :: Proxy Int)
            ]
    mapM_ print res
    print (length res)
