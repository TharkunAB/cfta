-- Some usual list functions.
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Specftacular

main =
    ftacularSpec
        [ con "reverse" (reverse :: [A] -> [A])
        , con "++" ((++) :: [A] -> [A] -> [A])
        , con "[]" ([] :: [A])
        , con "map" (map :: (A -> B) -> [A] -> [B])
        , con "length" (length :: [A] -> Int)
        , con "concat" (concat :: [[A]] -> [A])
        , -- Add some numeric functions to get more laws about length.
          arith (Proxy :: Proxy Int)
        ]
