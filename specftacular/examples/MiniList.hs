-- Some usual list functions.
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Specftacular

main =
    tacularSpec
        [ con "reverse" (reverse :: [A] -> [A])
        , con "[]" ([] :: [A])
        , con "null" (null :: [A] -> Bool)
        , con "True" (True :: Bool)
        , con "False" (False :: Bool)
        ]
