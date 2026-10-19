-- Some usual list functions.
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Specftacular

main =
    experimentalPhases
        7
        4
        (const Nothing)
        [ con "reverse" (reverse :: [A] -> [A])
        , con "[]" ([] :: [A])
        ]
