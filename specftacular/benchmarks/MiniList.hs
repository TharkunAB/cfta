-- Some usual list functions.
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Specftacular

main =
    experimentalPhases
        (defaultOptions 7 4)
        (const Nothing)
        [ con "reverse" (reverse :: [A] -> [A])
        , con "[]" ([] :: [A])
        ]
