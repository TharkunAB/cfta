module Holes where

-- GHC finds one fit of its own.
count :: [a] -> Int
count = _

-- GHC finds more than six fits of its own.
flatten :: (Ord a) => [[a]] -> [a]
flatten = _

mapList :: (a -> b) -> [a] -> [b]
mapList = _

-- The fit needs two components.
countMatches :: (a -> Bool) -> [a] -> Int
countMatches = _

-- A hole of a type that is not a function: the fits use the locals.
firstOr :: a -> [a] -> a
firstOr fallback xs = _
