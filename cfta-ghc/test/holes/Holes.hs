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

-- A hole in a case alternative: its binders have an open multiplicity.
sizeOf :: Maybe [Int] -> Int
sizeOf m = case m of
    Just ys -> _
    Nothing -> 0

-- A hole of a function type: the fits print eta reduced, as (,) x.
pairWith :: a -> b -> (a, b)
pairWith x = _

-- A function that GHC checks after the hole is a fit: twice x.
twiceOr :: Int -> Int
twiceOr x = _

twice :: Int -> Int
twice n = n + n
