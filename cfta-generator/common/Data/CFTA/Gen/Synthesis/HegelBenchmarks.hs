{-# LANGUAGE OverloadedStrings #-}

{- | A refinement-typed list library and benchmark queries in the style of the
RQ1 evaluation of Hegel (Mishra and Jagannathan, /Liquid Tree Automata/,
2026).

The papers name the 14 queries and describe each of their 42 refinements in
one line, but they do not print the specifications or the library: those are
in a supplement that is not public. This module recreates queries from the
descriptions over a list library with precise specifications. The
refinements use uninterpreted measures: @len@ (the length of a list), @hd@
and @lst@ (its first and last elements), @mem@ (one when an element is in a
list, and zero otherwise), @at@ (the element at an index), @idx@ (the index
of an element in a list), @proj1@ and @proj2@ (the parts of a pair), @ap@
(the application of a function value to an argument), and @iter@ (a function
applied to a value a number of times), and @mapM@ and @filt@ (a list mapped
by a function and a list filtered by a predicate). A Boolean is an integer that is zero or one.

As in the paper, each query has its own library: the list functions, and the
functions of its group, as pairs or Booleans. A goal must rule out the
smaller programs that also satisfy it, because a
synthesizer that merges similar terms returns the smallest program of the
goal type. A solution can be smaller than the paper's when a smaller program
satisfies the recreated goal. This is example data for the specs and the
benchmarks, not a stable interface.
-}
module Data.CFTA.Gen.Synthesis.HegelBenchmarks (
    -- * Libraries
    measures,
    listLibrary,
    pairLibrary,
    booleanLibrary,
    lookupLibrary,
    arrayLibrary,
    stringLibrary,
    functionLibrary,

    -- * Benchmarks
    LiquidBenchmark (..),
    liquidBenchmarks,
) where

import Data.Text (Text)

import Data.CFTA.Gen.Synthesis.Liquid

-- | The measures with their arities.
measures :: [(Text, Int)]
measures =
    [ ("len", 1)
    , ("hd", 1)
    , ("lst", 1)
    , ("mem", 2)
    , ("at", 2)
    , ("idx", 2)
    , ("proj1", 1)
    , ("proj2", 1)
    , ("ap", 2)
    , ("iter", 3)
    , ("mapM", 2)
    , ("filt", 2)
    ]

-- | Components with their refinement types in the syntax of 'parseRType'.
components :: [(Text, Text)] -> [Component]
components = map (fmap rtype)

-- | A refinement type in the syntax of 'parseRType'. A parse error stops the program.
rtype :: Text -> RType
rtype = either error id . parseRType

-- The library

-- | List functions with precise refinements over the measures.
listLibrary :: [Component]
listLibrary =
    components
        [ ("nil", "{v:[a] | len v = 0}")
        , ("zero", "{v:Int | v = 0}")
        ,
            ( "cons"
            , "x:a -> xs:[a] -> {v:[a] | len v = len xs + 1 && hd v = x && mem x v = 1"
                <> " && (len xs = 0 => lst v = x) && (len xs >= 1 => lst v = lst xs)}"
            )
        ,
            ( "append"
            , "xs:[a] -> ys:[a] -> {v:[a] | len v = len xs + len ys"
                <> " && (len xs >= 1 => hd v = hd xs && at v (len xs - 1) = lst xs)"
                <> " && (len ys >= 1 => lst v = lst ys)"
                <> " && (len xs = 0 && len ys >= 1 => hd v = hd ys)"
                <> " && (len ys = 0 && len xs >= 1 => lst v = lst xs)}"
            )
        , ("rev", "xs:[a] -> {v:[a] | len v = len xs && (len xs >= 1 => hd v = lst xs && lst v = hd xs)}")
        ,
            ( "take"
            , "n:{v:Int | v >= 0} -> xs:[a] -> {v:[a] | (n <= len xs => len v = n) && (n > len xs => len v = len xs)"
                <> " && (n >= 1 && len xs >= 1 => hd v = hd xs)}"
            )
        ,
            ( "drop"
            , "n:{v:Int | v >= 0} -> xs:[a] -> {v:[a] | (n <= len xs => len v = len xs - n)"
                <> " && (n > len xs => len v = 0) && (n < len xs => lst v = lst xs && hd v = at xs n)}"
            )
        , ("length", "xs:[a] -> {v:Int | v = len xs}")
        , ("incr", "x:Int -> {v:Int | v = x + 1}")
        , ("decr", "x:Int -> {v:Int | v = x - 1}")
        , ("sub", "x:Int -> y:Int -> {v:Int | v = x - y}")
        , ("head", "xs:{v:[a] | len v >= 1} -> {v:a | v = hd xs && mem v xs = 1}")
        , ("last", "xs:{v:[a] | len v >= 1} -> {v:a | v = lst xs && mem v xs = 1}")
        , ("tail", "xs:{v:[a] | len v >= 1} -> {v:[a] | len v = len xs - 1 && (len xs >= 2 => lst v = lst xs)}")
        , ("nth", "xs:[a] -> i:{v:Int | 0 <= v && v < len xs} -> {v:a | v = at xs i && mem v xs = 1}")
        ]

-- | Pairs of lists, with @splitAt@ and @zip@.
pairLibrary :: [Component]
pairLibrary =
    components
        [
            ( "splitAt"
            , "n:{v:Int | v >= 0} -> xs:[a]"
                <> " -> {v:([a], [a]) | (n <= len xs => len (proj1 v) = n && len (proj2 v) = len xs - n)"
                <> " && (n > len xs => len (proj1 v) = len xs && len (proj2 v) = 0)"
                <> " && (n < len xs => hd (proj2 v) = at xs n && lst (proj2 v) = lst xs)}"
            )
        , ("fst", "p:([a], [a]) -> {v:[a] | v = proj1 p}")
        , ("snd", "p:([a], [a]) -> {v:[a] | v = proj2 p}")
        , ("pair", "f:[a] -> s:[a] -> {v:([a], [a]) | proj1 v = f && proj2 v = s}")
        ,
            ( "zip"
            , "xs:[a] -> ys:[a] -> {v:[(a, a)] | (len xs <= len ys => len v = len xs)"
                <> " && (len xs > len ys => len v = len ys)"
                <> " && (len xs >= 1 && len ys >= 1 => proj1 (hd v) = hd xs && proj2 (hd v) = hd ys)"
                <> " && (len xs = len ys && len xs >= 1 => proj1 (lst v) = lst xs && proj2 (lst v) = lst ys)}"
            )
        ]

-- | Booleans, and membership in a list.
booleanLibrary :: [Component]
booleanLibrary =
    components
        [ ("elem", "x:a -> xs:[a] -> {v:Bool | v <=> mem x xs = 1}")
        , ("and", "p:Bool -> q:Bool -> {v:Bool | v <=> p = 1 && q = 1}")
        , ("or", "p:Bool -> q:Bool -> {v:Bool | v <=> p = 1 || q = 1}")
        , ("not", "p:Bool -> {v:Bool | v <=> p = 0}")
        ]

-- | A test of zero, and the lookup of a key in a list of keys with a list of values.
lookupLibrary :: [Component]
lookupLibrary =
    components
        [ ("isZero", "x:Int -> {v:Bool | v <=> x = 0}")
        , ("lookup", "k:Int -> ks:[Int] -> vs:{v:[a] | len v = len ks} -> {v:a | v = at vs (idx k ks)}")
        ]

{- | The update of a list at an index. The frame condition is a quantified
formula: every other index keeps its element.
-}
arrayLibrary :: [Component]
arrayLibrary =
    components
        [
            ( "set"
            , "xs:[a] -> i:{v:Int | 0 <= v && v < len xs} -> x:a"
                <> " -> {v:[a] | len v = len xs && at v i = x && forall k. k = i || at v k = at xs k}"
            )
        ]

-- | The first index of a character in a string, or the length of the string.
stringLibrary :: [Component]
stringLibrary =
    components
        [("indexOf", "c:Char -> s:[Char] -> {v:Int | v = idx c s && 0 <= v && v <= len s}")]

{- | Higher-order functions over function values, with @ap@ for application.
Each group of queries takes the functions it names from this list.
-}
functionLibrary :: [Component]
functionLibrary =
    components
        [ ("map", "f:(a -> b) -> xs:[a] -> {v:[b] | len v = len xs && forall k. at v k = ap f (at xs k)}")
        , ("compose", "f:(b -> c) -> g:(a -> b) -> {v:a -> c | forall k. ap v k = ap f (ap g k)}")
        , ("apply", "f:(a -> b) -> x:a -> {v:b | v = ap f x}")
        , ("applyN", "f:(Int -> Int) -> n:{v:Int | v >= 0} -> x:Int -> {v:Int | v = iter f n x}")
        , ("add", "x:Int -> y:Int -> {v:Int | v = x + y}")
        , ("incr", "x:Int -> {v:Int | v = x + 1}")
        , ("decr", "x:Int -> {v:Int | v = x - 1}")
        ,
            ( "rev"
            , "xs:[a] -> {v:[a] | len v = len xs && forall k. 0 <= k && k < len xs => at v k = at xs (len xs - 1 - k)}"
            )
        , ("head", "xs:{v:[a] | len v >= 1} -> {v:a | v = hd xs && mem v xs = 1}")
        , ("last", "xs:{v:[a] | len v >= 1} -> {v:a | v = lst xs && mem v xs = 1}")
        , ("null", "xs:[a] -> {v:Bool | v <=> len xs = 0}")
        , ("mapE", "f:(a -> b) -> xs:[a] -> {v:[b] | v = mapM f xs && len v = len xs}")
        , ("filter", "p:(a -> Bool) -> xs:[a] -> {v:[a] | v = filt p xs && len v <= len xs}")
        ]

-- Benchmarks

-- | A query with the paper's description of it, its library, and a bound on its size.
data LiquidBenchmark = LiquidBenchmark
    { liquidName :: Text
    , liquidDescription :: Text
    , liquidLibrary :: [Component]
    , liquidConditionals :: Bool
    -- ^ Whether the solutions need @if@, as for the paper's starred queries.
    , liquidQuery :: LiquidQuery
    , liquidBound :: Int
    }

-- | The recreated queries.
liquidBenchmarks :: [LiquidBenchmark]
liquidBenchmarks =
    [ bounded 7
        $ benchmark
            "Nth2"
            "Swap the elements at indexes i and j of the reverse of l"
            (indexing <> functions ["rev"])
        $ "i:{v:Int | 0 <= v && v < len l} -> j:{v:Int | 0 <= v && v < len l && v /= i} -> l:[a]"
            <> " -> {v:[a] | len v = len l && at v i = at l (len l - 1 - j) && at v j = at l (len l - 1 - i)"
            <> " && forall k. k = i || k = j || k < 0 || k >= len l || at v k = at l (len l - 1 - k)}"
    , bounded 6
        $ benchmark
            "Nth3"
            "Increment the elements at indexes i and j of l, and swap them"
            (indexing <> functions ["incr"])
        $ "i:{v:Int | 0 <= v && v < len l} -> j:{v:Int | 0 <= v && v < len l && v /= i} -> l:[Int]"
            <> " -> {v:[Int] | len v = len l && at v i = at l j + 1 && at v j = at l i + 1"
            <> " && forall k. k = i || k = j || at v k = at l k}"
    , benchmark
        "SplitStr1"
        "Split s at the character c"
        strings
        "c:Char -> s:[Char] -> {v:([Char], [Char]) | len (proj1 v) = idx c s && len (proj2 v) = len s - idx c s}"
    , benchmark "SplitStr2" "Split s at the character c, and swap the parts" strings $
        "c:Char -> s:[Char] -> {v:([Char], [Char]) | len (proj1 v) = len s - idx c s && len (proj2 v) = idx c s"
            <> " && (idx c s < len s => hd (proj1 v) = at s (idx c s)) && (idx c s >= 1 => hd (proj2 v) = hd s)}"
    , bounded 6
        $ benchmark "SplitStr3" "Split s at the character c, and put c in front of the second part" strings
        $ "c:Char -> s:[Char] -> {v:([Char], [Char]) | len (proj1 v) = idx c s"
            <> " && len (proj2 v) = len s - idx c s + 1 && hd (proj2 v) = c}"
    , benchmark "Nth1" "Swap the elements at indexes i and j of l" indexing $
        "i:{v:Int | 0 <= v && v < len l} -> j:{v:Int | 0 <= v && v < len l && v /= i} -> l:[a]"
            <> " -> {v:[a] | len v = len l && at v i = at l j && at v j = at l i"
            <> " && forall k. k = i || k = j || at v k = at l k}"
    , benchmark
        "RevApp1"
        "Reverse l and append to itself"
        lists
        "l:{v:[a] | len v >= 1} -> {v:[a] | len v = len l + len l && hd v = lst l && lst v = lst l}"
    , benchmark
        "RevApp2"
        "Append l to itself and reverse"
        lists
        "l:{v:[a] | len v >= 1} -> {v:[a] | len v = len l + len l && hd v = lst l && lst v = hd l}"
    , benchmark
        "RevApp3"
        "Reverse l, append l, and reverse"
        lists
        "l:{v:[a] | len v >= 1} -> {v:[a] | len v = len l + len l && hd v = hd l && lst v = hd l}"
    , benchmark "RevZip1" "Reverse f and zip it with s" pairs $
        "f:{v:[a] | len v >= 1} -> s:{v:[a] | len v = len f}"
            <> " -> {v:[(a, a)] | len v = len f && proj1 (hd v) = lst f && proj2 (hd v) = hd s}"
    , benchmark "RevZip2" "Reverse s and zip f with it" pairs $
        "f:{v:[a] | len v >= 1} -> s:{v:[a] | len v = len f}"
            <> " -> {v:[(a, a)] | len v = len f && proj1 (hd v) = hd f && proj2 (hd v) = lst s}"
    , benchmark "RevZip3" "Zip f and s, and reverse" pairs $
        "f:{v:[a] | len v >= 1} -> s:{v:[a] | len v = len f}"
            <> " -> {v:[(a, a)] | len v = len f && proj1 (hd v) = lst f && proj2 (hd v) = lst s}"
    , benchmark "SplitAt1" "Split l at index n; drop m elements from the second part (the motivating query)" pairs $
        "n:{v:Int | v >= 1} -> m:{v:Int | v >= 0} -> l:{v:[a] | n + m < len v}"
            <> " -> {v:([a], [a]) | len (proj1 v) = n && hd (proj1 v) = hd l && len (proj2 v) = len l - n - m"
            <> " && lst (proj2 v) = lst l}"
    , benchmark "SplitAt2" "Split l at index n; drop m elements from the first part" pairs $
        "n:{v:Int | v >= 0} -> m:{v:Int | v >= 0 && v <= n} -> l:{v:[a] | n <= len v}"
            <> " -> {v:([a], [a]) | len (proj1 v) = n - m && len (proj2 v) = len l - n}"
    , benchmark "SplitAt3" "Split l at index n; drop (n-m) elements from the second part" pairs $
        "n:{v:Int | v >= 1} -> m:{v:Int | v >= 0 && v <= n} -> l:{v:[a] | n + n - m < len v}"
            <> " -> {v:([a], [a]) | len (proj1 v) = n && hd (proj1 v) = hd l && len (proj2 v) = len l - n - (n - m)"
            <> " && lst (proj2 v) = lst l}"
    , benchmark
        "Nth_Incr1"
        "Return the (n+1)th element of l"
        lists
        "n:{v:Int | v >= 0} -> l:{v:[a] | n + 1 < len v} -> {v:a | v = at l (n + 1)}"
    , benchmark
        "Nth_Incr2"
        "Return the (n-1)th element of l"
        lists
        "n:{v:Int | v >= 1} -> l:{v:[a] | n < len v} -> {v:a | v = at l (n - 1)}"
    , benchmark
        "Nth_Incr3"
        "Return the nth element of l and increment it"
        lists
        "n:{v:Int | v >= 0} -> l:{v:[Int] | n < len v} -> {v:Int | v = at l n + 1}"
    , benchmark
        "AppendN1"
        "Append the first n elements to l"
        lists
        "n:{v:Int | v >= 0} -> l:{v:[a] | len v >= 1 && n <= len v} -> {v:[a] | len v = n + len l && lst v = lst l}"
    , benchmark "AppendN3" "Append the last n elements to l" lists $
        "n:{v:Int | v >= 1} -> l:{v:[a] | n <= len v}"
            <> " -> {v:[a] | len v = n + len l && at v (n - 1) = lst l && lst v = lst l}"
    , starred "AppendN2" "Append the first (n-1) elements to l" (listLibrary <> lookupLibrary) $
        "n:{v:Int | v >= 0} -> l:{v:[a] | len v >= 1 && n <= len v}"
            <> " -> {v:[a] | (n >= 1 => len v = n - 1 + len l) && (n = 0 => v = l) && lst v = lst l}"
    , starred "LookRange1" "Lookup k in the values, else return d" lookups $
        "k:Int -> ks:[Int] -> vs:{v:[a] | len v = len ks && len v >= 1} -> d:a"
            <> " -> {v:a | (mem k ks = 1 => v = at vs (idx k ks)) && (mem k ks /= 1 => v = d)}"
    , starred "LookRange2" "Lookup k in the values, else return the last value" lookups $
        "k:Int -> ks:[Int] -> vs:{v:[a] | len v = len ks && len v >= 1}"
            <> " -> {v:a | (mem k ks = 1 => v = at vs (idx k ks)) && (mem k ks /= 1 => v = lst vs)}"
    , starred "LookRange3" "Lookup k in the values, else return the first value" lookups $
        "k:Int -> ks:[Int] -> vs:{v:[a] | len v = len ks && len v >= 1}"
            <> " -> {v:a | (mem k ks = 1 => v = at vs (idx k ks)) && (mem k ks /= 1 => v = hd vs)}"
    , benchmark
        "Map1"
        "Map f on l and increment each element"
        mapping
        "f:(Int -> Int) -> l:[Int] -> {v:[Int] | len v = len l && forall k. at v k = ap f (at l k) + 1}"
    , benchmark
        "Map2"
        "Map f on l and decrement each element"
        mapping
        "f:(Int -> Int) -> l:[Int] -> {v:[Int] | len v = len l && forall k. at v k = ap f (at l k) - 1}"
    , benchmark "Map3" "Map f on l, increment each element, and reverse" mapping $
        "f:(Int -> Int) -> l:[Int]"
            <> " -> {v:[Int] | len v = len l"
            <> " && forall k. 0 <= k && k < len l => at v k = ap f (at l (len l - 1 - k)) + 1}"
    , benchmark
        "MapDouble1"
        "Map f followed by g"
        mappingTwice
        "f:(a -> b) -> g:(b -> c) -> l:[a] -> {v:[c] | len v = len l && forall k. at v k = ap g (ap f (at l k))}"
    , benchmark
        "MapDouble2"
        "Map g followed by f"
        mappingTwice
        "f:(b -> c) -> g:(a -> b) -> l:[a] -> {v:[c] | len v = len l && forall k. at v k = ap f (ap g (at l k))}"
    , benchmark
        "MapDouble3"
        "Map the composition of f with itself on l"
        mappingTwice
        "f:(a -> a) -> l:[a] -> {v:[a] | len v = len l && forall k. at v k = ap f (ap f (at l k))}"
    , benchmark
        "ApplyNAdd1"
        "Apply f on m, n times, and add m"
        iterating
        "f:(Int -> Int) -> n:{v:Int | v >= 0} -> m:Int -> {v:Int | v = iter f n m + m}"
    , benchmark
        "ApplyNAdd2"
        "Apply f on m, n+1 times, and add m"
        iterating
        "f:(Int -> Int) -> n:{v:Int | v >= 0} -> m:Int -> {v:Int | v = iter f (n + 1) m + m}"
    , benchmark
        "ApplyNAdd3"
        "Apply f on m, n+1 times, and add m+1"
        iterating
        "f:(Int -> Int) -> n:{v:Int | v >= 0} -> m:Int -> {v:Int | v = iter f (n + 1) m + m + 1}"
    , benchmark
        "ApplyNInv1"
        "Apply g and h on l, and filter using f"
        filtering
        "f:(a -> Bool) -> g:(a -> a) -> h:(a -> a) -> l:[a] -> {v:[a] | v = filt f (mapM h (mapM g l))}"
    , benchmark
        "ApplyNInv2"
        "Filter l using f, and apply g and h"
        filtering
        "f:(a -> Bool) -> g:(a -> a) -> h:(a -> a) -> l:[a] -> {v:[a] | v = mapM h (mapM g (filt f l))}"
    , benchmark "ApplyNInv3" "Apply g and h on l, filter using f, and apply g and h" filtering $
        "f:(a -> Bool) -> g:(a -> a) -> h:(a -> a) -> l:[a]"
            <> " -> {v:[a] | v = mapM h (mapM g (filt f (mapM h (mapM g l))))}"
    , starred
        "ApplyList1"
        "Apply the head of fl on s"
        applying
        "fl:{v:[a -> a] | len v >= 0} -> s:a -> {v:a | (len fl >= 1 => v = ap (hd fl) s) && (len fl = 0 => v = s)}"
    , starred
        "ApplyList2"
        "Apply the last element of fl on s"
        applying
        "fl:{v:[a -> a] | len v >= 0} -> s:a -> {v:a | (len fl >= 1 => v = ap (lst fl) s) && (len fl = 0 => v = s)}"
    , benchmark
        "ApplyList3"
        "Apply the first and then the last function of fl on s"
        applying
        "fl:{v:[a -> a] | len v >= 1} -> s:a -> {v:a | v = ap (lst fl) (ap (hd fl) s)}"
    , benchmark
        "CEdge1"
        "True if src and tgt both are in l"
        booleans
        "src:Int -> tgt:Int -> l:[Int] -> {v:Bool | v <=> mem src l = 1 && mem tgt l = 1}"
    , benchmark
        "CEdge2"
        "True if src or tgt is in l"
        booleans
        "src:Int -> tgt:Int -> l:[Int] -> {v:Bool | v <=> mem src l = 1 || mem tgt l = 1}"
    , benchmark
        "CEdge3"
        "True if src is, but tgt is not in l"
        booleans
        "src:Int -> tgt:Int -> l:[Int] -> {v:Bool | v <=> mem src l = 1 && mem tgt l /= 1}"
    ]
  where
    benchmark name description library signature = LiquidBenchmark name description library False (query signature) 5
    starred name description library signature = LiquidBenchmark name description library True (query signature) 5
    query = either error id . parseQuery
    bounded bound entry = entry{liquidBound = bound}
    indexing = [component | component@(name, _) <- listLibrary, name == "nth"] <> arrayLibrary
    strings =
        [ component
        | component@(name, _) <- listLibrary <> pairLibrary
        , name `elem` ["take", "drop", "cons", "splitAt", "fst", "snd", "pair"]
        ]
            <> stringLibrary
    functions names = [component | component@(name, _) <- functionLibrary, name `elem` names]
    mapping = functions ["map", "compose", "incr", "decr", "rev"]
    mappingTwice = functions ["map", "compose", "apply"]
    iterating = functions ["applyN", "add", "incr"]
    applying = functions ["head", "last", "apply", "null"]
    -- The map of this group states its result as a term of mapM.
    filtering = [(if name == "mapE" then "map" else name, typ) | (name, typ) <- functions ["mapE", "filter"]]
    lookups = listLibrary <> booleanLibrary <> lookupLibrary
    lists = listLibrary
    pairs = listLibrary <> pairLibrary
    booleans = listLibrary <> booleanLibrary
