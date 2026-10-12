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
applied to a value a number of times). A Boolean is an integer that is zero or one.

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
    functionLibrary,

    -- * Benchmarks
    LiquidBenchmark (..),
    liquidBenchmarks,
) where

import Data.Text (Text)

import Data.CFTA.Formula (Formula (Forall), Name (..), Sort (IntSort))

import Data.CFTA.Gen.Synthesis (Type (..), (~>))
import Data.CFTA.Gen.Synthesis.Liquid
import Data.CFTA.Refinement.Expression (
    Expr,
    lnot,
    variable,
    (.&&),
    (./=),
    (.<),
    (.<=),
    (.==),
    (.>),
    (.>=),
    (.||),
 )

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
    ]

-- Types and measures

a, int, bool, listA, intList :: Type
a = TVar "a"
int = TCons "Int" []
bool = TCons "Bool" []
listA = TCons "List" [a]
intList = TCons "List" [int]

-- | A pair of lists of @a@.
pairOfLists :: Type
pairOfLists = TCons "Pair" [listA, listA]

len, hd, lst, proj1, proj2 :: Expr -> Expr
len e = measure "len" [e]
hd e = measure "hd" [e]
lst e = measure "lst" [e]
proj1 e = measure "proj1" [e]
proj2 e = measure "proj2" [e]

mem, at :: Expr -> Expr -> Expr
mem x xs = measure "mem" [x, xs]
at xs i = measure "at" [xs, i]

infixr 1 ==>

-- | Implication.
(==>) :: Formula -> Formula -> Formula
p ==> q = lnot p .|| q

-- | Equivalence.
(<=>) :: Formula -> Formula -> Formula
p <=> q = (p ==> q) .&& (q ==> p)

-- | A name of the logic, for the parameters that refinements mention.
var :: String -> Expr
var = variable

-- | A natural number.
nat :: RType
nat = refined int (.>= 0)

-- | A list that is not empty.
nonEmpty :: Type -> RType
nonEmpty typ = refined typ (\v -> len v .>= 1)

-- | A Boolean that holds exactly when the formula does.
truth :: Expr -> Formula -> Formula
truth v formula = (v .== 1 .|| v .== 0) .&& ((v .== 1) <=> formula)

-- The library

-- | List functions with precise refinements over the measures.
listLibrary :: [Component]
listLibrary =
    [ ("nil", refined listA (\v -> len v .== 0))
    , ("zero", refined int (.== 0))
    ,
        ( "cons"
        , "x"
            .: plain a
            --> "xs"
            .: plain listA
            --> refined
                listA
                ( \v ->
                    len v .== len xs
                        + 1 .&& hd v .== x .&& mem x v .== 1 .&& (len xs .== 0 ==> lst v .== x) .&& (len xs .>= 1 ==> lst v .== lst xs)
                )
        )
    ,
        ( "append"
        , "xs"
            .: plain listA
            --> "ys"
            .: plain listA
            --> refined
                listA
                ( \v ->
                    len v .== len xs
                        + len ys
                            .&& (len xs .>= 1 ==> hd v .== hd xs .&& at v (len xs - 1) .== lst xs)
                            .&& (len ys .>= 1 ==> lst v .== lst ys)
                            .&& (len xs .== 0 .&& len ys .>= 1 ==> hd v .== hd ys)
                            .&& (len ys .== 0 .&& len xs .>= 1 ==> lst v .== lst xs)
                )
        )
    ,
        ( "rev"
        , "xs"
            .: plain listA
            --> refined listA (\v -> len v .== len xs .&& (len xs .>= 1 ==> hd v .== lst xs .&& lst v .== hd xs))
        )
    ,
        ( "take"
        , "n"
            .: nat
            --> "xs"
            .: plain listA
            --> refined
                listA
                ( \v ->
                    (n .<= len xs ==> len v .== n) .&& (n .> len xs ==> len v .== len xs) .&& (n .>= 1 .&& len xs .>= 1 ==> hd v .== hd xs)
                )
        )
    ,
        ( "drop"
        , "n"
            .: nat
            --> "xs"
            .: plain listA
            --> refined
                listA
                ( \v ->
                    (n .<= len xs ==> len v .== len xs - n)
                        .&& (n .> len xs ==> len v .== 0)
                        .&& (n .< len xs ==> lst v .== lst xs .&& hd v .== at xs n)
                )
        )
    , ("length", "xs" .: plain listA --> refined int (\v -> v .== len xs))
    , ("incr", "x" .: plain int --> refined int (\v -> v .== x + 1))
    , ("decr", "x" .: plain int --> refined int (\v -> v .== x - 1))
    , ("sub", "x" .: plain int --> "y" .: plain int --> refined int (\v -> v .== x - var "y"))
    , ("head", "xs" .: nonEmpty listA --> refined a (\v -> v .== hd xs .&& mem v xs .== 1))
    , ("last", "xs" .: nonEmpty listA --> refined a (\v -> v .== lst xs .&& mem v xs .== 1))
    , ("tail", "xs" .: nonEmpty listA --> refined listA (\v -> len v .== len xs - 1 .&& (len xs .>= 2 ==> lst v .== lst xs)))
    ,
        ( "nth"
        , "xs"
            .: plain listA
            --> "i"
            .: refined int (\v -> 0 .<= v .&& v .< len xs)
            --> refined a (\v -> v .== at xs (var "i") .&& mem v xs .== 1)
        )
    ]
  where
    x = var "x"
    xs = var "xs"
    ys = var "ys"
    n = var "n"

-- | Pairs of lists, with @splitAt@ and @zip@.
pairLibrary :: [Component]
pairLibrary =
    [
        ( "splitAt"
        , "n"
            .: nat
            --> "xs"
            .: plain listA
            --> refined
                pairOfLists
                ( \v ->
                    (n .<= len xs ==> len (proj1 v) .== n .&& len (proj2 v) .== len xs - n)
                        .&& (n .> len xs ==> len (proj1 v) .== len xs .&& len (proj2 v) .== 0)
                        .&& (n .< len xs ==> hd (proj2 v) .== at xs n .&& lst (proj2 v) .== lst xs)
                )
        )
    , ("fst", "p" .: plain pairOfLists --> refined listA (\v -> v .== proj1 (var "p")))
    , ("snd", "p" .: plain pairOfLists --> refined listA (\v -> v .== proj2 (var "p")))
    ,
        ( "pair"
        , "f" .: plain listA --> "s" .: plain listA --> refined pairOfLists (\v -> proj1 v .== var "f" .&& proj2 v .== var "s")
        )
    ,
        ( "zip"
        , "xs"
            .: plain listA
            --> "ys"
            .: plain listA
            --> refined
                (TCons "List" [TCons "Pair" [a, a]])
                ( \v ->
                    (len xs .<= len ys ==> len v .== len xs)
                        .&& (len xs .> len ys ==> len v .== len ys)
                        .&& (len xs .>= 1 .&& len ys .>= 1 ==> proj1 (hd v) .== hd xs .&& proj2 (hd v) .== hd ys)
                        .&& (len xs .== len ys .&& len xs .>= 1 ==> proj1 (lst v) .== lst xs .&& proj2 (lst v) .== lst ys)
                )
        )
    ]
  where
    xs = var "xs"
    ys = var "ys"
    n = var "n"

-- | Booleans, and membership in a list.
booleanLibrary :: [Component]
booleanLibrary =
    [ ("elem", "x" .: plain a --> "xs" .: plain listA --> refined bool (\v -> truth v (mem (var "x") (var "xs") .== 1)))
    , ("and", "p" .: plain bool --> "q" .: plain bool --> refined bool (\v -> truth v (var "p" .== 1 .&& var "q" .== 1)))
    , ("or", "p" .: plain bool --> "q" .: plain bool --> refined bool (\v -> truth v (var "p" .== 1 .|| var "q" .== 1)))
    , ("not", "p" .: plain bool --> refined bool (\v -> truth v (var "p" .== 0)))
    ]

-- | A test of zero, and the lookup of a key in a list of keys with a list of values.
lookupLibrary :: [Component]
lookupLibrary =
    [ ("isZero", "x" .: plain int --> refined bool (\v -> truth v (var "x" .== 0)))
    ,
        ( "lookup"
        , "k"
            .: plain int
            --> "ks"
            .: plain intList
            --> "vs"
            .: refined listA (\v -> len v .== len (var "ks"))
            --> refined a (\v -> v .== at (var "vs") (measure "idx" [var "k", var "ks"]))
        )
    ]

{- | The update of a list at an index. The frame condition is a quantified
formula: every other index keeps its element.
-}
arrayLibrary :: [Component]
arrayLibrary =
    [
        ( "set"
        , "xs"
            .: plain listA
            --> "i"
            .: refined int (\v -> 0 .<= v .&& v .< len (var "xs"))
            --> "x"
            .: plain a
            --> refined listA (\v -> len v .== len (var "xs") .&& at v (var "i") .== var "x" .&& keeps v (var "xs") [var "i"])
        )
    ]

{- | Every index of the first list except the given ones has the element of
the second list at it.
-}
keeps :: Expr -> Expr -> [Expr] -> Formula
keeps new old excepted =
    Forall
        [(Name "k", IntSort)]
        (foldr (\index rest -> var "k" .== index .|| rest) (at new (var "k") .== at old (var "k")) excepted)

{- | Higher-order functions over function values, with @ap@ for application.
Each group of queries takes the functions it names from this list.
-}
functionLibrary :: [Component]
functionLibrary =
    [
        ( "map"
        , "f"
            .: plain (a ~> b)
            --> "xs"
            .: plain listA
            --> refined
                (TCons "List" [b])
                (\v -> len v .== len (var "xs") .&& everywhere (\k -> at v k .== ap (var "f") (at (var "xs") k)))
        )
    ,
        ( "compose"
        , "f"
            .: plain (b ~> c)
            --> "g"
            .: plain (a ~> b)
            --> refined (a ~> c) (\v -> everywhere (\x -> ap v x .== ap (var "f") (ap (var "g") x)))
        )
    , ("apply", "f" .: plain (a ~> b) --> "x" .: plain a --> refined b (\v -> v .== ap (var "f") (var "x")))
    ,
        ( "applyN"
        , "f"
            .: plain (int ~> int)
            --> "n"
            .: nat
            --> "x"
            .: plain int
            --> refined int (\v -> v .== measure "iter" [var "f", var "n", var "x"])
        )
    , ("add", "x" .: plain int --> "y" .: plain int --> refined int (\v -> v .== var "x" + var "y"))
    , ("incr", "x" .: plain int --> refined int (\v -> v .== var "x" + 1))
    , ("decr", "x" .: plain int --> refined int (\v -> v .== var "x" - 1))
    ,
        ( "rev"
        , "xs"
            .: plain listA
            --> refined
                listA
                ( \v ->
                    len v
                        .== len (var "xs")
                        .&& everywhere (\k -> 0 .<= k .&& k .< len (var "xs") ==> at v k .== at (var "xs") (len (var "xs") - 1 - k))
                )
        )
    , ("head", "xs" .: nonEmpty listA --> refined a (\v -> v .== hd (var "xs") .&& mem v (var "xs") .== 1))
    , ("last", "xs" .: nonEmpty listA --> refined a (\v -> v .== lst (var "xs") .&& mem v (var "xs") .== 1))
    , ("null", "xs" .: plain listA --> refined bool (\v -> truth v (len (var "xs") .== 0)))
    ]
  where
    b = TVar "b"
    c = TVar "c"

-- | The application of a function value to an argument.
ap :: Expr -> Expr -> Expr
ap function argument = measure "ap" [function, argument]

-- | A formula for every integer, given as a function of the bound name.
everywhere :: (Expr -> Formula) -> Formula
everywhere body = Forall [(Name "k", IntSort)] (body (var "k"))

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
    [ benchmark
        "Nth1"
        "Swap the elements at indexes i and j of l"
        (listLibrary <> arrayLibrary)
        [("i", index), ("j", refined int (\v -> 0 .<= v .&& v .< len l .&& v ./= var "i")), ("l", plain listA)]
        $ refined
            listA
            ( \v ->
                len v
                    .== len l
                    .&& at v (var "i")
                    .== at l (var "j")
                    .&& at v (var "j")
                    .== at l (var "i")
                    .&& keeps v l [var "i", var "j"]
            )
    , benchmark "RevApp1" "Reverse l and append to itself" lists [("l", nonEmpty listA)] $
        refined listA (\v -> len v .== len l + len l .&& hd v .== lst l .&& lst v .== lst l)
    , benchmark "RevApp2" "Append l to itself and reverse" lists [("l", nonEmpty listA)] $
        refined listA (\v -> len v .== len l + len l .&& hd v .== lst l .&& lst v .== hd l)
    , benchmark "RevApp3" "Reverse l, append l, and reverse" lists [("l", nonEmpty listA)] $
        refined listA (\v -> len v .== len l + len l .&& hd v .== hd l .&& lst v .== hd l)
    , benchmark "RevZip1" "Reverse f and zip it with s" pairs sameLength $
        refined pairList (\v -> len v .== len f .&& proj1 (hd v) .== lst f .&& proj2 (hd v) .== hd s)
    , benchmark "RevZip2" "Reverse s and zip f with it" pairs sameLength $
        refined pairList (\v -> len v .== len f .&& proj1 (hd v) .== hd f .&& proj2 (hd v) .== lst s)
    , benchmark "RevZip3" "Zip f and s, and reverse" pairs sameLength $
        refined pairList (\v -> len v .== len f .&& proj1 (hd v) .== lst f .&& proj2 (hd v) .== lst s)
    , benchmark
        "SplitAt1"
        "Split l at index n; drop m elements from the second part (the motivating query)"
        pairs
        [("n", refined int (.>= 1)), ("m", nat), ("l", refined listA (\v -> var "n" + var "m" .< len v))]
        $ refined
            pairOfLists
            ( \v ->
                len (proj1 v) .== var "n" .&& hd (proj1 v) .== hd l .&& len (proj2 v) .== len l
                    - var "n"
                    - var "m" .&& lst (proj2 v) .== lst l
            )
    , benchmark
        "SplitAt2"
        "Split l at index n; drop m elements from the first part"
        pairs
        [("n", nat), ("m", refined int (\v -> v .>= 0 .&& v .<= var "n")), ("l", refined listA (\v -> var "n" .<= len v))]
        $ refined pairOfLists (\v -> len (proj1 v) .== var "n" - var "m" .&& len (proj2 v) .== len l - var "n")
    , benchmark
        "SplitAt3"
        "Split l at index n; drop (n-m) elements from the second part"
        pairs
        [ ("n", refined int (.>= 1))
        , ("m", refined int (\v -> v .>= 0 .&& v .<= var "n"))
        , ("l", refined listA (\v -> var "n" + var "n" - var "m" .< len v))
        ]
        $ refined
            pairOfLists
            ( \v ->
                len (proj1 v) .== var "n" .&& hd (proj1 v) .== hd l .&& len (proj2 v) .== len l
                    - var "n"
                    - (var "n" - var "m") .&& lst (proj2 v) .== lst l
            )
    , benchmark
        "Nth_Incr1"
        "Return the (n+1)th element of l"
        lists
        [("n", nat), ("l", refined listA (\v -> var "n" + 1 .< len v))]
        $ refined a (\v -> v .== at l (var "n" + 1))
    , benchmark
        "Nth_Incr2"
        "Return the (n-1)th element of l"
        lists
        [("n", refined int (.>= 1)), ("l", refined listA (\v -> var "n" .< len v))]
        $ refined a (\v -> v .== at l (var "n" - 1))
    , benchmark
        "Nth_Incr3"
        "Return the nth element of l and increment it"
        lists
        [("n", nat), ("l", refined intList (\v -> var "n" .< len v))]
        $ refined int (\v -> v .== at l (var "n") + 1)
    , benchmark
        "AppendN1"
        "Append the first n elements to l"
        lists
        [("n", nat), ("l", refined listA (\v -> len v .>= 1 .&& var "n" .<= len v))]
        $ refined listA (\v -> len v .== var "n" + len l .&& lst v .== lst l)
    , benchmark
        "AppendN3"
        "Append the last n elements to l"
        lists
        [("n", refined int (.>= 1)), ("l", refined listA (\v -> var "n" .<= len v))]
        $ refined listA (\v -> len v .== var "n" + len l .&& at v (var "n" - 1) .== lst l .&& lst v .== lst l)
    , starred
        "AppendN2"
        "Append the first (n-1) elements to l"
        (listLibrary <> lookupLibrary)
        [("n", nat), ("l", refined listA (\v -> len v .>= 1 .&& var "n" .<= len v))]
        $ refined
            listA
            (\v -> (var "n" .>= 1 ==> len v .== var "n" - 1 + len l) .&& (var "n" .== 0 ==> v .== l) .&& lst v .== lst l)
    , starred "LookRange1" "Lookup k in the values, else return d" lookups (keyed <> [("d", plain a)]) $
        refined a (\v -> found v .&& (mem (var "k") (var "ks") ./= 1 ==> v .== var "d"))
    , starred "LookRange2" "Lookup k in the values, else return the last value" lookups keyed $
        refined a (\v -> found v .&& (mem (var "k") (var "ks") ./= 1 ==> v .== lst (var "vs")))
    , starred "LookRange3" "Lookup k in the values, else return the first value" lookups keyed $
        refined a (\v -> found v .&& (mem (var "k") (var "ks") ./= 1 ==> v .== hd (var "vs")))
    , benchmark "Map1" "Map f on l and increment each element" mapping [("f", plain (int ~> int)), ("l", plain intList)] $
        refined intList (\v -> len v .== len l .&& everywhere (\k -> at v k .== ap (var "f") (at l k) + 1))
    , benchmark "Map2" "Map f on l and decrement each element" mapping [("f", plain (int ~> int)), ("l", plain intList)] $
        refined intList (\v -> len v .== len l .&& everywhere (\k -> at v k .== ap (var "f") (at l k) - 1))
    , benchmark
        "Map3"
        "Map f on l, increment each element, and reverse"
        mapping
        [("f", plain (int ~> int)), ("l", plain intList)]
        $ refined
            intList
            ( \v -> len v .== len l .&& everywhere (\k -> 0 .<= k .&& k .< len l ==> at v k .== ap (var "f") (at l (len l - 1 - k)) + 1)
            )
    , benchmark
        "MapDouble1"
        "Map f followed by g"
        mappingTwice
        [("f", plain (a ~> TVar "b")), ("g", plain (TVar "b" ~> TVar "c")), ("l", plain listA)]
        $ refined
            (TCons "List" [TVar "c"])
            (\v -> len v .== len l .&& everywhere (\k -> at v k .== ap (var "g") (ap (var "f") (at l k))))
    , benchmark
        "MapDouble2"
        "Map g followed by f"
        mappingTwice
        [("f", plain (TVar "b" ~> TVar "c")), ("g", plain (a ~> TVar "b")), ("l", plain listA)]
        $ refined
            (TCons "List" [TVar "c"])
            (\v -> len v .== len l .&& everywhere (\k -> at v k .== ap (var "f") (ap (var "g") (at l k))))
    , benchmark
        "MapDouble3"
        "Map the composition of f with itself on l"
        mappingTwice
        [("f", plain (a ~> a)), ("l", plain listA)]
        $ refined listA (\v -> len v .== len l .&& everywhere (\k -> at v k .== ap (var "f") (ap (var "f") (at l k))))
    , benchmark "ApplyNAdd1" "Apply f on m, n times, and add m" iterating applyN $
        refined int (\v -> v .== measure "iter" [var "f", var "n", var "m"] + var "m")
    , benchmark "ApplyNAdd2" "Apply f on m, n+1 times, and add m" iterating applyN $
        refined int (\v -> v .== measure "iter" [var "f", var "n" + 1, var "m"] + var "m")
    , benchmark "ApplyNAdd3" "Apply f on m, n+1 times, and add m+1" iterating applyN $
        refined int (\v -> v .== measure "iter" [var "f", var "n" + 1, var "m"] + var "m" + 1)
    , starred
        "ApplyList1"
        "Apply the head of fl on s"
        applying
        [("fl", refined (TCons "List" [a ~> a]) (\v -> len v .>= 0)), ("s", plain a)]
        $ refined
            a
            (\v -> (len (var "fl") .>= 1 ==> v .== ap (hd (var "fl")) (var "s")) .&& (len (var "fl") .== 0 ==> v .== var "s"))
    , starred
        "ApplyList2"
        "Apply the last element of fl on s"
        applying
        [("fl", refined (TCons "List" [a ~> a]) (\v -> len v .>= 0)), ("s", plain a)]
        $ refined
            a
            (\v -> (len (var "fl") .>= 1 ==> v .== ap (lst (var "fl")) (var "s")) .&& (len (var "fl") .== 0 ==> v .== var "s"))
    , benchmark
        "ApplyList3"
        "Apply the first and then the last function of fl on s"
        applying
        [("fl", nonEmpty (TCons "List" [a ~> a])), ("s", plain a)]
        $ refined a (\v -> v .== ap (lst (var "fl")) (ap (hd (var "fl")) (var "s")))
    , benchmark "CEdge1" "True if src and tgt both are in l" booleans edge $
        refined bool (\v -> truth v (mem src l .== 1 .&& mem tgt l .== 1))
    , benchmark "CEdge2" "True if src or tgt is in l" booleans edge $
        refined bool (\v -> truth v (mem src l .== 1 .|| mem tgt l .== 1))
    , benchmark "CEdge3" "True if src is, but tgt is not in l" booleans edge $
        refined bool (\v -> truth v (mem src l .== 1 .&& mem tgt l ./= 1))
    ]
  where
    benchmark name description library arguments goal = LiquidBenchmark name description library False (LiquidQuery arguments goal) 5
    starred name description library arguments goal = LiquidBenchmark name description library True (LiquidQuery arguments goal) 5
    index = refined int (\v -> 0 .<= v .&& v .< len l)
    functions names = [component | component@(name, _) <- functionLibrary, name `elem` names]
    mapping = functions ["map", "compose", "incr", "decr", "rev"]
    mappingTwice = functions ["map", "compose", "apply"]
    iterating = functions ["applyN", "add", "incr"]
    applying = functions ["head", "last", "apply", "null"]
    applyN = [("f", plain (int ~> int)), ("n", nat), ("m", plain int)]
    lookups = listLibrary <> booleanLibrary <> lookupLibrary
    keyed = [("k", plain int), ("ks", plain intList), ("vs", refined listA (\v -> len v .== len (var "ks") .&& len v .>= 1))]
    found v = mem (var "k") (var "ks") .== 1 ==> v .== at (var "vs") (measure "idx" [var "k", var "ks"])
    lists = listLibrary
    pairs = listLibrary <> pairLibrary
    booleans = listLibrary <> booleanLibrary
    l = var "l"
    f = var "f"
    s = var "s"
    src = var "src"
    tgt = var "tgt"
    pairList = TCons "List" [TCons "Pair" [a, a]]
    sameLength = [("f", nonEmpty listA), ("s", refined listA (\v -> len v .== len f))]
    edge = [("src", plain int), ("tgt", plain int), ("l", plain intList)]
