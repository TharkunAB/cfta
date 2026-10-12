{-# LANGUAGE OverloadedStrings #-}

{- | The Hoogle+ component library and benchmark queries of the ECTA paper.

The components are the 291 Hoogle+ components of Guo et al., /Program
Synthesis by Type-Guided Abstraction Refinement/ (POPL 2020), as Hectare
imported them, and the seven components that Hectare adds for the queries
from Stack Overflow. The queries are the Hoogle+ benchmarks and the Stack
Overflow benchmarks of Hectare's evaluation script, each with its size and
the solution that the evaluation expects. A size counts the components and
arguments of a program. This is example data for the specs and the
benchmarks, not a stable interface.
-}
module Data.CFTA.Gen.Synthesis.HooglePlus (
    -- * Libraries
    hooglePlus,
    hooglePlusWithAugmented,
    hooglePlusComponents,
    augmentedComponents,

    -- * Benchmarks
    Benchmark (..),
    hooglePlusBenchmarks,
    stackOverflowBenchmarks,
) where

import Data.Text (Text)

import Data.CFTA.Gen.Synthesis

-- | A benchmark query with its size and the solution that the evaluation expects.
data Benchmark = Benchmark
    { benchmarkName :: Text
    , benchmarkSize :: Int
    , benchmarkSolution :: Maybe Program
    -- ^ 'Nothing' when the evaluation script gives no solution.
    , benchmarkQuery :: Query
    }
    deriving (Show)

{- | The Hoogle+ library: the components, with @($)@ and @id@ only in argument
position, and Hectare's two pruning rules: a list function is not applied to
@Nil@, and a @Maybe@ function is not applied to @Nothing@.
-}
hooglePlus :: Library
hooglePlus = withComponents hooglePlusComponents

-- | The Hoogle+ library with the components that the Stack Overflow queries need.
hooglePlusWithAugmented :: Library
hooglePlusWithAugmented = withComponents (hooglePlusComponents <> augmentedComponents)

-- | The library of the components, as Hectare builds it.
withComponents :: [(Text, Type)] -> Library
withComponents components =
    library
        [component | component@(name, _) <- components, name `notElem` ["(Data.Function.$)", "Data.Function.id"]]
        [ ("$", TFun (TFun (TVar "a") (TVar "b")) (TFun (TVar "a") (TVar "b")))
        , ("id", TFun (TVar "a") (TVar "a"))
        ]
        -- The original code means to apply the Maybe functions to anything
        -- but Nothing, but its rule selects components by their names, and the
        -- components are group representatives, so the rule selects none:
        -- no Maybe function heads a term of size two. This library does the
        -- same, so its program spaces equal the original's, size by size.
        [ (listFunctions, Just ["Nil"])
        , (maybeFunctions, Nothing)
        ]
  where
    listFunctions =
        [ "Data.Maybe.listToMaybe"
        , "Data.Either.lefts"
        , "Data.Either.rights"
        , "Data.Either.partitionEithers"
        , "Data.Maybe.catMaybes"
        , "GHC.List.head"
        , "GHC.List.last"
        , "GHC.List.tail"
        , "GHC.List.init"
        , "GHC.List.null"
        , "GHC.List.length"
        , "GHC.List.reverse"
        , "GHC.List.concat"
        , "GHC.List.concatMap"
        , "GHC.List.sum"
        , "GHC.List.product"
        , "GHC.List.maximum"
        , "GHC.List.minimum"
        , "(GHC.List.!!)"
        , "(GHC.List.++)"
        ]
    maybeFunctions =
        [ "Data.Maybe.maybeToList"
        , "Data.Maybe.isJust"
        , "Data.Maybe.isNothing"
        , "Data.Maybe.fromJust"
        ]

-- | The 291 Hoogle+ components.
hooglePlusComponents :: [(Text, Type)]
hooglePlusComponents =
    [
        ( "(Data.Bool.&&)"
        , TFun (TCons "Bool" []) (TFun (TCons "Bool" []) (TCons "Bool" []))
        )
    ,
        ( "(Data.Bool.||)"
        , TFun (TCons "Bool" []) (TFun (TCons "Bool" []) (TCons "Bool" []))
        )
    ,
        ( "(Data.Eq./=)"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            (TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" [])))
        )
    ,
        ( "(Data.Eq.==)"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            (TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" [])))
        )
    ,
        ( "(Data.Function.$)"
        , TFun (TFun (TVar "a") (TVar "b")) (TFun (TVar "a") (TVar "b"))
        )
    ,
        ( "(GHC.List.!!)"
        , TFun (TCons "List" [TVar "a"]) (TFun (TCons "Int" []) (TVar "a"))
        )
    ,
        ( "(GHC.List.++)"
        , TFun
            (TCons "List" [TVar "a"])
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    , ("@@hplusTCInstance@@0EqBool", TCons "@@hplusTC@@Eq" [TCons "Bool" []])
    , ("@@hplusTCInstance@@0EqChar", TCons "@@hplusTC@@Eq" [TCons "Char" []])
    , ("@@hplusTCInstance@@0EqDouble", TCons "@@hplusTC@@Eq" [TCons "Double" []])
    , ("@@hplusTCInstance@@0EqFloat", TCons "@@hplusTC@@Eq" [TCons "Float" []])
    , ("@@hplusTCInstance@@0EqInt", TCons "@@hplusTC@@Eq" [TCons "Int" []])
    , ("@@hplusTCInstance@@0EqUnit", TCons "@@hplusTC@@Eq" [TCons "Unit" []])
    ,
        ( "@@hplusTCInstance@@0IsString"
        , TCons "@@hplusTC@@IsString" [TCons "Builder" []]
        )
    ,
        ( "@@hplusTCInstance@@0NumDouble"
        , TCons "@@hplusTC@@Num" [TCons "Double" []]
        )
    , ("@@hplusTCInstance@@0NumFloat", TCons "@@hplusTC@@Num" [TCons "Float" []])
    , ("@@hplusTCInstance@@0NumInt", TCons "@@hplusTC@@Num" [TCons "Int" []])
    , ("@@hplusTCInstance@@0OrdBool", TCons "@@hplusTC@@Ord" [TCons "Bool" []])
    , ("@@hplusTCInstance@@0OrdChar", TCons "@@hplusTC@@Ord" [TCons "Char" []])
    ,
        ( "@@hplusTCInstance@@0OrdDouble"
        , TCons "@@hplusTC@@Ord" [TCons "Double" []]
        )
    , ("@@hplusTCInstance@@0OrdFloat", TCons "@@hplusTC@@Ord" [TCons "Float" []])
    , ("@@hplusTCInstance@@0OrdInt", TCons "@@hplusTC@@Ord" [TCons "Int" []])
    , ("@@hplusTCInstance@@0ShowBool", TCons "@@hplusTC@@Show" [TCons "Bool" []])
    , ("@@hplusTCInstance@@0ShowChar", TCons "@@hplusTC@@Show" [TCons "Char" []])
    ,
        ( "@@hplusTCInstance@@0ShowDouble"
        , TCons "@@hplusTC@@Show" [TCons "Double" []]
        )
    ,
        ( "@@hplusTCInstance@@0ShowFloat"
        , TCons "@@hplusTC@@Show" [TCons "Float" []]
        )
    , ("@@hplusTCInstance@@0ShowInt", TCons "@@hplusTC@@Show" [TCons "Int" []])
    , ("@@hplusTCInstance@@0ShowUnit", TCons "@@hplusTC@@Show" [TCons "Unit" []])
    ,
        ( "@@hplusTCInstance@@1Show"
        , TFun
            (TCons "@@hplusTC@@Show" [TVar "a"])
            ( TFun
                (TCons "@@hplusTC@@Show" [TVar "b"])
                (TCons "@@hplusTC@@Show" [TCons "Either" [TVar "a", TVar "b"]])
            )
        )
    ,
        ( "@@hplusTCInstance@@2Read"
        , TFun
            (TCons "@@hplusTC@@Read" [TVar "a"])
            ( TFun
                (TCons "@@hplusTC@@Read" [TVar "b"])
                (TCons "@@hplusTC@@Read" [TCons "Either" [TVar "a", TVar "b"]])
            )
        )
    ,
        ( "@@hplusTCInstance@@3Ord"
        , TFun
            (TCons "@@hplusTC@@Ord" [TVar "a"])
            ( TFun
                (TCons "@@hplusTC@@Ord" [TVar "b"])
                (TCons "@@hplusTC@@Ord" [TCons "Either" [TVar "a", TVar "b"]])
            )
        )
    ,
        ( "@@hplusTCInstance@@4Eq"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            ( TFun
                (TCons "@@hplusTC@@Eq" [TVar "b"])
                (TCons "@@hplusTC@@Eq" [TCons "Either" [TVar "a", TVar "b"]])
            )
        )
    ,
        ( "@@hplusTCInstance@@6Semigroup"
        , TCons "@@hplusTC@@Semigroup" [TCons "Either" [TVar "a", TVar "b"]]
        )
    ,
        ( "@@hplusTCInstance@@9Eq"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            (TCons "@@hplusTC@@Eq" [TCons "List" [TVar "a"]])
        )
    ,
        ( "Cons"
        , TFun (TVar "a") (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    , ("Data.Bool.False", TCons "Bool" [])
    , ("Data.Bool.True", TCons "Bool" [])
    ,
        ( "Data.Bool.bool"
        , TFun (TVar "a") (TFun (TVar "a") (TFun (TCons "Bool" []) (TVar "a")))
        )
    , ("Data.Bool.not", TFun (TCons "Bool" []) (TCons "Bool" []))
    , ("Data.Bool.otherwise", TCons "Bool" [])
    ,
        ( "Data.ByteString.Builder.byteString"
        , TFun (TCons "ByteString" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.byteStringHex"
        , TFun (TCons "ByteString" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.char7"
        , TFun (TCons "Char" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.char8"
        , TFun (TCons "Char" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.charUtf8"
        , TFun (TCons "Char" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.doubleBE"
        , TFun (TCons "Double" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.doubleDec"
        , TFun (TCons "Double" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.doubleHexFixed"
        , TFun (TCons "Double" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.doubleLE"
        , TFun (TCons "Double" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.floatBE"
        , TFun (TCons "Float" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.floatDec"
        , TFun (TCons "Float" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.floatHexFixed"
        , TFun (TCons "Float" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.floatLE"
        , TFun (TCons "Float" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.hPutBuilder"
        , TFun
            (TCons "Handle" [])
            (TFun (TCons "Builder" []) (TCons "IO" [TCons "Unit" []]))
        )
    ,
        ( "Data.ByteString.Builder.int16BE"
        , TFun (TCons "Int16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int16Dec"
        , TFun (TCons "Int16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int16HexFixed"
        , TFun (TCons "Int16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int16LE"
        , TFun (TCons "Int16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int32BE"
        , TFun (TCons "Int32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int32Dec"
        , TFun (TCons "Int32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int32HexFixed"
        , TFun (TCons "Int32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int32LE"
        , TFun (TCons "Int32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int64BE"
        , TFun (TCons "Int64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int64Dec"
        , TFun (TCons "Int64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int64HexFixed"
        , TFun (TCons "Int64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int64LE"
        , TFun (TCons "Int64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int8"
        , TFun (TCons "Int8" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int8Dec"
        , TFun (TCons "Int8" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.int8HexFixed"
        , TFun (TCons "Int8" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.intDec"
        , TFun (TCons "Int" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.integerDec"
        , TFun (TCons "Integer" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.lazyByteString"
        , TFun (TCons "ByteString" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.lazyByteStringHex"
        , TFun (TCons "ByteString" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.shortByteString"
        , TFun (TCons "ShortByteString" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.string7"
        , TFun (TCons "List" [TCons "Char" []]) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.string8"
        , TFun (TCons "List" [TCons "Char" []]) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.stringUtf8"
        , TFun (TCons "List" [TCons "Char" []]) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.toLazyByteString"
        , TFun (TCons "Builder" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Builder.word16BE"
        , TFun (TCons "Word16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word16Dec"
        , TFun (TCons "Word16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word16Hex"
        , TFun (TCons "Word16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word16HexFixed"
        , TFun (TCons "Word16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word16LE"
        , TFun (TCons "Word16" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word32BE"
        , TFun (TCons "Word32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word32Dec"
        , TFun (TCons "Word32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word32Hex"
        , TFun (TCons "Word32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word32HexFixed"
        , TFun (TCons "Word32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word32LE"
        , TFun (TCons "Word32" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word64BE"
        , TFun (TCons "Word64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word64Dec"
        , TFun (TCons "Word64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word64Hex"
        , TFun (TCons "Word64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word64HexFixed"
        , TFun (TCons "Word64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word64LE"
        , TFun (TCons "Word64" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word8"
        , TFun (TCons "Word8" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word8Dec"
        , TFun (TCons "Word8" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word8Hex"
        , TFun (TCons "Word8" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.word8HexFixed"
        , TFun (TCons "Word8" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.wordDec"
        , TFun (TCons "Word" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Builder.wordHex"
        , TFun (TCons "Word" []) (TCons "Builder" [])
        )
    ,
        ( "Data.ByteString.Lazy.all"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "Bool" []))
        )
    ,
        ( "Data.ByteString.Lazy.any"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "Bool" []))
        )
    ,
        ( "Data.ByteString.Lazy.append"
        , TFun
            (TCons "ByteString" [])
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.appendFile"
        , TFun
            (TCons "List" [TCons "Char" []])
            (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
        )
    ,
        ( "Data.ByteString.Lazy.break"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            ( TFun
                (TCons "ByteString" [])
                (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
            )
        )
    ,
        ( "Data.ByteString.Lazy.concat"
        , TFun (TCons "List" [TCons "ByteString" []]) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.concatMap"
        , TFun
            (TFun (TCons "Word8" []) (TCons "ByteString" []))
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.cons"
        , TFun
            (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.cons'"
        , TFun
            (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.copy"
        , TFun (TCons "ByteString" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.count"
        , TFun (TCons "Word8" []) (TFun (TCons "ByteString" []) (TCons "Int64" []))
        )
    ,
        ( "Data.ByteString.Lazy.cycle"
        , TFun (TCons "ByteString" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.drop"
        , TFun
            (TCons "Int64" [])
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.dropWhile"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.elem"
        , TFun (TCons "Word8" []) (TFun (TCons "ByteString" []) (TCons "Bool" []))
        )
    ,
        ( "Data.ByteString.Lazy.elemIndex"
        , TFun
            (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Int64" []]))
        )
    ,
        ( "Data.ByteString.Lazy.elemIndexEnd"
        , TFun
            (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Int64" []]))
        )
    ,
        ( "Data.ByteString.Lazy.elemIndices"
        , TFun
            (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "List" [TCons "Int64" []]))
        )
    , ("Data.ByteString.Lazy.empty", TCons "ByteString" [])
    ,
        ( "Data.ByteString.Lazy.filter"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.find"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Word8" []]))
        )
    ,
        ( "Data.ByteString.Lazy.findIndex"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Int64" []]))
        )
    ,
        ( "Data.ByteString.Lazy.findIndices"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "List" [TCons "Int64" []]))
        )
    ,
        ( "Data.ByteString.Lazy.foldl"
        , TFun
            (TFun (TVar "a") (TFun (TCons "Word8" []) (TVar "a")))
            (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
        )
    ,
        ( "Data.ByteString.Lazy.foldl'"
        , TFun
            (TFun (TVar "a") (TFun (TCons "Word8" []) (TVar "a")))
            (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
        )
    ,
        ( "Data.ByteString.Lazy.foldl1"
        , TFun
            (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
            (TFun (TCons "ByteString" []) (TCons "Word8" []))
        )
    ,
        ( "Data.ByteString.Lazy.foldl1'"
        , TFun
            (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
            (TFun (TCons "ByteString" []) (TCons "Word8" []))
        )
    ,
        ( "Data.ByteString.Lazy.foldlChunks"
        , TFun
            (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
            (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
        )
    ,
        ( "Data.ByteString.Lazy.foldr"
        , TFun
            (TFun (TCons "Word8" []) (TFun (TVar "a") (TVar "a")))
            (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
        )
    ,
        ( "Data.ByteString.Lazy.foldr1"
        , TFun
            (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
            (TFun (TCons "ByteString" []) (TCons "Word8" []))
        )
    ,
        ( "Data.ByteString.Lazy.foldrChunks"
        , TFun
            (TFun (TCons "ByteString" []) (TFun (TVar "a") (TVar "a")))
            (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
        )
    ,
        ( "Data.ByteString.Lazy.fromChunks"
        , TFun (TCons "List" [TCons "ByteString" []]) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.fromStrict"
        , TFun (TCons "ByteString" []) (TCons "ByteString" [])
        )
    , ("Data.ByteString.Lazy.getContents", TCons "IO" [TCons "ByteString" []])
    ,
        ( "Data.ByteString.Lazy.group"
        , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.groupBy"
        , TFun
            (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Bool" [])))
            (TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.hGet"
        , TFun
            (TCons "Handle" [])
            (TFun (TCons "Int" []) (TCons "IO" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.hGetContents"
        , TFun (TCons "Handle" []) (TCons "IO" [TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.hGetNonBlocking"
        , TFun
            (TCons "Handle" [])
            (TFun (TCons "Int" []) (TCons "IO" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.hPut"
        , TFun
            (TCons "Handle" [])
            (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
        )
    ,
        ( "Data.ByteString.Lazy.hPutNonBlocking"
        , TFun
            (TCons "Handle" [])
            (TFun (TCons "ByteString" []) (TCons "IO" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.hPutStr"
        , TFun
            (TCons "Handle" [])
            (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
        )
    ,
        ( "Data.ByteString.Lazy.head"
        , TFun (TCons "ByteString" []) (TCons "Word8" [])
        )
    ,
        ( "Data.ByteString.Lazy.index"
        , TFun (TCons "ByteString" []) (TFun (TCons "Int64" []) (TCons "Word8" []))
        )
    ,
        ( "Data.ByteString.Lazy.init"
        , TFun (TCons "ByteString" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.inits"
        , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.interact"
        , TFun
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
            (TCons "IO" [TCons "Unit" []])
        )
    ,
        ( "Data.ByteString.Lazy.intercalate"
        , TFun
            (TCons "ByteString" [])
            (TFun (TCons "List" [TCons "ByteString" []]) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.intersperse"
        , TFun
            (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.isPrefixOf"
        , TFun
            (TCons "ByteString" [])
            (TFun (TCons "ByteString" []) (TCons "Bool" []))
        )
    ,
        ( "Data.ByteString.Lazy.isSuffixOf"
        , TFun
            (TCons "ByteString" [])
            (TFun (TCons "ByteString" []) (TCons "Bool" []))
        )
    ,
        ( "Data.ByteString.Lazy.iterate"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Word8" []))
            (TFun (TCons "Word8" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.last"
        , TFun (TCons "ByteString" []) (TCons "Word8" [])
        )
    ,
        ( "Data.ByteString.Lazy.length"
        , TFun (TCons "ByteString" []) (TCons "Int64" [])
        )
    ,
        ( "Data.ByteString.Lazy.map"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Word8" []))
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.mapAccumL"
        , TFun
            ( TFun
                (TVar "acc")
                (TFun (TCons "Word8" []) (TCons "Pair" [TVar "acc", TCons "Word8" []]))
            )
            ( TFun
                (TVar "acc")
                ( TFun
                    (TCons "ByteString" [])
                    (TCons "Pair" [TVar "acc", TCons "ByteString" []])
                )
            )
        )
    ,
        ( "Data.ByteString.Lazy.mapAccumR"
        , TFun
            ( TFun
                (TVar "acc")
                (TFun (TCons "Word8" []) (TCons "Pair" [TVar "acc", TCons "Word8" []]))
            )
            ( TFun
                (TVar "acc")
                ( TFun
                    (TCons "ByteString" [])
                    (TCons "Pair" [TVar "acc", TCons "ByteString" []])
                )
            )
        )
    ,
        ( "Data.ByteString.Lazy.maximum"
        , TFun (TCons "ByteString" []) (TCons "Word8" [])
        )
    ,
        ( "Data.ByteString.Lazy.minimum"
        , TFun (TCons "ByteString" []) (TCons "Word8" [])
        )
    ,
        ( "Data.ByteString.Lazy.notElem"
        , TFun (TCons "Word8" []) (TFun (TCons "ByteString" []) (TCons "Bool" []))
        )
    ,
        ( "Data.ByteString.Lazy.null"
        , TFun (TCons "ByteString" []) (TCons "Bool" [])
        )
    ,
        ( "Data.ByteString.Lazy.pack"
        , TFun (TCons "List" [TCons "Word8" []]) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.partition"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            ( TFun
                (TCons "ByteString" [])
                (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
            )
        )
    ,
        ( "Data.ByteString.Lazy.putStr"
        , TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []])
        )
    ,
        ( "Data.ByteString.Lazy.putStrLn"
        , TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []])
        )
    ,
        ( "Data.ByteString.Lazy.readFile"
        , TFun (TCons "List" [TCons "Char" []]) (TCons "IO" [TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.repeat"
        , TFun (TCons "Word8" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.replicate"
        , TFun (TCons "Int64" []) (TFun (TCons "Word8" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.reverse"
        , TFun (TCons "ByteString" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.scanl"
        , TFun
            (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
            ( TFun
                (TCons "Word8" [])
                (TFun (TCons "ByteString" []) (TCons "ByteString" []))
            )
        )
    ,
        ( "Data.ByteString.Lazy.singleton"
        , TFun (TCons "Word8" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.snoc"
        , TFun
            (TCons "ByteString" [])
            (TFun (TCons "Word8" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.span"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            ( TFun
                (TCons "ByteString" [])
                (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
            )
        )
    ,
        ( "Data.ByteString.Lazy.split"
        , TFun
            (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.splitAt"
        , TFun
            (TCons "Int64" [])
            ( TFun
                (TCons "ByteString" [])
                (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
            )
        )
    ,
        ( "Data.ByteString.Lazy.splitWith"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.stripPrefix"
        , TFun
            (TCons "ByteString" [])
            (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.stripSuffix"
        , TFun
            (TCons "ByteString" [])
            (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "ByteString" []]))
        )
    ,
        ( "Data.ByteString.Lazy.tail"
        , TFun (TCons "ByteString" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.tails"
        , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.take"
        , TFun
            (TCons "Int64" [])
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.takeWhile"
        , TFun
            (TFun (TCons "Word8" []) (TCons "Bool" []))
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.toChunks"
        , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.toStrict"
        , TFun (TCons "ByteString" []) (TCons "ByteString" [])
        )
    ,
        ( "Data.ByteString.Lazy.transpose"
        , TFun
            (TCons "List" [TCons "ByteString" []])
            (TCons "List" [TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.uncons"
        , TFun
            (TCons "ByteString" [])
            (TCons "Maybe" [TCons "Pair" [TCons "Word8" [], TCons "ByteString" []]])
        )
    ,
        ( "Data.ByteString.Lazy.unfoldr"
        , TFun
            ( TFun
                (TVar "a")
                (TCons "Maybe" [TCons "Pair" [TCons "Word8" [], TVar "a"]])
            )
            (TFun (TVar "a") (TCons "ByteString" []))
        )
    ,
        ( "Data.ByteString.Lazy.unpack"
        , TFun (TCons "ByteString" []) (TCons "List" [TCons "Word8" []])
        )
    ,
        ( "Data.ByteString.Lazy.unsnoc"
        , TFun
            (TCons "ByteString" [])
            (TCons "Maybe" [TCons "Pair" [TCons "ByteString" [], TCons "Word8" []]])
        )
    ,
        ( "Data.ByteString.Lazy.unzip"
        , TFun
            (TCons "List" [TCons "Pair" [TCons "Word8" [], TCons "Word8" []]])
            (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
        )
    ,
        ( "Data.ByteString.Lazy.writeFile"
        , TFun
            (TCons "List" [TCons "Char" []])
            (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
        )
    ,
        ( "Data.ByteString.Lazy.zip"
        , TFun
            (TCons "ByteString" [])
            ( TFun
                (TCons "ByteString" [])
                (TCons "List" [TCons "Pair" [TCons "Word8" [], TCons "Word8" []]])
            )
        )
    ,
        ( "Data.ByteString.Lazy.zipWith"
        , TFun
            (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TVar "a")))
            ( TFun
                (TCons "ByteString" [])
                (TFun (TCons "ByteString" []) (TCons "List" [TVar "a"]))
            )
        )
    , ("Data.Either.Left", TFun (TVar "a") (TCons "Either" [TVar "a", TVar "b"]))
    , ("Data.Either.Right", TFun (TVar "b") (TCons "Either" [TVar "a", TVar "b"]))
    ,
        ( "Data.Either.either"
        , TFun
            (TFun (TVar "a") (TVar "c"))
            ( TFun
                (TFun (TVar "b") (TVar "c"))
                (TFun (TCons "Either" [TVar "a", TVar "b"]) (TVar "c"))
            )
        )
    ,
        ( "Data.Either.fromLeft"
        , TFun (TVar "a") (TFun (TCons "Either" [TVar "a", TVar "b"]) (TVar "a"))
        )
    ,
        ( "Data.Either.fromRight"
        , TFun (TVar "b") (TFun (TCons "Either" [TVar "a", TVar "b"]) (TVar "b"))
        )
    ,
        ( "Data.Either.isLeft"
        , TFun (TCons "Either" [TVar "a", TVar "b"]) (TCons "Bool" [])
        )
    ,
        ( "Data.Either.isRight"
        , TFun (TCons "Either" [TVar "a", TVar "b"]) (TCons "Bool" [])
        )
    ,
        ( "Data.Either.lefts"
        , TFun
            (TCons "List" [TCons "Either" [TVar "a", TVar "b"]])
            (TCons "List" [TVar "a"])
        )
    ,
        ( "Data.Either.partitionEithers"
        , TFun
            (TCons "List" [TCons "Either" [TVar "a", TVar "b"]])
            (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "b"]])
        )
    ,
        ( "Data.Either.rights"
        , TFun
            (TCons "List" [TCons "Either" [TVar "a", TVar "b"]])
            (TCons "List" [TVar "b"])
        )
    ,
        ( "Data.List.group"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TCons "List" [TVar "a"]]))
        )
    , ("Data.Maybe.Just", TFun (TVar "a") (TCons "Maybe" [TVar "a"]))
    , ("Data.Maybe.Nothing", TCons "Maybe" [TVar "a"])
    ,
        ( "Data.Maybe.catMaybes"
        , TFun (TCons "List" [TCons "Maybe" [TVar "a"]]) (TCons "List" [TVar "a"])
        )
    , ("Data.Maybe.fromJust", TFun (TCons "Maybe" [TVar "a"]) (TVar "a"))
    ,
        ( "Data.Maybe.fromMaybe"
        , TFun (TVar "a") (TFun (TCons "Maybe" [TVar "a"]) (TVar "a"))
        )
    , ("Data.Maybe.isJust", TFun (TCons "Maybe" [TVar "a"]) (TCons "Bool" []))
    , ("Data.Maybe.isNothing", TFun (TCons "Maybe" [TVar "a"]) (TCons "Bool" []))
    ,
        ( "Data.Maybe.listToMaybe"
        , TFun (TCons "List" [TVar "a"]) (TCons "Maybe" [TVar "a"])
        )
    ,
        ( "Data.Maybe.mapMaybe"
        , TFun
            (TFun (TVar "a") (TCons "Maybe" [TVar "b"]))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
        )
    ,
        ( "Data.Maybe.maybe"
        , TFun
            (TVar "b")
            ( TFun
                (TFun (TVar "a") (TVar "b"))
                (TFun (TCons "Maybe" [TVar "a"]) (TVar "b"))
            )
        )
    ,
        ( "Data.Maybe.maybeToList"
        , TFun (TCons "Maybe" [TVar "a"]) (TCons "List" [TVar "a"])
        )
    ,
        ( "Data.Tuple.curry"
        , TFun
            (TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "c"))
            (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
        )
    , ("Data.Tuple.fst", TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "a"))
    , ("Data.Tuple.snd", TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "b"))
    ,
        ( "Data.Tuple.swap"
        , TFun
            (TCons "Pair" [TVar "a", TVar "b"])
            (TCons "Pair" [TVar "b", TVar "a"])
        )
    ,
        ( "Data.Tuple.uncurry"
        , TFun
            (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
            (TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "c"))
        )
    , ("GHC.Char.chr", TFun (TCons "Int" []) (TCons "Char" []))
    ,
        ( "GHC.Char.eqChar"
        , TFun (TCons "Char" []) (TFun (TCons "Char" []) (TCons "Bool" []))
        )
    ,
        ( "GHC.Char.neChar"
        , TFun (TCons "Char" []) (TFun (TCons "Char" []) (TCons "Bool" []))
        )
    ,
        ( "GHC.List.all"
        , TFun
            (TFun (TVar "a") (TCons "Bool" []))
            (TFun (TCons "List" [TVar "a"]) (TCons "Bool" []))
        )
    , ("GHC.List.and", TFun (TCons "List" [TCons "Bool" []]) (TCons "Bool" []))
    ,
        ( "GHC.List.any"
        , TFun
            (TFun (TVar "a") (TCons "Bool" []))
            (TFun (TCons "List" [TVar "a"]) (TCons "Bool" []))
        )
    ,
        ( "GHC.List.break"
        , TFun
            (TFun (TVar "a") (TCons "Bool" []))
            ( TFun
                (TCons "List" [TVar "a"])
                (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
            )
        )
    ,
        ( "GHC.List.concat"
        , TFun (TCons "List" [TCons "List" [TVar "a"]]) (TCons "List" [TVar "a"])
        )
    ,
        ( "GHC.List.concatMap"
        , TFun
            (TFun (TVar "a") (TCons "List" [TVar "b"]))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
        )
    , ("GHC.List.cycle", TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    ,
        ( "GHC.List.drop"
        , TFun
            (TCons "Int" [])
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.dropWhile"
        , TFun
            (TFun (TVar "a") (TCons "Bool" []))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.elem"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            (TFun (TVar "a") (TFun (TCons "List" [TVar "a"]) (TCons "Bool" [])))
        )
    ,
        ( "GHC.List.filter"
        , TFun
            (TFun (TVar "a") (TCons "Bool" []))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.foldl"
        , TFun
            (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
            (TFun (TVar "b") (TFun (TCons "List" [TVar "a"]) (TVar "b")))
        )
    ,
        ( "GHC.List.foldl'"
        , TFun
            (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
            (TFun (TVar "b") (TFun (TCons "List" [TVar "a"]) (TVar "b")))
        )
    ,
        ( "GHC.List.foldl1"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    ,
        ( "GHC.List.foldl1'"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    ,
        ( "GHC.List.foldr"
        , TFun
            (TFun (TVar "a") (TFun (TVar "b") (TVar "b")))
            (TFun (TVar "b") (TFun (TCons "List" [TVar "a"]) (TVar "b")))
        )
    ,
        ( "GHC.List.foldr1"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    , ("GHC.List.head", TFun (TCons "List" [TVar "a"]) (TVar "a"))
    , ("GHC.List.init", TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    ,
        ( "GHC.List.iterate"
        , TFun
            (TFun (TVar "a") (TVar "a"))
            (TFun (TVar "a") (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.iterate'"
        , TFun
            (TFun (TVar "a") (TVar "a"))
            (TFun (TVar "a") (TCons "List" [TVar "a"]))
        )
    , ("GHC.List.last", TFun (TCons "List" [TVar "a"]) (TVar "a"))
    , ("GHC.List.length", TFun (TCons "List" [TVar "a"]) (TCons "Int" []))
    ,
        ( "GHC.List.lookup"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            ( TFun
                (TVar "a")
                ( TFun
                    (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
                    (TCons "Maybe" [TVar "b"])
                )
            )
        )
    ,
        ( "GHC.List.map"
        , TFun
            (TFun (TVar "a") (TVar "b"))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
        )
    ,
        ( "GHC.List.maximum"
        , TFun
            (TCons "@@hplusTC@@Ord" [TVar "a"])
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    ,
        ( "GHC.List.minimum"
        , TFun
            (TCons "@@hplusTC@@Ord" [TVar "a"])
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    ,
        ( "GHC.List.notElem"
        , TFun
            (TCons "@@hplusTC@@Eq" [TVar "a"])
            (TFun (TVar "a") (TFun (TCons "List" [TVar "a"]) (TCons "Bool" [])))
        )
    , ("GHC.List.null", TFun (TCons "List" [TVar "a"]) (TCons "Bool" []))
    , ("GHC.List.or", TFun (TCons "List" [TCons "Bool" []]) (TCons "Bool" []))
    ,
        ( "GHC.List.product"
        , TFun
            (TCons "@@hplusTC@@Num" [TVar "a"])
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    , ("GHC.List.repeat", TFun (TVar "a") (TCons "List" [TVar "a"]))
    ,
        ( "GHC.List.replicate"
        , TFun (TCons "Int" []) (TFun (TVar "a") (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.reverse"
        , TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"])
        )
    ,
        ( "GHC.List.scanl"
        , TFun
            (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
            ( TFun
                (TVar "b")
                (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
            )
        )
    ,
        ( "GHC.List.scanl'"
        , TFun
            (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
            ( TFun
                (TVar "b")
                (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
            )
        )
    ,
        ( "GHC.List.scanl1"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.scanr"
        , TFun
            (TFun (TVar "a") (TFun (TVar "b") (TVar "b")))
            ( TFun
                (TVar "b")
                (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
            )
        )
    ,
        ( "GHC.List.scanr1"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.span"
        , TFun
            (TFun (TVar "a") (TCons "Bool" []))
            ( TFun
                (TCons "List" [TVar "a"])
                (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
            )
        )
    ,
        ( "GHC.List.splitAt"
        , TFun
            (TCons "Int" [])
            ( TFun
                (TCons "List" [TVar "a"])
                (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
            )
        )
    ,
        ( "GHC.List.sum"
        , TFun
            (TCons "@@hplusTC@@Num" [TVar "a"])
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    , ("GHC.List.tail", TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    ,
        ( "GHC.List.take"
        , TFun
            (TCons "Int" [])
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.takeWhile"
        , TFun
            (TFun (TVar "a") (TCons "Bool" []))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "GHC.List.uncons"
        , TFun
            (TCons "List" [TVar "a"])
            (TCons "Maybe" [TCons "Pair" [TVar "a", TCons "List" [TVar "a"]]])
        )
    ,
        ( "GHC.List.unzip"
        , TFun
            (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
            (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "b"]])
        )
    ,
        ( "GHC.List.unzip3"
        , TFun
            (TCons "List" [TCons "Pair" [TCons "Pair" [TVar "a", TVar "b"], TVar "c"]])
            ( TCons
                "Pair"
                [ TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "b"]]
                , TCons "List" [TVar "c"]
                ]
            )
        )
    ,
        ( "GHC.List.zip"
        , TFun
            (TCons "List" [TVar "a"])
            ( TFun
                (TCons "List" [TVar "b"])
                (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
            )
        )
    ,
        ( "GHC.List.zip3"
        , TFun
            (TCons "List" [TVar "a"])
            ( TFun
                (TCons "List" [TVar "b"])
                ( TFun
                    (TCons "List" [TVar "c"])
                    ( TCons
                        "List"
                        [TCons "Pair" [TCons "Pair" [TVar "a", TVar "b"], TVar "c"]]
                    )
                )
            )
        )
    ,
        ( "GHC.List.zipWith"
        , TFun
            (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
            ( TFun
                (TCons "List" [TVar "a"])
                (TFun (TCons "List" [TVar "b"]) (TCons "List" [TVar "c"]))
            )
        )
    ,
        ( "GHC.List.zipWith3"
        , TFun
            (TFun (TVar "a") (TFun (TVar "b") (TFun (TVar "c") (TVar "d"))))
            ( TFun
                (TCons "List" [TVar "a"])
                ( TFun
                    (TCons "List" [TVar "b"])
                    (TFun (TCons "List" [TVar "c"]) (TCons "List" [TVar "d"]))
                )
            )
        )
    , ("Nil", TCons "List" [TVar "a"])
    ,
        ( "Pair"
        , TFun (TVar "a") (TFun (TVar "b") (TCons "Pair" [TVar "a", TVar "b"]))
        )
    ,
        ( "Text.Show.show"
        , TFun
            (TCons "@@hplusTC@@Show" [TVar "a"])
            (TFun (TVar "a") (TCons "List" [TCons "Char" []]))
        )
    ,
        ( "Text.Show.showChar"
        , TFun
            (TCons "Char" [])
            (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
        )
    ,
        ( "Text.Show.showList"
        , TFun
            (TCons "@@hplusTC@@Show" [TVar "a"])
            ( TFun
                (TCons "List" [TVar "a"])
                (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
            )
        )
    ,
        ( "Text.Show.showListWith"
        , TFun
            ( TFun
                (TVar "a")
                (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
            )
            ( TFun
                (TCons "List" [TVar "a"])
                (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
            )
        )
    ,
        ( "Text.Show.showParen"
        , TFun
            (TCons "Bool" [])
            ( TFun
                (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
                (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
            )
        )
    ,
        ( "Text.Show.showString"
        , TFun
            (TCons "List" [TCons "Char" []])
            (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
        )
    ,
        ( "Text.Show.shows"
        , TFun
            (TCons "@@hplusTC@@Show" [TVar "a"])
            ( TFun
                (TVar "a")
                (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
            )
        )
    ,
        ( "Text.Show.showsPrec"
        , TFun
            (TCons "@@hplusTC@@Show" [TVar "a"])
            ( TFun
                (TCons "Int" [])
                ( TFun
                    (TVar "a")
                    ( TFun
                        (TCons "List" [TCons "Char" []])
                        (TCons "List" [TCons "Char" []])
                    )
                )
            )
        )
    ]

-- | The components that Hectare adds for the Stack Overflow queries.
augmentedComponents :: [(Text, Type)]
augmentedComponents =
    [
        ( "(Data.Function..)"
        , TFun
            (TFun (TVar "b") (TVar "c"))
            (TFun (TFun (TVar "a") (TVar "b")) (TFun (TVar "a") (TVar "c")))
        )
    ,
        ( "Data.Function.on"
        , TFun
            (TFun (TVar "b") (TFun (TVar "b") (TVar "c")))
            ( TFun
                (TFun (TVar "a") (TVar "b"))
                (TFun (TVar "a") (TFun (TVar "a") (TVar "c")))
            )
        )
    ,
        ( "Data.Function.flip"
        , TFun
            (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
            (TFun (TVar "b") (TFun (TVar "a") (TVar "c")))
        )
    ,
        ( "Data.List.groupBy"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" [])))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TCons "List" [TVar "a"]]))
        )
    ,
        ( "Data.List.sortBy"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TCons "Ordering" [])))
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
        )
    ,
        ( "Data.List.maximumBy"
        , TFun
            (TFun (TVar "a") (TFun (TVar "a") (TCons "Ordering" [])))
            (TFun (TCons "List" [TVar "a"]) (TVar "a"))
        )
    ,
        ( "Data.Ord.compare"
        , TFun
            (TCons "@@hplusTC@@Ord" [TVar "a"])
            (TFun (TVar "a") (TFun (TVar "a") (TCons "Ordering" [])))
        )
    ]

-- | The Hoogle+ benchmark queries.
hooglePlusBenchmarks :: [Benchmark]
hooglePlusBenchmarks =
    [ Benchmark
        { benchmarkName = "appBoth"
        , benchmarkSize = 5
        , benchmarkSolution = Just (App (App (Var "Pair") (App (Var "f") (Var "x"))) (App (Var "g") (Var "x")))
        , benchmarkQuery =
            Query
                [("f", TFun (TVar "a") (TVar "b")), ("g", TFun (TVar "a") (TVar "c")), ("x", TVar "a")]
                (TCons "Pair" [TVar "b", TVar "c"])
        }
    , Benchmark
        { benchmarkName = "test"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just
                (App (App (App (Var "Data.Bool.bool") (Var "Data.Maybe.Nothing")) (App (Var "Data.Maybe.Just") (Var "x"))) (Var "b"))
        , benchmarkQuery = Query [("b", TCons "Bool" []), ("x", TVar "a")] (TCons "Maybe" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "both"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "Pair") (App (Var "f") (App (Var "Data.Tuple.fst") (Var "p"))))
                    (App (Var "f") (App (Var "Data.Tuple.snd") (Var "p")))
                )
        , benchmarkQuery =
            Query [("f", TFun (TVar "a") (TVar "b")), ("p", TCons "Pair" [TVar "a", TVar "a"])] (TCons "Pair" [TVar "b", TVar "b"])
        }
    , Benchmark
        { benchmarkName = "mapEither"
        , benchmarkSize = 4
        , benchmarkSolution =
            Just (App (Var "Data.Either.partitionEithers") (App (App (Var "GHC.List.map") (Var "f")) (Var "xs")))
        , benchmarkQuery =
            Query
                [("f", TFun (TVar "a") (TCons "Either" [TVar "b", TVar "c"])), ("xs", TCons "List" [TVar "a"])]
                (TCons "Pair" [TCons "List" [TVar "b"], TCons "List" [TVar "c"]])
        }
    , Benchmark
        { benchmarkName = "mapMaybes"
        , benchmarkSize = 4
        , benchmarkSolution =
            Just (App (Var "Data.Maybe.listToMaybe") (App (App (Var "Data.Maybe.mapMaybe") (Var "f")) (Var "xs")))
        , benchmarkQuery =
            Query [("f", TFun (TVar "a") (TCons "Maybe" [TVar "b"])), ("xs", TCons "List" [TVar "a"])] (TCons "Maybe" [TVar "b"])
        }
    , Benchmark
        { benchmarkName = "mergeEither"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (App (Var "Data.Either.either") (Var "Data.Either.Left")) (Var "id")) (Var "e"))
        , benchmarkQuery =
            Query [("e", TCons "Either" [TVar "a", TCons "Either" [TVar "a", TVar "b"]])] (TCons "Either" [TVar "a", TVar "b"])
        }
    , Benchmark
        { benchmarkName = "mbToEither"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just
                (App (App (App (Var "Data.Maybe.maybe") (App (Var "Data.Either.Left") (Var "x"))) (Var "Data.Either.Right")) (Var "mb"))
        , benchmarkQuery = Query [("x", TVar "a"), ("mb", TCons "Maybe" [TVar "b"])] (TCons "Either" [TVar "a", TVar "b"])
        }
    , Benchmark
        { benchmarkName = "cartProduct"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "GHC.List.map") (App (Var "GHC.List.zip") (Var "xs")))
                    (App (App (Var "GHC.List.map") (Var "GHC.List.repeat")) (Var "ys"))
                )
        , benchmarkQuery =
            Query
                [("xs", TCons "List" [TVar "a"]), ("ys", TCons "List" [TVar "b"])]
                (TCons "List" [TCons "List" [TCons "Pair" [TVar "a", TVar "b"]]])
        }
    , Benchmark
        { benchmarkName = "multiAppPair"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "Pair") (App (App (Var "Data.Tuple.fst") (Var "tp")) (Var "x")))
                    (App (App (Var "Data.Tuple.snd") (Var "tp")) (Var "x"))
                )
        , benchmarkQuery =
            Query
                [("tp", TCons "Pair" [TFun (TVar "a") (TVar "b"), TFun (TVar "a") (TVar "c")]), ("x", TVar "a")]
                (TCons "Pair" [TVar "b", TVar "c"])
        }
    , Benchmark
        { benchmarkName = "map"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (App (Var "GHC.List.map") (Var "f")) (Var "xs"))
        , benchmarkQuery = Query [("f", TFun (TVar "a") (TVar "b")), ("xs", TCons "List" [TVar "a"])] (TCons "List" [TVar "b"])
        }
    , Benchmark
        { benchmarkName = "replFuncs"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (App (Var "GHC.List.replicate") (Var "n")) (Var "f"))
        , benchmarkQuery =
            Query [("f", TFun (TVar "a") (TVar "b")), ("n", TCons "Int" [])] (TCons "List" [TFun (TVar "a") (TVar "b")])
        }
    , Benchmark
        { benchmarkName = "mbAppFirst"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (App (Var "Data.Maybe.maybe") (Var "x")) (Var "f")) (App (Var "Data.Maybe.listToMaybe") (Var "xs")))
        , benchmarkQuery = Query [("x", TVar "b"), ("f", TFun (TVar "a") (TVar "b")), ("xs", TCons "List" [TVar "a"])] (TVar "b")
        }
    , Benchmark
        { benchmarkName = "mapTwice"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (Var "GHC.List.map") (Var "g")) (App (App (Var "GHC.List.map") (Var "f")) (Var "xs")))
        , benchmarkQuery =
            Query
                [("f", TFun (TVar "a") (TVar "b")), ("g", TFun (TVar "b") (TVar "c")), ("xs", TCons "List" [TVar "a"])]
                (TCons "List" [TVar "c"])
        }
    , Benchmark
        { benchmarkName = "resolveEither"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (App (Var "Data.Either.either") (Var "f")) (Var "id")) (Var "e"))
        , benchmarkQuery = Query [("e", TCons "Either" [TVar "a", TVar "b"]), ("f", TFun (TVar "a") (TVar "b"))] (TVar "b")
        }
    , Benchmark
        { benchmarkName = "firstJust"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "Data.Maybe.fromMaybe") (Var "x"))
                    (App (Var "Data.Maybe.listToMaybe") (App (Var "Data.Maybe.catMaybes") (Var "xs")))
                )
        , benchmarkQuery = Query [("x", TVar "a"), ("xs", TCons "List" [TCons "Maybe" [TVar "a"]])] (TVar "a")
        }
    , Benchmark
        { benchmarkName = "appendN"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (Var "GHC.List.concat") (App (App (Var "GHC.List.replicate") (Var "n")) (Var "xs")))
        , benchmarkQuery = Query [("n", TCons "Int" []), ("xs", TCons "List" [TVar "a"])] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "applyNtimes"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                (App (App (App (Var "GHC.List.foldr") (Var "$")) (Var "x")) (App (App (Var "GHC.List.replicate") (Var "n")) (Var "f")))
        , benchmarkQuery = Query [("f", TFun (TVar "a") (TVar "a")), ("x", TVar "a"), ("n", TCons "Int" [])] (TVar "a")
        }
    , Benchmark
        { benchmarkName = "dedupe"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just
                (App (App (Var "GHC.List.map") (Var "GHC.List.head")) (App (App (Var "Data.List.group") (Var "tcarg0")) (Var "xs")))
        , benchmarkQuery =
            Query [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("xs", TCons "List" [TVar "a"])] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "inverseMap"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (App (Var "GHC.List.zipWith") (Var "$")) (Var "fs")) (App (Var "GHC.List.repeat") (Var "x")))
        , benchmarkQuery = Query [("fs", TCons "List" [TFun (TVar "a") (TVar "b")]), ("x", TVar "a")] (TCons "List" [TVar "b"])
        }
    , Benchmark
        { benchmarkName = "app2"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (Var "f") (Var "x")) (App (Var "g") (Var "x")))
        , benchmarkQuery =
            Query
                [("f", TFun (TVar "a") (TFun (TVar "b") (TVar "c"))), ("g", TFun (TVar "a") (TVar "b")), ("x", TVar "a")]
                (TVar "c")
        }
    , Benchmark
        { benchmarkName = "singletonList"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (App (Var "Cons") (Var "x")) (Var "Nil"))
        , benchmarkQuery = Query [("x", TVar "a")] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "headLast"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (Var "Pair") (App (Var "GHC.List.head") (Var "xs"))) (App (Var "GHC.List.last") (Var "xs")))
        , benchmarkQuery = Query [("xs", TCons "List" [TVar "a"])] (TCons "Pair" [TVar "a", TVar "a"])
        }
    , Benchmark
        { benchmarkName = "headRest"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (Var "Data.Maybe.fromJust") (App (Var "GHC.List.uncons") (Var "xs")))
        , benchmarkQuery = Query [("xs", TCons "List" [TVar "a"])] (TCons "Pair" [TVar "a", TCons "List" [TVar "a"]])
        }
    , Benchmark
        { benchmarkName = "coundPredMatch"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (Var "GHC.List.length") (App (App (Var "GHC.List.filter") (Var "p")) (Var "xs")))
        , benchmarkQuery = Query [("xs", TCons "List" [TVar "a"]), ("p", TFun (TVar "a") (TCons "Bool" []))] (TCons "Int" [])
        }
    , Benchmark
        { benchmarkName = "splitStr"
        , benchmarkSize = 7
        , benchmarkSolution = Nothing
        , benchmarkQuery =
            Query [("str", TCons "List" [TCons "Char" []]), ("c", TCons "Char" [])] (TCons "List" [TCons "List" [TCons "Char" []]])
        }
    , Benchmark
        { benchmarkName = "splitAtFirst"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (Var "GHC.List.break") (App (App (Var "(Data.Eq.==)") (Var "tcarg0")) (Var "x"))) (Var "xs"))
        , benchmarkQuery =
            Query
                [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("x", TVar "a"), ("xs", TCons "List" [TVar "a"])]
                (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
        }
    , Benchmark
        { benchmarkName = "hoogle01"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (Var "f") (App (Var "GHC.List.head") (Var "xs")))
        , benchmarkQuery = Query [("f", TFun (TVar "a") (TVar "b")), ("xs", TCons "List" [TVar "a"])] (TVar "b")
        }
    , Benchmark
        { benchmarkName = "firstMatch"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (Var "GHC.List.head") (App (App (Var "GHC.List.filter") (Var "p")) (Var "xs")))
        , benchmarkQuery = Query [("xs", TCons "List" [TVar "a"]), ("p", TFun (TVar "a") (TCons "Bool" []))] (TVar "a")
        }
    , Benchmark
        { benchmarkName = "firstMaybe"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (Var "GHC.List.head") (App (Var "Data.Maybe.catMaybes") (Var "mbs")))
        , benchmarkQuery = Query [("mbs", TCons "List" [TCons "Maybe" [TVar "a"]])] (TVar "a")
        }
    , Benchmark
        { benchmarkName = "rights"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (Var "Data.Either.Right") (App (Var "Data.Either.rights") (Var "es")))
        , benchmarkQuery =
            Query [("es", TCons "List" [TCons "Either" [TVar "a", TVar "b"]])] (TCons "Either" [TVar "a", TCons "List" [TVar "b"]])
        }
    , Benchmark
        { benchmarkName = "firstKey"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (Var "Data.Tuple.fst") (App (Var "GHC.List.head") (Var "xs")))
        , benchmarkQuery = Query [("xs", TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])] (TVar "a")
        }
    , Benchmark
        { benchmarkName = "firstRight"
        , benchmarkSize = 4
        , benchmarkSolution =
            Just (App (Var "Data.Either.Right") (App (Var "GHC.List.head") (App (Var "Data.Either.rights") (Var "es"))))
        , benchmarkQuery =
            Query [("es", TCons "List" [TCons "Either" [TVar "a", TVar "b"]])] (TCons "Either" [TVar "a", TVar "b"])
        }
    , Benchmark
        { benchmarkName = "maybe"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (Var "Data.Maybe.Just") (App (App (Var "Data.Maybe.fromMaybe") (Var "x")) (Var "mb")))
        , benchmarkQuery = Query [("mb", TCons "Maybe" [TVar "a"]), ("x", TVar "a")] (TCons "Maybe" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "app3"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (App (Var "f") (Var "x")) (Var "z")) (Var "y"))
        , benchmarkQuery =
            Query
                [ ("f", TFun (TVar "a") (TFun (TVar "b") (TFun (TVar "c") (TVar "d"))))
                , ("x", TVar "a")
                , ("y", TVar "c")
                , ("z", TVar "b")
                ]
                (TVar "d")
        }
    , Benchmark
        { benchmarkName = "zipWithResult"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (Var "GHC.List.zip") (Var "xs")) (App (App (Var "GHC.List.map") (Var "f")) (Var "xs")))
        , benchmarkQuery =
            Query
                [("f", TFun (TVar "a") (TVar "b")), ("xs", TCons "List" [TVar "a"])]
                (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
        }
    , Benchmark
        { benchmarkName = "eitherTriple"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (App (Var "Data.Bool.bool") (Var "e2")) (Var "e1")) (App (Var "Data.Either.isLeft") (Var "e1")))
        , benchmarkQuery =
            Query
                [("e1", TCons "Either" [TVar "a", TVar "b"]), ("e2", TCons "Either" [TVar "a", TVar "b"])]
                (TCons "Either" [TVar "a", TVar "b"])
        }
    , Benchmark
        { benchmarkName = "pipe"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (App (Var "GHC.List.foldr") (Var "$")) (Var "x")) (Var "fs"))
        , benchmarkQuery = Query [("fs", TCons "List" [TFun (TVar "a") (TVar "a")]), ("x", TVar "a")] (TVar "a")
        }
    , Benchmark
        { benchmarkName = "lookup"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (Var "Data.Maybe.fromJust") (App (App (App (Var "GHC.List.lookup") (Var "tcarg0")) (Var "k")) (Var "xs")))
        , benchmarkQuery =
            Query
                [ ("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"])
                , ("xs", TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
                , ("k", TVar "a")
                ]
                (TVar "b")
        }
    , Benchmark
        { benchmarkName = "mbElem"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    (Var "Data.Maybe.listToMaybe")
                    (App (App (Var "GHC.List.filter") (App (App (Var "(Data.Eq.==)") (Var "tcarg0")) (Var "x"))) (Var "xs"))
                )
        , benchmarkQuery =
            Query
                [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("x", TVar "a"), ("xs", TCons "List" [TVar "a"])]
                (TCons "Maybe" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "areEq"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    (Var "Data.Maybe.listToMaybe")
                    ( App
                        (App (Var "GHC.List.filter") (App (App (Var "(Data.Eq.==)") (Var "tcarg0")) (Var "x")))
                        (App (Var "GHC.List.repeat") (Var "y"))
                    )
                )
        , benchmarkQuery =
            Query [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("x", TVar "a"), ("y", TVar "a")] (TCons "Maybe" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "applyPair"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (Var "Data.Tuple.fst") (Var "p")) (App (Var "Data.Tuple.snd") (Var "p")))
        , benchmarkQuery = Query [("p", TCons "Pair" [TFun (TVar "a") (TVar "b"), TVar "a"])] (TVar "b")
        }
    , Benchmark
        { benchmarkName = "flatten"
        , benchmarkSize = 3
        , benchmarkSolution = Just (App (Var "GHC.List.concat") (App (Var "GHC.List.concat") (Var "xss")))
        , benchmarkQuery = Query [("xss", TCons "List" [TCons "List" [TCons "List" [TVar "a"]]])] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "takeNdropM"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "Pair") (App (App (Var "GHC.List.take") (Var "n")) (Var "xs")))
                    (App (App (Var "GHC.List.drop") (Var "m")) (Var "xs"))
                )
        , benchmarkQuery =
            Query
                [("n", TCons "Int" []), ("m", TCons "Int" []), ("xs", TCons "List" [TVar "a"])]
                (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
        }
    , Benchmark
        { benchmarkName = "indexesOf"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "GHC.List.map") (Var "Data.Tuple.snd"))
                    (App (Var "f") (App (App (Var "GHC.List.zip") (Var "xs")) (Var "ys")))
                )
        , benchmarkQuery =
            Query
                [
                    ( "f"
                    , TFun (TCons "List" [TCons "Pair" [TVar "a", TCons "Int" []]]) (TCons "List" [TCons "Pair" [TVar "a", TCons "Int" []]])
                    )
                , ("xs", TCons "List" [TVar "a"])
                , ("ys", TCons "List" [TCons "Int" []])
                ]
                (TCons "List" [TCons "Int" []])
        }
    , Benchmark
        { benchmarkName = "containsEdge"
        , benchmarkSize = 9
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "(Data.Bool.&&)") (App (App (Var "GHC.List.elem") (App (Var "Data.Tuple.fst") (Var "edge"))) (Var "vs")))
                    (App (App (Var "GHC.List.elem") (App (Var "Data.Tuple.snd") (Var "edge"))) (Var "vs"))
                )
        , benchmarkQuery =
            Query [("vs", TCons "List" [TCons "Int" []]), ("edge", TCons "Pair" [TCons "Int" [], TCons "Int" []])] (TCons "Bool" [])
        }
    ]

-- | The Stack Overflow benchmark queries, which need 'hooglePlusWithAugmented'.
stackOverflowBenchmarks :: [Benchmark]
stackOverflowBenchmarks =
    [ Benchmark
        { benchmarkName = "extractEitherValues"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just (App (App (Var "GHC.List.map") (App (App (Var "Data.Either.either") (Var "id")) (Var "id"))) (Var "es"))
        , benchmarkQuery = Query [("es", TCons "List" [TCons "Either" [TVar "b", TVar "b"]])] (TCons "List" [TVar "b"])
        }
    , Benchmark
        { benchmarkName = "filterMultiple"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "GHC.List.filter") (App (App (Var "Data.Function.flip") (App (Var "GHC.List.elem") (Var "tcarg0"))) (Var "xs")))
                    (Var "ys")
                )
        , benchmarkQuery =
            Query
                [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("xs", TCons "List" [TVar "a"]), ("ys", TCons "List" [TVar "a"])]
                (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "filterNot"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just
                (App (App (Var "GHC.List.filter") (App (App (Var "(Data.Function..)") (Var "Data.Bool.not")) (Var "p"))) (Var "xs"))
        , benchmarkQuery =
            Query [("p", TFun (TVar "a") (TCons "Bool" [])), ("xs", TCons "List" [TVar "a"])] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "isSortedBy"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    (Var "GHC.List.and")
                    (App (App (App (Var "GHC.List.zipWith") (Var "cmp")) (Var "xs")) (App (Var "GHC.List.tail") (Var "xs")))
                )
        , benchmarkQuery =
            Query [("cmp", TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" []))), ("xs", TCons "List" [TVar "a"])] (TCons "Bool" [])
        }
    , Benchmark
        { benchmarkName = "multipleNth"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (Var "GHC.List.map") (App (Var "(GHC.List.!!)") (Var "xs"))) (Var "indices"))
        , benchmarkQuery =
            Query [("xs", TCons "List" [TVar "a"]), ("indices", TCons "List" [TCons "Int" []])] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "doubleMap"
        , benchmarkSize = 4
        , benchmarkSolution = Just (App (App (Var "GHC.List.map") (App (Var "GHC.List.map") (Var "f"))) (Var "xss"))
        , benchmarkQuery =
            Query
                [("f", TFun (TVar "a") (TVar "b")), ("xss", TCons "List" [TCons "List" [TVar "a"]])]
                (TCons "List" [TCons "List" [TVar "b"]])
        }
    , Benchmark
        { benchmarkName = "lengthOfSnds"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just
                ( App
                    (Var "GHC.List.length")
                    (App (Var "GHC.List.concat") (App (App (Var "GHC.List.map") (Var "Data.Tuple.snd")) (Var "ps")))
                )
        , benchmarkQuery = Query [("ps", TCons "List" [TCons "Pair" [TVar "a", TCons "List" [TVar "b"]]])] (TCons "Int" [])
        }
    , Benchmark
        { benchmarkName = "lessThanNTimes"
        , benchmarkSize = 8
        , benchmarkSolution =
            Just
                ( App
                    (Var "GHC.List.null")
                    ( App
                        (App (Var "GHC.List.drop") (Var "n"))
                        (App (App (Var "GHC.List.filter") (App (App (Var "(Data.Eq.==)") (Var "tcarg0")) (Var "x"))) (Var "xs"))
                    )
                )
        , benchmarkQuery =
            Query
                [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("n", TCons "Int" []), ("x", TVar "a"), ("xs", TCons "List" [TVar "a"])]
                (TCons "Bool" [])
        }
    , Benchmark
        { benchmarkName = "groupByFirst"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    ( App
                        (Var "Data.List.groupBy")
                        (App (App (Var "Data.Function.on") (App (Var "(Data.Eq.==)") (Var "tcarg0"))) (Var "Data.Tuple.fst"))
                    )
                    (Var "xs")
                )
        , benchmarkQuery =
            Query
                [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("xs", TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])]
                (TCons "List" [TCons "List" [TCons "Pair" [TVar "a", TVar "b"]]])
        }
    , Benchmark
        { benchmarkName = "mySortBy"
        , benchmarkSize = 5
        , benchmarkSolution =
            Just
                (App (App (Var "Data.List.sortBy") (App (App (Var "Data.Function.on") (Var "cmp")) (Var "Data.Tuple.fst"))) (Var "xs"))
        , benchmarkQuery =
            Query
                [ ("cmp", TFun (TVar "a") (TFun (TVar "a") (TCons "Ordering" [])))
                , ("xs", TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
                ]
                (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
        }
    , Benchmark
        { benchmarkName = "transpose"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    (App (App (Var "GHC.List.foldr") (App (Var "GHC.List.zipWith") (Var "Cons"))) (App (Var "GHC.List.repeat") (Var "Nil")))
                    (Var "xs")
                )
        , benchmarkQuery = Query [("xs", TCons "List" [TCons "List" [TVar "a"]])] (TCons "List" [TCons "List" [TVar "a"]])
        }
    , Benchmark
        { benchmarkName = "partition"
        , benchmarkSize = 9
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "Pair") (App (App (Var "GHC.List.filter") (Var "p")) (Var "xs")))
                    (App (App (Var "GHC.List.filter") (App (App (Var "(Data.Function..)") (Var "Data.Bool.not")) (Var "p"))) (Var "xs"))
                )
        , benchmarkQuery =
            Query
                [("p", TFun (TVar "a") (TCons "Bool" [])), ("xs", TCons "List" [TVar "a"])]
                (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
        }
    , Benchmark
        { benchmarkName = "matchedKeys"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "GHC.List.map") (Var "Data.Tuple.fst"))
                    (App (App (Var "GHC.List.filter") (App (App (Var "(Data.Function..)") (Var "p")) (Var "Data.Tuple.snd"))) (Var "xs"))
                )
        , benchmarkQuery =
            Query
                [("p", TFun (TVar "b") (TCons "Bool" [])), ("xs", TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])]
                (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "filterPairs"
        , benchmarkSize = 6
        , benchmarkSolution =
            Just
                ( App
                    (App (Var "GHC.List.filter") (App (Var "Data.Tuple.uncurry") (Var "f")))
                    (App (App (Var "GHC.List.zip") (Var "xs")) (Var "ys"))
                )
        , benchmarkQuery =
            Query
                [ ("f", TFun (TVar "a") (TFun (TVar "b") (TCons "Bool" [])))
                , ("xs", TCons "List" [TVar "a"])
                , ("ys", TCons "List" [TVar "b"])
                ]
                (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
        }
    , Benchmark
        { benchmarkName = "applyNthNTimes"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    ( App
                        (App (Var "GHC.List.zipWith") (Var "$"))
                        (App (App (Var "GHC.List.iterate") (App (Var "(Data.Function..)") (Var "f"))) (Var "f"))
                    )
                    (Var "xs")
                )
        , benchmarkQuery = Query [("f", TFun (TVar "a") (TVar "a")), ("xs", TCons "List" [TVar "a"])] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "removeMax"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    ( App
                        (Var "GHC.List.filter")
                        (App (App (Var "(Data.Eq./=)_Ord") (Var "tcarg0")) (App (App (Var "GHC.List.maximum") (Var "tcarg0")) (Var "xs")))
                    )
                    (Var "xs")
                )
        , benchmarkQuery =
            Query [("tcarg0", TCons "@@hplusTC@@Ord" [TVar "a"]), ("xs", TCons "List" [TVar "a"])] (TCons "List" [TVar "a"])
        }
    , Benchmark
        { benchmarkName = "allSameBy"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    ( App
                        (Var "GHC.List.all")
                        (App (App (App (Var "Data.Function.on") (App (Var "(Data.Eq.==)") (Var "tcarg0"))) (Var "cmp")) (Var "xs"))
                    )
                    (Var "xss")
                )
        , benchmarkQuery =
            Query
                [ ("tcarg0", TCons "@@hplusTC@@Eq" [TVar "b"])
                , ("cmp", TFun (TVar "a") (TVar "b"))
                , ("xs", TVar "a")
                , ("xss", TCons "List" [TVar "a"])
                ]
                (TCons "Bool" [])
        }
    , Benchmark
        { benchmarkName = "mostFrequent"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    ( App
                        (Var "Data.List.maximumBy")
                        (App (App (Var "Data.Function.on") (App (Var "Data.Ord.compare") (Var "tcarg0"))) (Var "Data.Tuple.snd"))
                    )
                    (App (Var "occur") (Var "xs"))
                )
        , benchmarkQuery =
            Query
                [ ("tcarg0", TCons "@@hplusTC@@Ord" [TVar "b"])
                , ("xs", TCons "List" [TVar "a"])
                , ("occur", TFun (TCons "List" [TVar "a"]) (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]]))
                ]
                (TCons "Pair" [TVar "a", TVar "b"])
        }
    , Benchmark
        { benchmarkName = "splitOn"
        , benchmarkSize = 7
        , benchmarkSolution =
            Just
                ( App
                    ( App
                        (Var "Data.List.groupBy")
                        (App (App (Var "Data.Function.on") (Var "(Data.Bool.&&)")) (App (App (Var "(Data.Eq./=)") (Var "tcarg0")) (Var "x")))
                    )
                    (Var "xs")
                )
        , benchmarkQuery =
            Query
                [("tcarg0", TCons "@@hplusTC@@Eq" [TVar "a"]), ("x", TVar "a"), ("xs", TCons "List" [TVar "a"])]
                (TCons "List" [TCons "List" [TVar "a"]])
        }
    ]
