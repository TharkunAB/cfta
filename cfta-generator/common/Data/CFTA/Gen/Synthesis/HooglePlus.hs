{-# LANGUAGE OverloadedStrings #-}

{- | The Hoogle+ component library and benchmark queries of the ECTA paper.

The components are the 284 Hoogle+ components of Guo et al., /Program
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
import qualified Data.Text as Text

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
withComponents allComponents =
    library
        [component | component@(name, _) <- allComponents, name `notElem` ["(Data.Function.$)", "Data.Function.id"]]
        [("$", typ "(a -> b) -> a -> b"), ("id", typ "a -> a")]
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

-- | Components with their types in Haskell syntax.
components :: [(Text, Text)] -> [(Text, Type)]
components = map (fmap typ)

{- | A benchmark from its name, its size, its solution, its arguments as
@name :: type@, and its goal type.
-}
benchmark :: Text -> Int -> Maybe Text -> [Text] -> Text -> Benchmark
benchmark name size solution arguments goal =
    Benchmark
        { benchmarkName = name
        , benchmarkSize = size
        , benchmarkSolution = program <$> solution
        , benchmarkQuery = Query (map argument arguments) (typ goal)
        }
  where
    argument text = case Text.splitOn " :: " text of
        [argumentName, argumentType] -> (argumentName, typ argumentType)
        _ -> error ("cannot parse the argument " <> show text)

-- | A type in Haskell syntax. A parse error stops the program.
typ :: Text -> Type
typ = either error id . parseType

-- | A program in Haskell syntax. A parse error stops the program.
program :: Text -> Program
program = either error id . parseProgram

-- | The 284 Hoogle+ components.
hooglePlusComponents :: [(Text, Type)]
hooglePlusComponents =
    components
        [ ("(Data.Bool.&&)", "Bool -> Bool -> Bool")
        , ("(Data.Bool.||)", "Bool -> Bool -> Bool")
        , ("(Data.Eq./=)", "Eq a => a -> a -> Bool")
        , ("(Data.Eq.==)", "Eq a => a -> a -> Bool")
        , ("(Data.Function.$)", "(a -> b) -> a -> b")
        , ("(GHC.List.!!)", "[a] -> Int -> a")
        , ("(GHC.List.++)", "[a] -> [a] -> [a]")
        , ("@@hplusTCInstance@@0EqBool", "@@hplusTC@@Eq Bool")
        , ("@@hplusTCInstance@@0EqChar", "@@hplusTC@@Eq Char")
        , ("@@hplusTCInstance@@0EqDouble", "@@hplusTC@@Eq Double")
        , ("@@hplusTCInstance@@0EqFloat", "@@hplusTC@@Eq Float")
        , ("@@hplusTCInstance@@0EqInt", "@@hplusTC@@Eq Int")
        , ("@@hplusTCInstance@@0EqUnit", "@@hplusTC@@Eq ()")
        , ("@@hplusTCInstance@@0IsString", "@@hplusTC@@IsString Builder")
        , ("@@hplusTCInstance@@0NumDouble", "@@hplusTC@@Num Double")
        , ("@@hplusTCInstance@@0NumFloat", "@@hplusTC@@Num Float")
        , ("@@hplusTCInstance@@0NumInt", "@@hplusTC@@Num Int")
        , ("@@hplusTCInstance@@0OrdBool", "@@hplusTC@@Ord Bool")
        , ("@@hplusTCInstance@@0OrdChar", "@@hplusTC@@Ord Char")
        , ("@@hplusTCInstance@@0OrdDouble", "@@hplusTC@@Ord Double")
        , ("@@hplusTCInstance@@0OrdFloat", "@@hplusTC@@Ord Float")
        , ("@@hplusTCInstance@@0OrdInt", "@@hplusTC@@Ord Int")
        , ("@@hplusTCInstance@@0ShowBool", "@@hplusTC@@Show Bool")
        , ("@@hplusTCInstance@@0ShowChar", "@@hplusTC@@Show Char")
        , ("@@hplusTCInstance@@0ShowDouble", "@@hplusTC@@Show Double")
        , ("@@hplusTCInstance@@0ShowFloat", "@@hplusTC@@Show Float")
        , ("@@hplusTCInstance@@0ShowInt", "@@hplusTC@@Show Int")
        , ("@@hplusTCInstance@@0ShowUnit", "@@hplusTC@@Show ()")
        , ("@@hplusTCInstance@@1Show", "(Show a, Show b) => @@hplusTC@@Show (Either a b)")
        , ("@@hplusTCInstance@@2Read", "(Read a, Read b) => @@hplusTC@@Read (Either a b)")
        , ("@@hplusTCInstance@@3Ord", "(Ord a, Ord b) => @@hplusTC@@Ord (Either a b)")
        , ("@@hplusTCInstance@@4Eq", "(Eq a, Eq b) => @@hplusTC@@Eq (Either a b)")
        , ("@@hplusTCInstance@@6Semigroup", "@@hplusTC@@Semigroup (Either a b)")
        , ("@@hplusTCInstance@@9Eq", "Eq a => @@hplusTC@@Eq [a]")
        , ("Cons", "a -> [a] -> [a]")
        , ("Data.Bool.False", "Bool")
        , ("Data.Bool.True", "Bool")
        , ("Data.Bool.bool", "a -> a -> Bool -> a")
        , ("Data.Bool.not", "Bool -> Bool")
        , ("Data.Bool.otherwise", "Bool")
        , ("Data.ByteString.Builder.byteString", "ByteString -> Builder")
        , ("Data.ByteString.Builder.byteStringHex", "ByteString -> Builder")
        , ("Data.ByteString.Builder.char7", "Char -> Builder")
        , ("Data.ByteString.Builder.char8", "Char -> Builder")
        , ("Data.ByteString.Builder.charUtf8", "Char -> Builder")
        , ("Data.ByteString.Builder.doubleBE", "Double -> Builder")
        , ("Data.ByteString.Builder.doubleDec", "Double -> Builder")
        , ("Data.ByteString.Builder.doubleHexFixed", "Double -> Builder")
        , ("Data.ByteString.Builder.doubleLE", "Double -> Builder")
        , ("Data.ByteString.Builder.floatBE", "Float -> Builder")
        , ("Data.ByteString.Builder.floatDec", "Float -> Builder")
        , ("Data.ByteString.Builder.floatHexFixed", "Float -> Builder")
        , ("Data.ByteString.Builder.floatLE", "Float -> Builder")
        , ("Data.ByteString.Builder.hPutBuilder", "Handle -> Builder -> IO ()")
        , ("Data.ByteString.Builder.int16BE", "Int16 -> Builder")
        , ("Data.ByteString.Builder.int16Dec", "Int16 -> Builder")
        , ("Data.ByteString.Builder.int16HexFixed", "Int16 -> Builder")
        , ("Data.ByteString.Builder.int16LE", "Int16 -> Builder")
        , ("Data.ByteString.Builder.int32BE", "Int32 -> Builder")
        , ("Data.ByteString.Builder.int32Dec", "Int32 -> Builder")
        , ("Data.ByteString.Builder.int32HexFixed", "Int32 -> Builder")
        , ("Data.ByteString.Builder.int32LE", "Int32 -> Builder")
        , ("Data.ByteString.Builder.int64BE", "Int64 -> Builder")
        , ("Data.ByteString.Builder.int64Dec", "Int64 -> Builder")
        , ("Data.ByteString.Builder.int64HexFixed", "Int64 -> Builder")
        , ("Data.ByteString.Builder.int64LE", "Int64 -> Builder")
        , ("Data.ByteString.Builder.int8", "Int8 -> Builder")
        , ("Data.ByteString.Builder.int8Dec", "Int8 -> Builder")
        , ("Data.ByteString.Builder.int8HexFixed", "Int8 -> Builder")
        , ("Data.ByteString.Builder.intDec", "Int -> Builder")
        , ("Data.ByteString.Builder.integerDec", "Integer -> Builder")
        , ("Data.ByteString.Builder.lazyByteString", "ByteString -> Builder")
        , ("Data.ByteString.Builder.lazyByteStringHex", "ByteString -> Builder")
        , ("Data.ByteString.Builder.shortByteString", "ShortByteString -> Builder")
        , ("Data.ByteString.Builder.string7", "[Char] -> Builder")
        , ("Data.ByteString.Builder.string8", "[Char] -> Builder")
        , ("Data.ByteString.Builder.stringUtf8", "[Char] -> Builder")
        , ("Data.ByteString.Builder.toLazyByteString", "Builder -> ByteString")
        , ("Data.ByteString.Builder.word16BE", "Word16 -> Builder")
        , ("Data.ByteString.Builder.word16Dec", "Word16 -> Builder")
        , ("Data.ByteString.Builder.word16Hex", "Word16 -> Builder")
        , ("Data.ByteString.Builder.word16HexFixed", "Word16 -> Builder")
        , ("Data.ByteString.Builder.word16LE", "Word16 -> Builder")
        , ("Data.ByteString.Builder.word32BE", "Word32 -> Builder")
        , ("Data.ByteString.Builder.word32Dec", "Word32 -> Builder")
        , ("Data.ByteString.Builder.word32Hex", "Word32 -> Builder")
        , ("Data.ByteString.Builder.word32HexFixed", "Word32 -> Builder")
        , ("Data.ByteString.Builder.word32LE", "Word32 -> Builder")
        , ("Data.ByteString.Builder.word64BE", "Word64 -> Builder")
        , ("Data.ByteString.Builder.word64Dec", "Word64 -> Builder")
        , ("Data.ByteString.Builder.word64Hex", "Word64 -> Builder")
        , ("Data.ByteString.Builder.word64HexFixed", "Word64 -> Builder")
        , ("Data.ByteString.Builder.word64LE", "Word64 -> Builder")
        , ("Data.ByteString.Builder.word8", "Word8 -> Builder")
        , ("Data.ByteString.Builder.word8Dec", "Word8 -> Builder")
        , ("Data.ByteString.Builder.word8Hex", "Word8 -> Builder")
        , ("Data.ByteString.Builder.word8HexFixed", "Word8 -> Builder")
        , ("Data.ByteString.Builder.wordDec", "Word -> Builder")
        , ("Data.ByteString.Builder.wordHex", "Word -> Builder")
        , ("Data.ByteString.Lazy.all", "(Word8 -> Bool) -> ByteString -> Bool")
        , ("Data.ByteString.Lazy.any", "(Word8 -> Bool) -> ByteString -> Bool")
        , ("Data.ByteString.Lazy.append", "ByteString -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.appendFile", "[Char] -> ByteString -> IO ()")
        , ("Data.ByteString.Lazy.break", "(Word8 -> Bool) -> ByteString -> (ByteString, ByteString)")
        , ("Data.ByteString.Lazy.concat", "[ByteString] -> ByteString")
        , ("Data.ByteString.Lazy.concatMap", "(Word8 -> ByteString) -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.cons", "Word8 -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.cons'", "Word8 -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.copy", "ByteString -> ByteString")
        , ("Data.ByteString.Lazy.count", "Word8 -> ByteString -> Int64")
        , ("Data.ByteString.Lazy.cycle", "ByteString -> ByteString")
        , ("Data.ByteString.Lazy.drop", "Int64 -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.dropWhile", "(Word8 -> Bool) -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.elem", "Word8 -> ByteString -> Bool")
        , ("Data.ByteString.Lazy.elemIndex", "Word8 -> ByteString -> Maybe Int64")
        , ("Data.ByteString.Lazy.elemIndexEnd", "Word8 -> ByteString -> Maybe Int64")
        , ("Data.ByteString.Lazy.elemIndices", "Word8 -> ByteString -> [Int64]")
        , ("Data.ByteString.Lazy.empty", "ByteString")
        , ("Data.ByteString.Lazy.filter", "(Word8 -> Bool) -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.find", "(Word8 -> Bool) -> ByteString -> Maybe Word8")
        , ("Data.ByteString.Lazy.findIndex", "(Word8 -> Bool) -> ByteString -> Maybe Int64")
        , ("Data.ByteString.Lazy.findIndices", "(Word8 -> Bool) -> ByteString -> [Int64]")
        , ("Data.ByteString.Lazy.foldl", "(a -> Word8 -> a) -> a -> ByteString -> a")
        , ("Data.ByteString.Lazy.foldl'", "(a -> Word8 -> a) -> a -> ByteString -> a")
        , ("Data.ByteString.Lazy.foldl1", "(Word8 -> Word8 -> Word8) -> ByteString -> Word8")
        , ("Data.ByteString.Lazy.foldl1'", "(Word8 -> Word8 -> Word8) -> ByteString -> Word8")
        , ("Data.ByteString.Lazy.foldlChunks", "(a -> ByteString -> a) -> a -> ByteString -> a")
        , ("Data.ByteString.Lazy.foldr", "(Word8 -> a -> a) -> a -> ByteString -> a")
        , ("Data.ByteString.Lazy.foldr1", "(Word8 -> Word8 -> Word8) -> ByteString -> Word8")
        , ("Data.ByteString.Lazy.foldrChunks", "(ByteString -> a -> a) -> a -> ByteString -> a")
        , ("Data.ByteString.Lazy.fromChunks", "[ByteString] -> ByteString")
        , ("Data.ByteString.Lazy.fromStrict", "ByteString -> ByteString")
        , ("Data.ByteString.Lazy.getContents", "IO ByteString")
        , ("Data.ByteString.Lazy.group", "ByteString -> [ByteString]")
        , ("Data.ByteString.Lazy.groupBy", "(Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]")
        , ("Data.ByteString.Lazy.hGet", "Handle -> Int -> IO ByteString")
        , ("Data.ByteString.Lazy.hGetContents", "Handle -> IO ByteString")
        , ("Data.ByteString.Lazy.hGetNonBlocking", "Handle -> Int -> IO ByteString")
        , ("Data.ByteString.Lazy.hPut", "Handle -> ByteString -> IO ()")
        , ("Data.ByteString.Lazy.hPutNonBlocking", "Handle -> ByteString -> IO ByteString")
        , ("Data.ByteString.Lazy.hPutStr", "Handle -> ByteString -> IO ()")
        , ("Data.ByteString.Lazy.head", "ByteString -> Word8")
        , ("Data.ByteString.Lazy.index", "ByteString -> Int64 -> Word8")
        , ("Data.ByteString.Lazy.init", "ByteString -> ByteString")
        , ("Data.ByteString.Lazy.inits", "ByteString -> [ByteString]")
        , ("Data.ByteString.Lazy.interact", "(ByteString -> ByteString) -> IO ()")
        , ("Data.ByteString.Lazy.intercalate", "ByteString -> [ByteString] -> ByteString")
        , ("Data.ByteString.Lazy.intersperse", "Word8 -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.isPrefixOf", "ByteString -> ByteString -> Bool")
        , ("Data.ByteString.Lazy.isSuffixOf", "ByteString -> ByteString -> Bool")
        , ("Data.ByteString.Lazy.iterate", "(Word8 -> Word8) -> Word8 -> ByteString")
        , ("Data.ByteString.Lazy.last", "ByteString -> Word8")
        , ("Data.ByteString.Lazy.length", "ByteString -> Int64")
        , ("Data.ByteString.Lazy.map", "(Word8 -> Word8) -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.mapAccumL", "(acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)")
        , ("Data.ByteString.Lazy.mapAccumR", "(acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)")
        , ("Data.ByteString.Lazy.maximum", "ByteString -> Word8")
        , ("Data.ByteString.Lazy.minimum", "ByteString -> Word8")
        , ("Data.ByteString.Lazy.notElem", "Word8 -> ByteString -> Bool")
        , ("Data.ByteString.Lazy.null", "ByteString -> Bool")
        , ("Data.ByteString.Lazy.pack", "[Word8] -> ByteString")
        , ("Data.ByteString.Lazy.partition", "(Word8 -> Bool) -> ByteString -> (ByteString, ByteString)")
        , ("Data.ByteString.Lazy.putStr", "ByteString -> IO ()")
        , ("Data.ByteString.Lazy.putStrLn", "ByteString -> IO ()")
        , ("Data.ByteString.Lazy.readFile", "[Char] -> IO ByteString")
        , ("Data.ByteString.Lazy.repeat", "Word8 -> ByteString")
        , ("Data.ByteString.Lazy.replicate", "Int64 -> Word8 -> ByteString")
        , ("Data.ByteString.Lazy.reverse", "ByteString -> ByteString")
        , ("Data.ByteString.Lazy.scanl", "(Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.singleton", "Word8 -> ByteString")
        , ("Data.ByteString.Lazy.snoc", "ByteString -> Word8 -> ByteString")
        , ("Data.ByteString.Lazy.span", "(Word8 -> Bool) -> ByteString -> (ByteString, ByteString)")
        , ("Data.ByteString.Lazy.split", "Word8 -> ByteString -> [ByteString]")
        , ("Data.ByteString.Lazy.splitAt", "Int64 -> ByteString -> (ByteString, ByteString)")
        , ("Data.ByteString.Lazy.splitWith", "(Word8 -> Bool) -> ByteString -> [ByteString]")
        , ("Data.ByteString.Lazy.stripPrefix", "ByteString -> ByteString -> Maybe ByteString")
        , ("Data.ByteString.Lazy.stripSuffix", "ByteString -> ByteString -> Maybe ByteString")
        , ("Data.ByteString.Lazy.tail", "ByteString -> ByteString")
        , ("Data.ByteString.Lazy.tails", "ByteString -> [ByteString]")
        , ("Data.ByteString.Lazy.take", "Int64 -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.takeWhile", "(Word8 -> Bool) -> ByteString -> ByteString")
        , ("Data.ByteString.Lazy.toChunks", "ByteString -> [ByteString]")
        , ("Data.ByteString.Lazy.toStrict", "ByteString -> ByteString")
        , ("Data.ByteString.Lazy.transpose", "[ByteString] -> [ByteString]")
        , ("Data.ByteString.Lazy.uncons", "ByteString -> Maybe (Word8, ByteString)")
        , ("Data.ByteString.Lazy.unfoldr", "(a -> Maybe (Word8, a)) -> a -> ByteString")
        , ("Data.ByteString.Lazy.unpack", "ByteString -> [Word8]")
        , ("Data.ByteString.Lazy.unsnoc", "ByteString -> Maybe (ByteString, Word8)")
        , ("Data.ByteString.Lazy.unzip", "[(Word8, Word8)] -> (ByteString, ByteString)")
        , ("Data.ByteString.Lazy.writeFile", "[Char] -> ByteString -> IO ()")
        , ("Data.ByteString.Lazy.zip", "ByteString -> ByteString -> [(Word8, Word8)]")
        , ("Data.ByteString.Lazy.zipWith", "(Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]")
        , ("Data.Either.Left", "a -> Either a b")
        , ("Data.Either.Right", "b -> Either a b")
        , ("Data.Either.either", "(a -> c) -> (b -> c) -> Either a b -> c")
        , ("Data.Either.fromLeft", "a -> Either a b -> a")
        , ("Data.Either.fromRight", "b -> Either a b -> b")
        , ("Data.Either.isLeft", "Either a b -> Bool")
        , ("Data.Either.isRight", "Either a b -> Bool")
        , ("Data.Either.lefts", "[Either a b] -> [a]")
        , ("Data.Either.partitionEithers", "[Either a b] -> ([a], [b])")
        , ("Data.Either.rights", "[Either a b] -> [b]")
        , ("Data.List.group", "Eq a => [a] -> [[a]]")
        , ("Data.Maybe.Just", "a -> Maybe a")
        , ("Data.Maybe.Nothing", "Maybe a")
        , ("Data.Maybe.catMaybes", "[Maybe a] -> [a]")
        , ("Data.Maybe.fromJust", "Maybe a -> a")
        , ("Data.Maybe.fromMaybe", "a -> Maybe a -> a")
        , ("Data.Maybe.isJust", "Maybe a -> Bool")
        , ("Data.Maybe.isNothing", "Maybe a -> Bool")
        , ("Data.Maybe.listToMaybe", "[a] -> Maybe a")
        , ("Data.Maybe.mapMaybe", "(a -> Maybe b) -> [a] -> [b]")
        , ("Data.Maybe.maybe", "b -> (a -> b) -> Maybe a -> b")
        , ("Data.Maybe.maybeToList", "Maybe a -> [a]")
        , ("Data.Tuple.curry", "((a, b) -> c) -> a -> b -> c")
        , ("Data.Tuple.fst", "(a, b) -> a")
        , ("Data.Tuple.snd", "(a, b) -> b")
        , ("Data.Tuple.swap", "(a, b) -> (b, a)")
        , ("Data.Tuple.uncurry", "(a -> b -> c) -> (a, b) -> c")
        , ("GHC.Char.chr", "Int -> Char")
        , ("GHC.Char.eqChar", "Char -> Char -> Bool")
        , ("GHC.Char.neChar", "Char -> Char -> Bool")
        , ("GHC.List.all", "(a -> Bool) -> [a] -> Bool")
        , ("GHC.List.and", "[Bool] -> Bool")
        , ("GHC.List.any", "(a -> Bool) -> [a] -> Bool")
        , ("GHC.List.break", "(a -> Bool) -> [a] -> ([a], [a])")
        , ("GHC.List.concat", "[[a]] -> [a]")
        , ("GHC.List.concatMap", "(a -> [b]) -> [a] -> [b]")
        , ("GHC.List.cycle", "[a] -> [a]")
        , ("GHC.List.drop", "Int -> [a] -> [a]")
        , ("GHC.List.dropWhile", "(a -> Bool) -> [a] -> [a]")
        , ("GHC.List.elem", "Eq a => a -> [a] -> Bool")
        , ("GHC.List.filter", "(a -> Bool) -> [a] -> [a]")
        , ("GHC.List.foldl", "(b -> a -> b) -> b -> [a] -> b")
        , ("GHC.List.foldl'", "(b -> a -> b) -> b -> [a] -> b")
        , ("GHC.List.foldl1", "(a -> a -> a) -> [a] -> a")
        , ("GHC.List.foldl1'", "(a -> a -> a) -> [a] -> a")
        , ("GHC.List.foldr", "(a -> b -> b) -> b -> [a] -> b")
        , ("GHC.List.foldr1", "(a -> a -> a) -> [a] -> a")
        , ("GHC.List.head", "[a] -> a")
        , ("GHC.List.init", "[a] -> [a]")
        , ("GHC.List.iterate", "(a -> a) -> a -> [a]")
        , ("GHC.List.iterate'", "(a -> a) -> a -> [a]")
        , ("GHC.List.last", "[a] -> a")
        , ("GHC.List.length", "[a] -> Int")
        , ("GHC.List.lookup", "Eq a => a -> [(a, b)] -> Maybe b")
        , ("GHC.List.map", "(a -> b) -> [a] -> [b]")
        , ("GHC.List.maximum", "Ord a => [a] -> a")
        , ("GHC.List.minimum", "Ord a => [a] -> a")
        , ("GHC.List.notElem", "Eq a => a -> [a] -> Bool")
        , ("GHC.List.null", "[a] -> Bool")
        , ("GHC.List.or", "[Bool] -> Bool")
        , ("GHC.List.product", "Num a => [a] -> a")
        , ("GHC.List.repeat", "a -> [a]")
        , ("GHC.List.replicate", "Int -> a -> [a]")
        , ("GHC.List.reverse", "[a] -> [a]")
        , ("GHC.List.scanl", "(b -> a -> b) -> b -> [a] -> [b]")
        , ("GHC.List.scanl'", "(b -> a -> b) -> b -> [a] -> [b]")
        , ("GHC.List.scanl1", "(a -> a -> a) -> [a] -> [a]")
        , ("GHC.List.scanr", "(a -> b -> b) -> b -> [a] -> [b]")
        , ("GHC.List.scanr1", "(a -> a -> a) -> [a] -> [a]")
        , ("GHC.List.span", "(a -> Bool) -> [a] -> ([a], [a])")
        , ("GHC.List.splitAt", "Int -> [a] -> ([a], [a])")
        , ("GHC.List.sum", "Num a => [a] -> a")
        , ("GHC.List.tail", "[a] -> [a]")
        , ("GHC.List.take", "Int -> [a] -> [a]")
        , ("GHC.List.takeWhile", "(a -> Bool) -> [a] -> [a]")
        , ("GHC.List.uncons", "[a] -> Maybe (a, [a])")
        , ("GHC.List.unzip", "[(a, b)] -> ([a], [b])")
        , ("GHC.List.unzip3", "[((a, b), c)] -> (([a], [b]), [c])")
        , ("GHC.List.zip", "[a] -> [b] -> [(a, b)]")
        , ("GHC.List.zip3", "[a] -> [b] -> [c] -> [((a, b), c)]")
        , ("GHC.List.zipWith", "(a -> b -> c) -> [a] -> [b] -> [c]")
        , ("GHC.List.zipWith3", "(a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]")
        , ("Nil", "[a]")
        , ("Pair", "a -> b -> (a, b)")
        , ("Text.Show.show", "Show a => a -> [Char]")
        , ("Text.Show.showChar", "Char -> [Char] -> [Char]")
        , ("Text.Show.showList", "Show a => [a] -> [Char] -> [Char]")
        , ("Text.Show.showListWith", "(a -> [Char] -> [Char]) -> [a] -> [Char] -> [Char]")
        , ("Text.Show.showParen", "Bool -> ([Char] -> [Char]) -> [Char] -> [Char]")
        , ("Text.Show.showString", "[Char] -> [Char] -> [Char]")
        , ("Text.Show.shows", "Show a => a -> [Char] -> [Char]")
        , ("Text.Show.showsPrec", "Show a => Int -> a -> [Char] -> [Char]")
        ]

-- | The components that Hectare adds for the Stack Overflow queries.
augmentedComponents :: [(Text, Type)]
augmentedComponents =
    components
        [ ("(Data.Function..)", "(b -> c) -> (a -> b) -> a -> c")
        , ("Data.Function.on", "(b -> b -> c) -> (a -> b) -> a -> a -> c")
        , ("Data.Function.flip", "(a -> b -> c) -> b -> a -> c")
        , ("Data.List.groupBy", "(a -> a -> Bool) -> [a] -> [[a]]")
        , ("Data.List.sortBy", "(a -> a -> Ordering) -> [a] -> [a]")
        , ("Data.List.maximumBy", "(a -> a -> Ordering) -> [a] -> a")
        , ("Data.Ord.compare", "Ord a => a -> a -> Ordering")
        ]

-- | The Hoogle+ benchmark queries.
hooglePlusBenchmarks :: [Benchmark]
hooglePlusBenchmarks =
    [ benchmark "appBoth" 5 (Just "Pair (f x) (g x)") ["f :: a -> b", "g :: a -> c", "x :: a"] "(b, c)"
    , benchmark "test" 5 (Just "Data.Bool.bool Data.Maybe.Nothing (Data.Maybe.Just x) b") ["b :: Bool", "x :: a"] "Maybe a"
    , benchmark "both" 7 (Just "Pair (f (Data.Tuple.fst p)) (f (Data.Tuple.snd p))") ["f :: a -> b", "p :: (a, a)"] "(b, b)"
    , benchmark
        "mapEither"
        4
        (Just "Data.Either.partitionEithers (GHC.List.map f xs)")
        ["f :: a -> Either b c", "xs :: [a]"]
        "([b], [c])"
    , benchmark
        "mapMaybes"
        4
        (Just "Data.Maybe.listToMaybe (Data.Maybe.mapMaybe f xs)")
        ["f :: a -> Maybe b", "xs :: [a]"]
        "Maybe b"
    , benchmark "mergeEither" 4 (Just "Data.Either.either Data.Either.Left id e") ["e :: Either a (Either a b)"] "Either a b"
    , benchmark
        "mbToEither"
        5
        (Just "Data.Maybe.maybe (Data.Either.Left x) Data.Either.Right mb")
        ["x :: a", "mb :: Maybe b"]
        "Either a b"
    , benchmark
        "cartProduct"
        6
        (Just "GHC.List.map (GHC.List.zip xs) (GHC.List.map GHC.List.repeat ys)")
        ["xs :: [a]", "ys :: [b]"]
        "[[(a, b)]]"
    , benchmark
        "multiAppPair"
        7
        (Just "Pair (Data.Tuple.fst tp x) (Data.Tuple.snd tp x)")
        ["tp :: (a -> b, a -> c)", "x :: a"]
        "(b, c)"
    , benchmark "map" 3 (Just "GHC.List.map f xs") ["f :: a -> b", "xs :: [a]"] "[b]"
    , benchmark "replFuncs" 3 (Just "GHC.List.replicate n f") ["f :: a -> b", "n :: Int"] "[a -> b]"
    , benchmark
        "mbAppFirst"
        5
        (Just "Data.Maybe.maybe x f (Data.Maybe.listToMaybe xs)")
        ["x :: b", "f :: a -> b", "xs :: [a]"]
        "b"
    , benchmark "mapTwice" 5 (Just "GHC.List.map g (GHC.List.map f xs)") ["f :: a -> b", "g :: b -> c", "xs :: [a]"] "[c]"
    , benchmark "resolveEither" 4 (Just "Data.Either.either f id e") ["e :: Either a b", "f :: a -> b"] "b"
    , benchmark
        "firstJust"
        5
        (Just "Data.Maybe.fromMaybe x (Data.Maybe.listToMaybe (Data.Maybe.catMaybes xs))")
        ["x :: a", "xs :: [Maybe a]"]
        "a"
    , benchmark "appendN" 4 (Just "GHC.List.concat (GHC.List.replicate n xs)") ["n :: Int", "xs :: [a]"] "[a]"
    , benchmark "applyNtimes" 6 (Just "GHC.List.foldr $ x (GHC.List.replicate n f)") ["f :: a -> a", "x :: a", "n :: Int"] "a"
    , benchmark
        "dedupe"
        5
        (Just "GHC.List.map GHC.List.head (Data.List.group tcarg0 xs)")
        ["tcarg0 :: @@hplusTC@@Eq a", "xs :: [a]"]
        "[a]"
    , benchmark "inverseMap" 5 (Just "GHC.List.zipWith $ fs (GHC.List.repeat x)") ["fs :: [a -> b]", "x :: a"] "[b]"
    , benchmark "app2" 4 (Just "f x (g x)") ["f :: a -> b -> c", "g :: a -> b", "x :: a"] "c"
    , benchmark "singletonList" 3 (Just "Cons x Nil") ["x :: a"] "[a]"
    , benchmark "headLast" 5 (Just "Pair (GHC.List.head xs) (GHC.List.last xs)") ["xs :: [a]"] "(a, a)"
    , benchmark "headRest" 3 (Just "Data.Maybe.fromJust (GHC.List.uncons xs)") ["xs :: [a]"] "(a, [a])"
    , benchmark "coundPredMatch" 4 (Just "GHC.List.length (GHC.List.filter p xs)") ["xs :: [a]", "p :: a -> Bool"] "Int"
    , benchmark "splitStr" 7 Nothing ["str :: [Char]", "c :: Char"] "[[Char]]"
    , benchmark
        "splitAtFirst"
        5
        (Just "GHC.List.break ((Data.Eq.==) tcarg0 x) xs")
        ["tcarg0 :: @@hplusTC@@Eq a", "x :: a", "xs :: [a]"]
        "([a], [a])"
    , benchmark "hoogle01" 3 (Just "f (GHC.List.head xs)") ["f :: a -> b", "xs :: [a]"] "b"
    , benchmark "firstMatch" 4 (Just "GHC.List.head (GHC.List.filter p xs)") ["xs :: [a]", "p :: a -> Bool"] "a"
    , benchmark "firstMaybe" 3 (Just "GHC.List.head (Data.Maybe.catMaybes mbs)") ["mbs :: [Maybe a]"] "a"
    , benchmark "rights" 3 (Just "Data.Either.Right (Data.Either.rights es)") ["es :: [Either a b]"] "Either a [b]"
    , benchmark "firstKey" 3 (Just "Data.Tuple.fst (GHC.List.head xs)") ["xs :: [(a, b)]"] "a"
    , benchmark
        "firstRight"
        4
        (Just "Data.Either.Right (GHC.List.head (Data.Either.rights es))")
        ["es :: [Either a b]"]
        "Either a b"
    , benchmark "maybe" 4 (Just "Data.Maybe.Just (Data.Maybe.fromMaybe x mb)") ["mb :: Maybe a", "x :: a"] "Maybe a"
    , benchmark "app3" 4 (Just "f x z y") ["f :: a -> b -> c -> d", "x :: a", "y :: c", "z :: b"] "d"
    , benchmark "zipWithResult" 5 (Just "GHC.List.zip xs (GHC.List.map f xs)") ["f :: a -> b", "xs :: [a]"] "[(a, b)]"
    , benchmark
        "eitherTriple"
        5
        (Just "Data.Bool.bool e2 e1 (Data.Either.isLeft e1)")
        ["e1 :: Either a b", "e2 :: Either a b"]
        "Either a b"
    , benchmark "pipe" 4 (Just "GHC.List.foldr $ x fs") ["fs :: [a -> a]", "x :: a"] "a"
    , benchmark
        "lookup"
        5
        (Just "Data.Maybe.fromJust (GHC.List.lookup tcarg0 k xs)")
        ["tcarg0 :: @@hplusTC@@Eq a", "xs :: [(a, b)]", "k :: a"]
        "b"
    , benchmark
        "mbElem"
        6
        (Just "Data.Maybe.listToMaybe (GHC.List.filter ((Data.Eq.==) tcarg0 x) xs)")
        ["tcarg0 :: @@hplusTC@@Eq a", "x :: a", "xs :: [a]"]
        "Maybe a"
    , benchmark
        "areEq"
        7
        (Just "Data.Maybe.listToMaybe (GHC.List.filter ((Data.Eq.==) tcarg0 x) (GHC.List.repeat y))")
        ["tcarg0 :: @@hplusTC@@Eq a", "x :: a", "y :: a"]
        "Maybe a"
    , benchmark "applyPair" 4 (Just "Data.Tuple.fst p (Data.Tuple.snd p)") ["p :: (a -> b, a)"] "b"
    , benchmark "flatten" 3 (Just "GHC.List.concat (GHC.List.concat xss)") ["xss :: [[[a]]]"] "[a]"
    , benchmark
        "takeNdropM"
        7
        (Just "Pair (GHC.List.take n xs) (GHC.List.drop m xs)")
        ["n :: Int", "m :: Int", "xs :: [a]"]
        "([a], [a])"
    , benchmark
        "indexesOf"
        6
        (Just "GHC.List.map Data.Tuple.snd (f (GHC.List.zip xs ys))")
        ["f :: [(a, Int)] -> [(a, Int)]", "xs :: [a]", "ys :: [Int]"]
        "[Int]"
    , benchmark
        "containsEdge"
        9
        (Just "(Data.Bool.&&) (GHC.List.elem (Data.Tuple.fst edge) vs) (GHC.List.elem (Data.Tuple.snd edge) vs)")
        ["vs :: [Int]", "edge :: (Int, Int)"]
        "Bool"
    ]

-- | The Stack Overflow benchmark queries, which need 'hooglePlusWithAugmented'.
stackOverflowBenchmarks :: [Benchmark]
stackOverflowBenchmarks =
    [ benchmark "extractEitherValues" 5 (Just "GHC.List.map (Data.Either.either id id) es") ["es :: [Either b b]"] "[b]"
    , benchmark
        "filterMultiple"
        6
        (Just "GHC.List.filter (Data.Function.flip (GHC.List.elem tcarg0) xs) ys")
        ["tcarg0 :: @@hplusTC@@Eq a", "xs :: [a]", "ys :: [a]"]
        "[a]"
    , benchmark
        "filterNot"
        5
        (Just "GHC.List.filter ((Data.Function..) Data.Bool.not p) xs")
        ["p :: a -> Bool", "xs :: [a]"]
        "[a]"
    , benchmark
        "isSortedBy"
        6
        (Just "GHC.List.and (GHC.List.zipWith cmp xs (GHC.List.tail xs))")
        ["cmp :: a -> a -> Bool", "xs :: [a]"]
        "Bool"
    , benchmark "multipleNth" 4 (Just "GHC.List.map ((GHC.List.!!) xs) indices") ["xs :: [a]", "indices :: [Int]"] "[a]"
    , benchmark "doubleMap" 4 (Just "GHC.List.map (GHC.List.map f) xss") ["f :: a -> b", "xss :: [[a]]"] "[[b]]"
    , benchmark
        "lengthOfSnds"
        5
        (Just "GHC.List.length (GHC.List.concat (GHC.List.map Data.Tuple.snd ps))")
        ["ps :: [(a, [b])]"]
        "Int"
    , benchmark
        "lessThanNTimes"
        8
        (Just "GHC.List.null (GHC.List.drop n (GHC.List.filter ((Data.Eq.==) tcarg0 x) xs))")
        ["tcarg0 :: @@hplusTC@@Eq a", "n :: Int", "x :: a", "xs :: [a]"]
        "Bool"
    , benchmark
        "groupByFirst"
        6
        (Just "Data.List.groupBy (Data.Function.on ((Data.Eq.==) tcarg0) Data.Tuple.fst) xs")
        ["tcarg0 :: @@hplusTC@@Eq a", "xs :: [(a, b)]"]
        "[[(a, b)]]"
    , benchmark
        "mySortBy"
        5
        (Just "Data.List.sortBy (Data.Function.on cmp Data.Tuple.fst) xs")
        ["cmp :: a -> a -> Ordering", "xs :: [(a, b)]"]
        "[(a, b)]"
    , benchmark "transpose" 6 (Just "GHC.List.foldr (GHC.List.zipWith Cons) (GHC.List.repeat Nil) xs") ["xs :: [[a]]"] "[[a]]"
    , benchmark
        "partition"
        9
        (Just "Pair (GHC.List.filter p xs) (GHC.List.filter ((Data.Function..) Data.Bool.not p) xs)")
        ["p :: a -> Bool", "xs :: [a]"]
        "([a], [a])"
    , benchmark
        "matchedKeys"
        7
        (Just "GHC.List.map Data.Tuple.fst (GHC.List.filter ((Data.Function..) p Data.Tuple.snd) xs)")
        ["p :: b -> Bool", "xs :: [(a, b)]"]
        "[a]"
    , benchmark
        "filterPairs"
        6
        (Just "GHC.List.filter (Data.Tuple.uncurry f) (GHC.List.zip xs ys)")
        ["f :: a -> b -> Bool", "xs :: [a]", "ys :: [b]"]
        "[(a, b)]"
    , benchmark
        "applyNthNTimes"
        7
        (Just "GHC.List.zipWith $ (GHC.List.iterate ((Data.Function..) f) f) xs")
        ["f :: a -> a", "xs :: [a]"]
        "[a]"
    , benchmark
        "removeMax"
        7
        (Just "GHC.List.filter ((Data.Eq./=)_Ord tcarg0 (GHC.List.maximum tcarg0 xs)) xs")
        ["tcarg0 :: @@hplusTC@@Ord a", "xs :: [a]"]
        "[a]"
    , benchmark
        "allSameBy"
        7
        (Just "GHC.List.all (Data.Function.on ((Data.Eq.==) tcarg0) cmp xs) xss")
        ["tcarg0 :: @@hplusTC@@Eq b", "cmp :: a -> b", "xs :: a", "xss :: [a]"]
        "Bool"
    , benchmark
        "mostFrequent"
        7
        (Just "Data.List.maximumBy (Data.Function.on (Data.Ord.compare tcarg0) Data.Tuple.snd) (occur xs)")
        ["tcarg0 :: @@hplusTC@@Ord b", "xs :: [a]", "occur :: [a] -> [(a, b)]"]
        "(a, b)"
    , benchmark
        "splitOn"
        7
        (Just "Data.List.groupBy (Data.Function.on (Data.Bool.&&) ((Data.Eq./=) tcarg0 x)) xs")
        ["tcarg0 :: @@hplusTC@@Eq a", "x :: a", "xs :: [a]"]
        "[[a]]"
    ]
