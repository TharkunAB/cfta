{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{- | A language tower in one loop.

1. The base language L0: sums of digits. Each digit is a leaf with an exact value.
2. The model, a black box: it accepts a sum when the sum is even and every digit is at most 4.
3. The outer loop: it tests a few concretizations of each abstract term up to a growing size
   bound, and finds the predicates that the model depends on, and a spec as a table.
4. Every concrete test up to the bound checks the spec; the loop asked only some of them.
5. The abstraction step from L0 to L1 is a language update, stored as text.
6. A short spec in L1, written with the automaton quote, agrees with every test.
7. A definitional step from L1 to L2 adds double(x), which lowers to add(x, x).
8. The spec lifts to L2: cfta counts and ranks the accepted tests of L2 of every size.
9. A second definitional step composes with the first: one lowering from L3 to L1.
-}
module Main (main) where

import Control.Monad (forM_, when)
import Data.Functor.Identity (Identity (..))
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Document as Document
import Data.CFTA.Formula (renderFormula)
import Data.CFTA.Gen.Tower (Exploration (..), Outcome (..))
import qualified Data.CFTA.Gen.Tower as Tower
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Size)
import Data.CFTA.Language (Language)
import qualified Data.CFTA.Language as Language
import Data.CFTA.Lowering (Expansion (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Refinement.Expression (Formula, modulo, refinementFormula, (.==), (.>))
import qualified Data.CFTA.Serialization.Text as Serialization
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol (RefinedSymbol), symbolText, valueName)
import Data.CFTA.TH (automaton)
import Data.CFTA.Term (Term (Node))

-- | The one state of the languages.
data State = Expr
    deriving (Eq, Ord, Show, Read)

-- | The value of a 'Right', or stop with the explained error.
must :: (failure -> String) -> Either failure value -> value
must explain = either (error . explain) id

-- | A digit leaf with an exact value.
digit :: Integer -> Symbol
digit value = RefinedSymbol "lit" $ refinementFormula (.== fromInteger value)

-- | L0: a production for each digit, and add.
base :: Language State
base =
    Language.fromDocument
        $ must Document.explainDocumentError
        $ Document.mkDocument
            Expr
            [
                ( Expr
                , [FTA.Transition (digit value) [] $ Document.Annotation (name value) Map.empty | value <- [0 .. 9]]
                    <> [FTA.Transition "add" [Expr, Expr] $ Document.Annotation "add" Map.empty]
                )
            ]
  where
    name value = Text.pack $ 'd' : show value

-- | The model: a sum is accepted when it is even and every digit is at most 4.
model :: Term Symbol -> Bool
model term = even (sum values) && all (<= 4) values
  where
    values = mapMaybe (`lookup` [(digit value, value) | value <- [0 .. 9 :: Integer]]) (leaves term)
    leaves (Node symbol []) = [symbol]
    leaves (Node _ children) = concatMap leaves children

-- | The size bound of the loop.
bound :: Size
bound = 7

-- | Every concrete test of L0 up to the bound, in rank order.
concreteTests :: [Term Symbol]
concreteTests = concatMap (Sized.termsOfSize $ must show $ Sized.sized $ Language.compileGraph base) [1 .. bound]

-- | The qualifier templates: @v > k@ and @v mod k == 0@.
templates :: [Integer -> Formula]
templates =
    [ \threshold -> refinementFormula (.> fromInteger threshold)
    , \divisor -> refinementFormula $ \v -> modulo v (fromInteger divisor) .== 0
    ]

-- | The outer loop: two concretizations of each abstract term, a spec that rejects by default.
exploration :: Exploration Bool
exploration = runIdentity $ Tower.explore templates False bound 2 (Language.compileGraph base) (Identity . model)

-- | The abstraction of a digit in the vocabulary that the loop found.
cubeOf :: Integer -> Symbol
cubeOf value = case Tower.abstract (exploredVocabulary exploration) (Node (digit value) []) of
    Just (Node symbol []) -> symbol
    _ -> error "a digit has no abstraction"

-- | The cubes of the small digits, for the spec below.
smallEven, smallOdd :: Symbol
smallEven = cubeOf 0
smallOdd = cubeOf 1

-- The quote below looks these names up, so they come before it.
$(pure [])

-- | A short spec in L1: only small digits, and an even sum.
spec :: FTA.PlainFTA String Symbol
spec =
    must
        show
        [automaton|
            start Even;
            state Even { $smallEven; add(Even, Even); add(Odd, Odd); }
            state Odd { $smallOdd; add(Even, Odd); add(Odd, Even); }
        |]

main :: IO ()
main = do
    heading "1. L0, the base language"
    TextIO.putStr $ Serialization.printLanguage base

    heading "2 and 3. The model and the outer loop"
    forM_ (exploredChanges exploration) $ \(size, vocabulary) ->
        putStrLn $ "at size bound " <> show size <> ", the vocabulary is: " <> intercalate ", " (map formula vocabulary)
    check "the loop ends in agreement" $ exploredOutcome exploration == Agreed
    putStrLn $
        "model calls: "
            <> show (exploredCalls exploration)
            <> ", for "
            <> show (length concreteTests)
            <> " concrete tests up to size "
            <> show bound

    heading "4. Every concrete test up to the bound checks the spec"
    let predicted test =
            maybe False (\term -> Map.findWithDefault False term $ exploredSpec exploration) $
                Tower.abstract (exploredVocabulary exploration) test
    check "the spec of the loop agrees with the model on every concrete test" $
        all (\test -> predicted test == model test) concreteTests
    putStrLn $
        "description length: "
            <> show (Tower.descriptionLength (exploredVocabulary exploration) (exploredSpec exploration))
            <> " nodes, against "
            <> show (Tower.descriptionLength [] concreteTable)
            <> " for the table of the accepted concrete tests"

    heading "5. The abstraction step from L0 to L1, as text"
    let abstraction =
            foldMap
                (\value -> Language.remove $ Language.at Expr $ Language.ProductionName $ Text.pack $ 'd' : show value)
                [0 .. 9 :: Int]
                <> foldMap
                    (\(cube, name) -> Language.define (Language.at Expr $ Language.ProductionName name) cube [])
                    (Map.toList cubeNames)
        stored = Serialization.printUpdate abstraction
    TextIO.putStr stored
    reopened <- either (fail . Serialization.explainTextError) pure $ Serialization.parseUpdate stored
    abstracted <- either (fail . Language.explainUpdateError) pure $ Language.update base abstraction
    check "the stored update gives the same L1" $ Language.update base reopened == Right abstracted
    TextIO.putStr $ Serialization.printLanguage abstracted

    heading "6. A short spec in L1, from the automaton quote"
    let agrees test = maybe False (FTA.accepts spec) (Tower.abstract (exploredVocabulary exploration) test) == model test
    check "the spec agrees with the model on every concrete test" $ all agrees concreteTests

    heading "7. The definitional step from L1 to L2: double(x) lowers to add(x, x)"
    let lowering = must show $ Lowering.mkLowering [("double", 1, Apply "add" [Child 0, Child 0])]
        definition = Language.define (Language.at Expr "double") "double" [Expr]
    TextIO.putStr $ Serialization.printUpdate definition
    extended <- either (fail . Language.explainUpdateError) pure $ Language.update abstracted definition
    TextIO.putStr $ Serialization.printLanguage extended
    let earlier = Language.compileGraph abstracted
        later = Language.compileGraph extended
    check "every term of L2 lowers to a term of L1" $ null $ Lowering.checkLowering lowering earlier later

    heading "8. The spec, lifted to L2"
    let lifted = must show $ Lowering.lift lowering spec
        accepted = must show $ Sized.sized $ either (error . show) FTA.dropConstraints $ FTA.intersect later lifted
        whole = must show $ Sized.sized later
    putStrLn "size: accepted tests of L2"
    forM_ [1 .. 9] $ \size -> do
        let Cardinality count = Sized.countOfSize accepted size
        putStrLn $ show size <> ": " <> show count
        when (size <= 5)
            $ check ("the count of size " <> show size <> " is the count of the tests of L2 whose lowering the spec accepts")
            $ count
                == toInteger
                    (length [term | term <- Sized.termsOfSize whole size, maybe False (FTA.accepts spec) (Lowering.lower lowering term)])
    let rank = ClassRank 3
    case Sized.unrankOfSize accepted 5 rank of
        Nothing -> fail "no term of rank 3"
        Just term -> do
            putStrLn $ "the accepted test of size 5 and rank 3: " <> render term
            putStrLn $ "its lowering in L1: " <> maybe "none" render (Lowering.lower lowering term)
            check "rank and unrank are inverse" $ Sized.rankOfSize accepted term == Just (5, rank)

    heading "9. quad(x) lowers to double(double(x)); the composite lowers L3 to L1 at once"
    let quad = must show $ Lowering.mkLowering [("quad", 1, Apply "double" [Apply "double" [Child 0]])]
        composite = must show $ Lowering.compose quad lowering
        example = Node "quad" [Node smallOdd []]
    putStrLn $ render example <> " lowers to " <> maybe "none" render (Lowering.lower composite example)
    check "the composite is the two lowerings" $
        Lowering.lower composite example == (Lowering.lower quad example >>= Lowering.lower lowering)
  where
    concreteTable = Map.fromList [(test, True) | test <- concreteTests, model test]

-- | The production names of L1: each cube is named by the digits that it holds.
cubeNames :: Map.Map Symbol Text.Text
cubeNames =
    Map.fromListWith
        (\later earlier -> earlier <> "-" <> Text.drop 3 later)
        [(cubeOf value, Text.pack $ "of-" <> show value) | value <- [0 .. 9]]

-- | A term in the syntax of the text format, with each cube by its production name.
render :: Term Symbol -> String
render (Node symbol children) =
    maybe (Text.unpack $ symbolText symbol) Text.unpack (Map.lookup symbol cubeNames)
        <> if null children then "" else "(" <> intercalate ", " (map render children) <> ")"

-- | A predicate, with @v@ for the value of a leaf as in the text format.
formula :: Formula -> String
formula = Text.unpack . Text.replace (Text.pack valueName) "v" . Text.pack . renderFormula

-- | Print a section heading.
heading :: String -> IO ()
heading title = putStrLn $ "\n== " <> title

-- | Stop the program when a check fails.
check :: String -> Bool -> IO ()
check label holds = if holds then putStrLn $ "ok: " <> label else fail $ "failed: " <> label
