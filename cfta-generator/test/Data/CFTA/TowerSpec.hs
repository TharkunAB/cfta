{-# LANGUAGE OverloadedStrings #-}

-- | A tower of an expression language: two definitional extensions and one abstraction extension.
module Data.CFTA.TowerSpec (spec) where

import Control.Exception (throwIO)
import Control.Monad (forM_, void)
import qualified Data.Map.Strict as Map
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Extension (ExtensionError (..))
import Data.CFTA.Formula (Formula)
import qualified Data.CFTA.Formula as F
import Data.CFTA.Index (Size (..))
import Data.CFTA.Language (Language (..))
import qualified Data.CFTA.Language as L
import qualified Data.CFTA.Language.Source as D
import Data.CFTA.Lowering (Expansion (..))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Refinement.Expression (Expr, refinementFormula, (.&&), (.<=), (.>), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..), withZ3)
import Data.CFTA.Refinement.Verdict (Entailment (Entailment), Verdict (..))
import Data.CFTA.Sized (sized, termsOfSize)
import Data.CFTA.Symbol (Symbol (RefinedSymbol))
import Data.CFTA.Template (Exclusion (..), Template (..))
import Data.CFTA.Term (Term (Node))
import Data.CFTA.Tower

spec :: Spec
spec = describe "Data.CFTA.Tower" $ do
    it "keeps the meaning of every old term through the tower, at each level" $ withZ3 [] $ \z3 -> do
        full <- build z3
        version full `shouldBe` 3
        let reports = keptMeaning full
        map reportLevel reports `shouldBe` [1, 2, 3]
        forM_ reports $ \report -> do
            (reportChecked report > 5) `shouldBe` True
            reportChanges report `shouldBe` []
        -- A term of version j has the same meaning in each later version.
        forM_ [0 .. 3] $ \j -> do
            below <- maybe (fail "no version") pure $ languageAt full j
            forM_ (take 200 $ termsOf below) $ \term ->
                forM_ [j .. 3] $ \k -> meaning full k term `shouldBe` meaning full j term
    it "gives the meaning in L0 of terms of the new constructors, also through the composed lowering" $ withZ3 [] $ \z3 -> do
        full <- build z3
        -- The variants of the digits relax to the digits of the base language.
        meaning full 3 (Node "sub" [Node notHigh [], Node high' []])
            `shouldBe` Just (Node "add" [Node digitAll [], Node "neg" [Node digitAll []]])
        -- Version 2 has a constructor that uses a constructor of version 1.
        meaning full 2 (Node "swap" [Node digitAll [], Node "double" [Node digitAll []]])
            `shouldBe` Just (Node "add" [Node "add" [Node digitAll [], Node digitAll []], Node "neg" [Node digitAll []]])
        composed <- either (fail . show) pure $ composedLowering full 3
        let term = Node "swap" [Node "double" [Node digitAll []], Node "sub" [Node digitAll [], Node digitAll []]]
        Lowering.lower composed term `shouldBe` meaning full 2 term
        (term `seq` Lowering.newConstructors composed) `shouldBe` ["double", "sub", "swap"]
    it "refuses a bad second extension with the term that changes meaning and its level" $ withZ3 [] $ \z3 -> do
        first <- expand z3 0 subtraction (tower (Size 4) base) >>= either (fail . show) pure
        -- The new production neg(e) lowers neg to a sum. Old terms with neg change meaning.
        result <- expand z3 1 badNegation first
        case result of
            Left (NotDefinitional 2 faults (Just change)) -> do
                faults `shouldSatisfy` any isLoweredOld
                change
                    `shouldBe` MeaningChange
                        2
                        (Node "neg" [Node digitAll []])
                        (Just (Node "neg" [Node digitAll []]))
                        (Just (Node "add" [Node digitAll [], Node digitAll []]))
            other -> fail $ "not refused as expected: " <> show (void other)
        -- The tower is the same, so the caller can go on from version 1.
        version first `shouldBe` 1
    it "refuses an expansion when the caller expects another version" $ withZ3 [] $ \z3 -> do
        let start = tower (Size 4) base
        expand z3 1 subtraction start `refuses` StaleVersion 1 0
        previewExpand z3 3 subtraction start `refuses` StaleVersion 3 0
        later <- expand z3 0 subtraction start >>= either (fail . show) pure
        expand z3 0 doubling later `refuses` StaleVersion 0 1
    it "gives a preview that equals the result of the expansion, and changes nothing" $ withZ3 [] $ \z3 -> do
        let start = tower (Size 4) base
        preview <- previewExpand z3 0 subtraction start >>= either (fail . show) pure
        -- The preview names what the extension adds, and the update replays on the old language.
        previewVersion preview `shouldBe` 1
        previewConstructors preview `shouldBe` ["sub"]
        L.update base (previewUpdate preview) `shouldBe` Right (levelLanguage $ previewLevel preview)
        version start `shouldBe` 0
        expanded <- expand z3 0 subtraction start >>= either (fail . show) pure
        current expanded `shouldBe` levelLanguage (previewLevel preview)
        commit start preview `shouldBe` Right expanded
        -- A split names the variants of the production.
        splitPreview <- previewExpand z3 0 (Abstraction [highSplit]) start >>= either (fail . show) pure
        previewVariants splitPreview `shouldBe` [("e", "digit", ["digit.hi", "digit.not-hi"])]
        L.update base (previewUpdate splitPreview) `shouldBe` Right (levelLanguage $ previewLevel splitPreview)
    it "keeps the facts, the exclusions, and the names through the tower" $ withZ3 [] $ \z3 -> do
        full <- build z3
        let facts language = Map.fromList [(D.annotationName annotation, D.annotationFacts annotation) | annotation <- annotations language]
        -- The base facts stay at their productions, and the variants have the facts of the split production.
        facts (current full) Map.!? "add" `shouldBe` Just (Map.fromList [("note", noConstraint)])
        facts (current full) Map.!? "digit.hi" `shouldBe` Just (Map.fromList [("range", noConstraint)])
        facts (current full) Map.!? "digit.not-hi" `shouldBe` Just (Map.fromList [("range", noConstraint)])
        facts (current full) Map.!? "sub" `shouldBe` Just Map.empty
        facts (current full) Map.!? "digit" `shouldBe` Nothing
        forM_ [0 .. 3] $ \k -> fmap L.exclusions (languageAt full k) `shouldBe` Just (L.exclusions base)
    it "refuses a preview from a different parent at the same version" $ withZ3 [] $ \z3 -> do
        let start = tower (Size 4) base
            otherSub = Definitional [Definition "e" "sub" "sub" ["e", "e"] (Apply "add" [Child 0, Child 1])]
        first <- previewExpand z3 0 subtraction start >>= either (fail . show) pure
        commit (tower (Size 4) twoDigits) first `shouldBe` Left PreviewParentMismatch
        commit (tower (Size 5) base) first `shouldBe` Left PreviewParentMismatch
        a <- either (fail . show) pure $ commit start first
        commit a first `shouldBe` Left (StaleVersion 0 1)
        b <- expand z3 0 otherSub start >>= either (fail . show) pure
        current a `shouldBe` current b
        version a `shouldBe` version b
        next <- previewExpand z3 1 doubling a >>= either (fail . show) pure
        commit b next `shouldBe` Left PreviewParentMismatch
    it "refuses a split that leaves a value out, and names the production" $ withZ3 [] $ \z3 -> do
        let start = tower (Size 4) base
            hole = Split "e" "digit" [("digit.hi", refinementFormula (\v -> v .>= 0 .&& v .<= 9 .&& v .> 5))]
        result <- expand z3 0 (Abstraction [hole]) start
        case result of
            Left (NotAbstraction 1 faults _) -> faults `shouldSatisfy` (not . null)
            other -> fail $ "not refused as expected: " <> show (void other)
    it "refuses two splits that give one variant symbol from two parents, and names the symbol and the parents" $ withZ3 [] $ \z3 -> do
        let start = tower (Size 4) twoDigits
            shared = refinementFormula (\v -> v .>= 2 .&& v .<= 4)
        previewExpand
            z3
            0
            (Abstraction [Split "e" "digit" [("digit.mid", shared)], Split "e" "small" [("small.mid", shared)]])
            start
            `refuses` AmbiguousVariant (RefinedSymbol "lit" shared) digitAll (RefinedSymbol "lit" smallFormula)
    it "checks the variants against their named parent even when its sibling covers them" $ withZ3 [] $ \z3 -> do
        let start = tower (Size 4) twoDigits
            six = refinementFormula (\v -> v .>= 6 .&& v .<= 6)
            split = Split "e" "small" [("small.keep", smallFormula), ("small.six", six)]
        previewExpand z3 0 (Abstraction [split]) start
            `refuses` UnsoundSplitVariant "e" "small" "small.six" No
    it "requires the named variants to cover their parent even when its sibling does" $ withZ3 [] $ \z3 -> do
        let zero = refinementFormula (\v -> v .>= 0 .&& v .<= 0)
            split = Split "e" "small" [("small.zero", zero)]
        previewExpand z3 0 (Abstraction [split]) (tower (Size 4) twoDigits)
            `refuses` UncoveredSplit "e" "small" No
    it "refuses an undecided or timed-out named coverage check" $ do
        let zero = refinementFormula (\v -> v .>= 0 .&& v .<= 0)
            split = Split "e" "small" [("small.zero", zero)]
            solver uncertain = Entailment $ \p q ->
                if p == smallFormula && q == F.disjunction [zero] then uncertain else pure Yes
        forM_ [pure Unknown, throwIO (TimeLimitReached 1)] $ \uncertain ->
            previewExpand (solver uncertain) 0 (Abstraction [split]) (tower (Size 4) twoDigits)
                `refuses` UncoveredSplit "e" "small" Unknown
    it "refuses a split of a production that the language does not have" $ withZ3 [] $ \z3 ->
        previewExpand z3 0 (Abstraction [Split "e" "missing" []]) (tower (Size 4) base)
            `refuses` MissingProduction "e" "missing"
  where
    isLoweredOld fault = case fault of
        LoweredOldConstructor symbol -> symbol == "neg"
        _ -> False
    refuses action expected = action >>= \result -> void result `shouldBe` Left expected

-- | The digits of the base language, as values from zero to nine.
range :: Expr -> Formula
range v = v .>= 0 .&& v .<= 9

-- | The symbol of the digits of the base language.
digitAll :: Symbol
digitAll = RefinedSymbol "lit" $ refinementFormula range

-- | The source of a language, with the annotations of its productions.
annotations :: Language String -> [D.Annotation]
annotations language = map FTA.transitionConstraint $ concat $ Map.elems $ FTA.transitionTable $ D.sourceGraph $ L.source language

-- | The terms of a language, by size.
termsOf :: Language String -> [Term Symbol]
termsOf language = case sized (D.compileGraph $ L.source language) of
    Right classes -> concat [termsOfSize classes (Size size) | size <- [1 .. 4]]
    Left _ -> []

-- | A language with two leaf productions with the same symbol text and other refinements.
twoDigits :: Language String
twoDigits =
    Language
        ( either (error . show) id $
            D.mkDocument
                "e"
                [
                    ( "e"
                    ,
                        [ production "digit" digitAll [] []
                        , production "small" (RefinedSymbol "lit" smallFormula) [] []
                        , production "add" "add" ["e", "e"] []
                        ]
                    )
                ]
        )
        Map.empty

-- | The digits from zero to five.
smallFormula :: Formula
smallFormula = refinementFormula (\v -> v .>= 0 .&& v .<= 5)

-- | The base language: digits, sums, and negations, with a fact on the sum and on the digits and an exclusion.
base :: Language String
base =
    Language
        ( either (error . show) id $
            D.mkDocument
                "e"
                [
                    ( "e"
                    ,
                        [ production "digit" digitAll [] [("range", noConstraint)]
                        , production "add" "add" ["e", "e"] [("note", noConstraint)]
                        , production "neg" "neg" ["e"] []
                        ]
                    )
                ]
        )
        (Map.singleton "never" $ AtRoot $ TemplateNode "unused" [])

production :: D.ProductionName -> Symbol -> [String] -> [(D.FactName, Constraint)] -> D.Production String
production name symbol children facts = FTA.Transition symbol children $ D.Annotation name $ Map.fromList facts

-- | The first extension: subtraction is a sum with a negation.
subtraction :: Extension String
subtraction = Definitional [Definition "e" "sub" "sub" ["e", "e"] (Apply "add" [Child 0, Apply "neg" [Child 1]])]

-- | The second extension: doubling, and a swapped subtraction that uses the constructor of the first extension.
doubling :: Extension String
doubling =
    Definitional
        [ Definition "e" "double" "double" ["e"] (Apply "add" [Child 0, Child 0])
        , Definition "e" "swap" "swap" ["e", "e"] (Apply "sub" [Child 1, Child 0])
        ]

-- | A bad extension: the old constructor neg lowers to a sum.
badNegation :: Extension String
badNegation = Definitional [Definition "e" "neg2" "neg" ["e"] (Apply "add" [Child 0, Child 0])]

-- | The refinement of the digits and the new predicate.
rangeFormula, bigFormula :: Formula
rangeFormula = refinementFormula range
bigFormula = refinementFormula (.> 4)

-- | The third extension: the digits split by a new predicate, into the digits above four and the others.
highSplit :: Split String
highSplit = predicateSplit "hi" "e" "digit" rangeFormula bigFormula

-- | The symbols of the two variants.
high', notHigh :: Symbol
high' = RefinedSymbol "lit" (F.conjunction [rangeFormula, bigFormula])
notHigh = RefinedSymbol "lit" (F.conjunction [rangeFormula, F.Not bigFormula])

-- | The tower of the three extensions.
build :: Entailment -> IO (Tower String)
build z3 = do
    one <- expand z3 0 subtraction (tower (Size 4) base) >>= either (fail . show) pure
    two <- expand z3 1 doubling one >>= either (fail . show) pure
    expand z3 2 (Abstraction [highSplit]) two >>= either (fail . show) pure
