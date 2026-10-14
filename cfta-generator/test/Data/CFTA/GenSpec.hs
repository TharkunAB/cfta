{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeApplications #-}

module Data.CFTA.GenSpec (spec) where

import Control.Exception (evaluate)
import Data.Either (fromRight)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (nub)
import Data.Maybe (isNothing)
import Data.Proxy (Proxy (Proxy))
import qualified Data.Set as Set
import Data.String (fromString)
import Data.Typeable (typeRep)
import GHC.Generics (Generic)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldReturn, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import Control.Monad (void)
import qualified Data.CFTA as Automaton
import Data.CFTA.Constraint (noConstraint)
import qualified Data.CFTA.Enumeration as Enumeration
import Data.CFTA.Gen (On ((:==:)))
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import qualified Data.CFTA.Gen.QuickCheck as FTAGen
import Data.CFTA.Gen.TestSupport (ranksBack, ranksEveryMemberBack)
import qualified Data.CFTA.Gen.UntypedExpressionLanguage as Expressions
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Index (Cardinality (..), everyRank)
import qualified Data.CFTA.Interned as Common
import qualified Data.CFTA.Ranked as Ranked
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A derived recursive fixture with named child positions.
data DerivedTree = Leaf Bool | Fork DerivedTree DerivedTree
    deriving (Eq, Ord, Show, Generic)

instance Datatype.HasFTA DerivedTree

-- | A call with a list of arguments, for a recursion nested in another one.
data Call = NoCall | Call [Call]
    deriving (Eq, Show)

-- | A record fixture: it keeps its selector names without partial record fields.
data RecordPair = RecordPair {leftChild :: DerivedTree, rightChild :: DerivedTree}
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA RecordPair

-- | The first type in a mutually recursive fixture.
data MutualA = AEnd | AStep MutualB
    deriving (Eq, Show, Generic)

-- | The second type in a mutually recursive fixture.
data MutualB = BEnd | BStep MutualA
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA MutualA
instance Datatype.HasFTA MutualB

-- | An empty datatype has one state with no transitions.
data EmptyDatatype deriving (Generic)

instance Datatype.HasFTA EmptyDatatype

-- | Non-regular recursion would require an unbounded set of type states.
data Growing a = GrowEnd | Grow (Growing [a])
    deriving (Generic)

instance (Datatype.HasFTA a) => Datatype.HasFTA (Growing a)

atoms :: FTAGen.FTAGen String Int
atoms = FTAGen.oneof [FTAGen.leaf 0 "zero", FTAGen.leaf 1 "one"]

pairs :: FTAGen.FTAGen String (Int, Int)
pairs = FTAGen.node "pair" $ FTAGen.do
    left <- atoms
    right <- atoms
    FTAGen.pure (left, right)

spec :: Spec
spec = do
    describe "datatype-derived FTA generation" $ do
        it "derives one recursive grammar and preserves typed replay and shrinking" $
            case Datatype.deriveFTA @DerivedTree of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    let expected = [Leaf False, Leaf True] <> [Fork (Leaf left) (Leaf right) | left <- [False, True], right <- [False, True]]
                        check generator = do
                            FTAGen.cardinality generator `shouldBe` Right 6
                            traverse (FTAGen.unrank generator) [0 .. 5] `shouldBe` Right expected
                            traverse (FTAGen.termAt generator) [0 .. 5]
                                `shouldBe` Right (map (fmap constructorSymbol . Datatype.encodeTerm) expected)
                            map (Datatype.decodeTerm . Datatype.encodeTerm) expected
                                `shouldBe` map Just expected
                            FTAGen.shrinkRank generator 5 `shouldSatisfy` (not . null)
                            map (FTAGen.unrank generator) (FTAGen.shrinkRank generator 5)
                                `shouldSatisfy` all (`elem` map Right (take 5 expected))
                    length (Automaton.states $ Datatype.datatypeFTA datatype) `shouldBe` 2
                    check $ FTAGen.fromDatatypeUpToDepth 2 datatype
                    check $ FTAGen.upToSize 5 $ FTAGen.fromDatatype datatype
                    ranksEveryMemberBack FTAGen.rankOfValue $ FTAGen.fromDatatypeUpToDepth 2 datatype
                    ranksBack FTAGen.rankOfValue (FTAGen.fromDatatype datatype) [0 .. 30]

        it "gives a built and an imported generator of one datatype the same sizes" $
            -- Every constructor pays one, so both count the nodes of a term.
            case Datatype.deriveFTA @DerivedTree of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    let built :: FTAGen.Gen String DerivedTree
                        built =
                            FTAGen.recur $ \tree ->
                                FTAGen.oneof
                                    [ FTAGen.node "Leaf" $ Leaf <$> FTAGen.oneof [FTAGen.leaf False "False", FTAGen.leaf True "True"]
                                    , FTAGen.node "Fork" $ Fork <$> tree <*> tree
                                    ]
                        imported = FTAGen.fromDatatype datatype
                    map (FTAGen.countAtSize built) [0 .. 9] `shouldBe` map (FTAGen.countAtSize imported) [0 .. 9]
                    map (FTAGen.pmfAtSize built) [0 .. 7] `shouldBe` map (FTAGen.pmfAtSize imported) [0 .. 7]

        it "retains record names, positions, and fully applied field types" $ do
            let Term.Node constructor _ = Datatype.encodeTerm $ RecordPair (Leaf False) (Leaf True)
                typ = typeRep $ Proxy @DerivedTree
            Datatype.constructorName constructor `shouldBe` "RecordPair"
            Datatype.fieldNamed "rightChild" constructor
                `shouldBe` Just (Datatype.Field 1 (Just "rightChild") typ)
            (Datatype.decodeTerm (Term.Node constructor []) :: Maybe DerivedTree) `shouldBe` Nothing
            (Datatype.decodeTerm (Datatype.encodeTerm True) :: Maybe DerivedTree) `shouldBe` Nothing

        it "reuses mutually recursive type states and accepts finite nested lists" $ do
            case Datatype.deriveFTA @MutualA of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    let generator = FTAGen.fromDatatypeUpToDepth 3 datatype
                    traverse (FTAGen.unrank generator) [0 .. 3]
                        `shouldBe` Right [AEnd, AStep BEnd, AStep (BStep AEnd), AStep (BStep (AStep BEnd))]
                    ranksEveryMemberBack FTAGen.rankOfValue generator
                    ranksBack FTAGen.rankOfValue (FTAGen.fromDatatype datatype) [0 .. 5]
            case Datatype.deriveFTA @[[Bool]] of
                Left err -> expectationFailure $ show err
                Right datatype ->
                    Automaton.accepts (Datatype.datatypeFTA datatype) (Datatype.encodeTerm [[True], [], [False]]) `shouldBe` True

        it "requires explicit atomic domains and retains their order without duplicates" $ do
            void (Datatype.deriveFTA @(Maybe Int))
                `shouldBe` Left (Datatype.MissingDomain $ typeRep $ Proxy @Int)
            case Datatype.deriveFTAWith @(Maybe Int) $ Datatype.domain @Int [2, 1, 2] of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    traverse (FTAGen.unrank $ FTAGen.fromDatatypeUpToDepth 1 datatype) [0 .. 2]
                        `shouldBe` Right [Nothing, Just 2, Just 1]
                    ranksEveryMemberBack FTAGen.rankOfValue $ FTAGen.fromDatatypeUpToDepth 1 datatype
            void (Datatype.deriveFTAWith @Bool $ Datatype.domain [False])
                `shouldBe` Left (Datatype.NonAtomicDomain $ typeRep $ Proxy @Bool)

        it "represents empty datatypes and rejects growing recursive type arguments" $ do
            case Datatype.deriveFTA @EmptyDatatype of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    FTAGen.cardinality (FTAGen.fromDatatypeUpToDepth 3 datatype)
                        `shouldBe` Left FTAGen.EmptyGenerator
                    FTAGen.rankOfTerm (FTAGen.fromDatatypeUpToDepth 3 datatype) (Term.Node (fromString "EmptyDatatype") [])
                        `shouldBe` Left FTAGen.EmptyGenerator
            void (Datatype.deriveFTA @(Growing Bool))
                `shouldBe` Left
                    ( Datatype.NonRegularRecursion
                        Datatype.defaultGrowthLimit
                        (typeRep $ Proxy @(Growing Bool))
                        (typeRep $ Proxy @(Growing [Bool]))
                    )

    describe "ordinary FTA generator syntax" $ do
        it "reports the error of a failed recursion through joins, groups, and lowering" $ do
            let failed = FTAGen.recur id :: FTAGen.FTAGen String Int
            sampled <- QC.generate (FTAGen.toGenEither failed)
            (sampled, FTAGen.cardinality (FTAGen.match (id :==: id) failed (FTAGen.elements [1 :: Int])))
                `shouldBe` (Left FTAGen.UnguardedRecursion, Left FTAGen.UnguardedRecursion)
            FTAGen.cardinalities (FTAGen.groupOn id failed) `shouldBe` Left FTAGen.UnguardedRecursion

        it "shrinks [False, False, True] to [True] only with smallerMembers" $ do
            -- A greedy shrink loop takes the first candidate that still fails.
            -- In a product, structural candidates shrink each component on its
            -- own, so they cannot drop a False in front of the True. A bounded
            -- recursive language shrinks by halving its size-major rank, which
            -- reaches a member with fewer elements here.
            let coin = FTAGen.oneof [FTAGen.leaf False "f", FTAGen.leaf True "t"]
                nested :: Int -> FTAGen.Gen String [Bool]
                nested 0 = FTAGen.leaf [] "nil"
                nested depth = FTAGen.oneof [FTAGen.leaf [] "nil", FTAGen.node "cons" ((:) <$> coin <*> nested (depth - 1))]
                -- [False, False, True] has size seven: three cons nodes, three coins, and nil.
                recursive :: FTAGen.Gen String [Bool]
                recursive =
                    FTAGen.upToSize 7 $
                        FTAGen.recur $
                            \self -> FTAGen.oneof [FTAGen.leaf [] "nil", FTAGen.node "cons" ((:) <$> coin <*> self)]
                shrunk lists withSmaller =
                    let fails rank = either (const False) or (FTAGen.unrank lists rank)
                        candidates rank =
                            (if withSmaller then map FTAGen.valueRank (FTAGen.smallerMembers lists rank) else [])
                                <> FTAGen.shrinkRank lists rank
                        loop rank = case filter fails (candidates rank) of
                            smaller : _ -> loop smaller
                            [] -> rank
                     in case [rank | rank <- [0 .. 62], FTAGen.unrank lists rank == Right [False, False, True]] of
                            start : _ -> FTAGen.unrank lists (loop start)
                            [] -> Left FTAGen.EmptyGenerator
            shrunk (nested 3) False `shouldBe` Right [False, False, True]
            shrunk (nested 3) True `shouldBe` Right [True]
            shrunk recursive False `shouldBe` Right [True]

        it "counts a recursion that reads a tied recursion before its own occurrence" $ do
            let trees :: FTAGen.Gen String DerivedTree
                trees = FTAGen.recur $ \self -> FTAGen.oneof [Leaf <$> FTAGen.elements [False, True], Fork <$> self <*> self]
                forest = FTAGen.recur $ \rest -> FTAGen.oneof [pure [], (:) <$> trees <*> rest]
                -- The constructors Call and (:) pay, which guards the recursions.
                calls :: FTAGen.Gen String Call
                calls =
                    FTAGen.recur $ \self ->
                        FTAGen.oneof
                            [ pure NoCall
                            , FTAGen.pay $ Call <$> FTAGen.recur (\rest -> FTAGen.oneof [pure [], FTAGen.pay $ (:) <$> self <*> rest])
                            ]
                counts = (FTAGen.countAtSize forest 1, map (FTAGen.countAtSize calls) [1 .. 4])
            counted <- timeout 10000000 $ counts <$ evaluate (length $ show counts)
            counted `shouldBe` Just (Right 2, [Right 1, Right 1, Right 2, Right 4])

        it "keeps a nested recursion whose finite members all use the outer occurrence" $ do
            let calls :: FTAGen.Gen String Call
                calls =
                    FTAGen.recur $ \self ->
                        FTAGen.oneof
                            [ pure NoCall
                            , FTAGen.pay $
                                pure Call <*> FTAGen.recur (\rest -> FTAGen.oneof [pure (: []) <*> self, FTAGen.pay $ (:) <$> self <*> rest])
                            ]
            FTAGen.isRecursive calls `shouldBe` True
            map (FTAGen.countAtSize calls) [1 .. 4] `shouldBe` [Right 1, Right 2, Right 5, Right 14]

        it "keeps the outer occurrence through a recursion whose finite members all use the middle occurrence" $ do
            -- The outer recursion reaches its own occurrence only through the
            -- inner recursion. The inner recursion has finite members only
            -- through a product of the middle occurrence and the outer one.
            let pair a b = FTAGen.pay $ (+) <$> a <*> b
                inner m o = FTAGen.recur $ \n -> FTAGen.oneof [pair m o, pair n n]
                middle o = FTAGen.recur $ \m -> FTAGen.oneof [pure 1, inner m o]
                outer :: FTAGen.FTAGen String Int
                outer = FTAGen.recur $ \o -> FTAGen.oneof [pure 0, middle o]
                bounded :: FTAGen.FTAGen String Int
                bounded = FTAGen.recur $ \o -> FTAGen.oneof [pure 0, FTAGen.upToSize 3 $ middle o]
                grouped :: FTAGen.FTAGen String Int
                grouped =
                    FTAGen.recur $ \o ->
                        FTAGen.oneof
                            [ pure 0
                            , FTAGen.atKey () $ FTAGen.recurGrouped $ \m ->
                                FTAGen.keyed () $ FTAGen.oneof [pure 1, inner (FTAGen.atKey () m) o]
                            ]
            -- In each language, O = 0 | M, M = 1 | N, and N = M * O | N * N,
            -- where each product pays one.
            map (FTAGen.countAtSize outer) [0 .. 3] `shouldBe` [Right 2, Right 2, Right 6, Right 26]
            traverse (FTAGen.unrank outer) [0 .. 3] `shouldBe` Right [0, 1, 1, 2]
            map (FTAGen.countAtSize grouped) [0 .. 3] `shouldBe` [Right 2, Right 2, Right 6, Right 26]
            -- A bound around the middle recursion reaches the outer occurrence.
            FTAGen.cardinality bounded `shouldBe` Left FTAGen.BoundedRecursiveOccurrence

        it "closes a single do binding as one direct constructor child" $ do
            let boxed = FTAGen.node "box" $ FTAGen.do
                    value <- atoms
                    FTAGen.pure $ value + 1
            FTAGen.cardinality boxed `shouldBe` Right 2
            FTAGen.unrank boxed 1 `shouldBe` Right 2
            FTAGen.termAt boxed 1
                `shouldBe` Right (Term.Node (FTAGen.Label "box") [Term.Node (FTAGen.Label "one") []])

        it "uses each do binding as one direct constructor child" $ do
            -- A child that is a choice keeps its alternative label, so equal
            -- values from different alternatives stay distinct terms.
            FTAGen.cardinality pairs `shouldBe` Right 4
            FTAGen.termAt pairs 2
                `shouldBe` Right
                    ( Term.Node
                        (FTAGen.Label "pair")
                        [ Term.Node (FTAGen.Choice 1) [Term.Node (FTAGen.Label "one") []]
                        , Term.Node (FTAGen.Choice 0) [Term.Node (FTAGen.Label "zero") []]
                        ]
                    )

        it "compiles and walks a language that two alternatives reuse once" $ do
            let depth = 40 :: Int
                chain :: Int -> FTAGen.FTAGen String (Term String)
                chain 0 = pure (Term.Node "z" [])
                chain n = FTAGen.oneof [wrap "a" <$> rest, wrap "b" <$> rest]
                  where
                    rest = chain (n - 1)
                rankedChain :: Int -> Either Ranked.RankedError (Ranked.Ranked (Term String))
                rankedChain 0 = Right (pure (Term.Node "z" []))
                rankedChain n = do
                    rest <- rankedChain (n - 1)
                    Ranked.oneof [wrap "a" <$> rest, wrap "b" <$> rest]
                wrap symbol term = Term.Node symbol [term]
                path symbol = iterate (wrap symbol) (Term.Node "z" []) !! depth
                generator = chain depth
                ranked = rankedChain depth
                lastRank = 2 ^ depth - 1
            -- The walks come before the decoders: without shared alternatives
            -- a walk takes exponential time in little memory, and the timeout
            -- stops it before a decoder fills the heap.
            completed <- timeout 10000000 $ do
                drawn <- QC.generate (FTAGen.toGen generator)
                evaluate $
                    FTAGen.minimumSize generator == Right (Just 0)
                        && FTAGen.smallest generator == Right (Just (path "a"))
                        && take 1 (FTAGen.shrinkRank generator lastRank) == [0]
                        && fmap (\language -> take 1 (Ranked.shrinkRank language lastRank)) ranked == Right [0]
                        && length (Term.flatten drawn) == depth + 1
                        && (ranked >>= (`Ranked.unrank` lastRank)) == Right (path "b")
            completed `shouldBe` Just True

        it "builds exact support accepting the term of every rank" $
            case (FTAGen.support pairs, traverse (FTAGen.termAt pairs) [0 .. 3]) of
                (Right support, Right terms) -> do
                    terms `shouldSatisfy` all (acceptsPlain support)
                    acceptsPlain support (Term.Node (FTAGen.Label "pair") [Term.Node (FTAGen.Label "zero") []])
                        `shouldBe` False
                (Left err, _) -> expectationFailure $ show err
                (_, Left err) -> expectationFailure $ show err

        it "closes every retained applicative alternative after grouping" $ do
            let source :: FTAGen.FTAGen String (Int, Int)
                source = (,) <$> FTAGen.elements [0, 1] <*> FTAGen.elements [0, 1]
                generator = FTAGen.ungroup $ FTAGen.node "group" $ FTAGen.groupOn (\(a, b) -> (a + b) `mod` 2) source
                marker = FTAGen.Label "unused-recursion-marker"
            FTAGen.cardinality generator `shouldBe` Right 4
            case (FTAGen.support generator, FTAGen.inspect generator, traverse (FTAGen.termAt generator) [0 .. 3]) of
                (Right support, Right inspection, Right terms) -> do
                    Set.fromList (Enumeration.termsWith marker support) `shouldBe` Set.fromList terms
                    let inspectionTerms =
                            Enumeration.termsWith
                                (FTAGen.InspectionSymbol marker Nothing)
                                (FTAGen.inspectionGraph inspection)
                    Set.fromList (map (fmap FTAGen.originalSymbol) inspectionTerms) `shouldBe` Set.fromList terms
                (Left err, _, _) -> expectationFailure $ show err
                (_, Left err, _) -> expectationFailure $ show err
                (_, _, Left err) -> expectationFailure $ show err

        it "filters recursive keys without losing their size classes or replay" $ do
            let recursive :: FTAGen.FTAGen String Int
                recursive = FTAGen.recur $ \self -> FTAGen.oneof [FTAGen.leaf 0 "zero", FTAGen.node "succ" $ (+ 1) <$> self]
                groups = FTAGen.oneofGrouped [FTAGen.keyed "keep" recursive, FTAGen.keyed "drop" $ FTAGen.leaf 99 "discarded"]
            calls <- newIORef []
            result <-
                FTAGen.filterGroupsM
                    (\key -> modifyIORef' calls (<> [key]) >> pure (Right $ key == "keep" :: Either String Bool))
                    groups
            readIORef calls `shouldReturn` ["drop", "keep"]
            case result of
                Left err -> expectationFailure err
                Right retained -> do
                    FTAGen.cardinality (FTAGen.atKey "drop" retained) `shouldBe` Left FTAGen.EmptyGenerator
                    let generator = FTAGen.ungroup retained
                    FTAGen.isRecursive generator `shouldBe` True
                    map (FTAGen.countAtSize generator) [0 .. 4] `shouldBe` map (FTAGen.countAtSize recursive) [0 .. 4]
                    FTAGen.values (FTAGen.upToSize 4 generator) `shouldBe` Right [0, 1, 2, 3]
                    (traverse (FTAGen.termAt generator) [0 .. 3] >>= traverse (FTAGen.rankOf generator)) `shouldBe` Right [0 .. 3]
            empty <- FTAGen.filterGroupsM (const $ pure $ Right False :: String -> IO (Either String Bool)) groups
            fmap (FTAGen.cardinality . FTAGen.ungroup) empty `shouldBe` Right (Left FTAGen.EmptyGenerator)
            failure <- FTAGen.filterGroupsM (\key -> pure $ Left key) groups
            either Just (const Nothing) failure `shouldBe` Just "drop"

        it "closes grouped function spines without mixing alternative children" $ do
            let retain = FTAGen.atKey () . FTAGen.groupOn (const ())
                source :: FTAGen.FTAGen String Int
                source = pure id <*> FTAGen.elements [0, 1]
                correlated =
                    uncurry (+)
                        <$> FTAGen.atKey
                            True
                            (FTAGen.groupOn (uncurry (==)) $ (,) <$> FTAGen.elements [0, 1] <*> FTAGen.elements [0, 1])
                sources =
                    [ retain source
                    , (+) <$> retain source <*> FTAGen.elements [10, 11]
                    , retain $ (+) <$> retain source <*> FTAGen.elements [10, 11]
                    , correlated
                    , retain $ pure 0
                    , retain $ FTAGen.elements [0, 1]
                    , retain $ FTAGen.oneof [pure 0, source, FTAGen.leaf 2 "atom"]
                    ]
                check functions = do
                    let generator = FTAGen.node "outer" $ (+) <$> functions <*> FTAGen.elements [100]
                        terms = FTAGen.cardinality generator >>= traverse (FTAGen.termAt generator) . everyRank
                        marker = FTAGen.Label "unused-recursion-marker"
                    case (FTAGen.support generator, FTAGen.inspect generator, terms) of
                        (Right support, Right inspection, Right selected) -> do
                            Set.fromList (Enumeration.termsWith marker support) `shouldBe` Set.fromList selected
                            let inspected =
                                    Enumeration.termsWith
                                        (FTAGen.InspectionSymbol marker Nothing)
                                        (FTAGen.inspectionGraph inspection)
                            Set.fromList (map (fmap FTAGen.originalSymbol) inspected) `shouldBe` Set.fromList selected
                            mapM_
                                (\(rank, term) -> FTAGen.ranksOf generator term `shouldSatisfy` either (const False) (rank `elem`))
                                (zip [0 ..] selected)
                        (Left err, _, _) -> expectationFailure $ show err
                        (_, Left err, _) -> expectationFailure $ show err
                        (_, _, Left err) -> expectationFailure $ show err
            mapM_ check sources

        it "keeps recursive members whole when labels close choices and applicative spines" $ do
            let chain :: FTAGen.FTAGen String Int
                chain = FTAGen.recur $ \self -> FTAGen.oneof [pure 0, FTAGen.node "s" $ (+ 1) <$> self]
                spine :: FTAGen.FTAGen String Int
                spine = FTAGen.recur $ \self -> (+) <$> FTAGen.oneof [pure 0, self] <*> FTAGen.elements [1, 2]
                blocked result = either (== FTAGen.QueriedRecursiveOccurrence) (const False) result
                observeSelf checks = FTAGen.recur $ \self ->
                    FTAGen.oneof [pure (if checks self then 0 else 100), FTAGen.node "s" $ (+ 1) <$> self]
                observations =
                    [ blocked . FTAGen.support
                    , blocked . FTAGen.inspect
                    , \self -> blocked $ FTAGen.countAtSize self 0
                    , blocked . FTAGen.minimumSize
                    , \self -> blocked $ FTAGen.unrank self 0
                    , \self -> blocked $ FTAGen.termAt self 0
                    , \self -> blocked $ FTAGen.ranksOf self (Term.Node FTAGen.Pure [])
                    , \self -> blocked $ FTAGen.pmfAtSize self 0
                    , \self -> blocked $ FTAGen.countsAtSize (FTAGen.keyed () self) 0
                    , \self -> blocked $ FTAGen.massesAtSize (FTAGen.keyed () self) 0
                    , \self -> isNothing (FTAGen.sizeOfRank self 0) && null (FTAGen.smallerMembers self 0)
                    , \self ->
                        blocked $ FTAGen.support $ FTAGen.recur $ \inner ->
                            FTAGen.oneof [pure 0, FTAGen.node "i" inner, FTAGen.node "o" self]
                    , \self -> FTAGen.cardinality (FTAGen.upToSize 1 self) == Left FTAGen.BoundedRecursiveOccurrence
                    , \self -> FTAGen.cardinality (FTAGen.atomic self) == Left FTAGen.BoundedRecursiveOccurrence
                    ]
                inspected = map observeSelf observations
                changing = FTAGen.recur $ \self -> case FTAGen.support self of
                    Right Common.EmptyNode -> FTAGen.oneof [pure 0, FTAGen.node "s" $ (+ 1) <$> self]
                    _ -> FTAGen.leaf 99 "wrong"
                selected = FTAGen.recur $ \outer -> FTAGen.atKey False $ FTAGen.recurGrouped $ \self ->
                    FTAGen.oneofGrouped
                        [ FTAGen.keyed False (pure 0)
                        , FTAGen.keyed True (FTAGen.node "outer" outer)
                        , FTAGen.keyed True (FTAGen.node "next" $ FTAGen.atKey True self)
                        ]
                changingMinimum = FTAGen.recurGrouped $ \self ->
                    FTAGen.oneofGrouped
                        [ FTAGen.keyed False $ case FTAGen.countsAtSize self 0 of
                            Right counts | null counts -> pure (0 :: Int)
                            _ -> FTAGen.leaf 1 "base"
                        , FTAGen.keyed False (FTAGen.node "step" $ (+ 1) <$> FTAGen.atKey False self)
                        ]
                apply generator = FTAGen.node "outer" $ (+) <$> generator <*> FTAGen.elements [10]
                check generator = do
                    let bounded = FTAGen.upToSize 4 generator
                    case (FTAGen.cardinality bounded, FTAGen.support bounded, FTAGen.inspect bounded) of
                        (Right count, Right support, Right inspection) ->
                            mapM_
                                ( \rank -> case FTAGen.termAt bounded rank of
                                    Left err -> expectationFailure $ show err
                                    Right term -> do
                                        acceptsPlain support term `shouldBe` True
                                        Common.acceptsWith
                                            (\_ _ -> True)
                                            (FTAGen.inspectionGraph inspection)
                                            (fmap (\symbol -> FTAGen.InspectionSymbol symbol Nothing) term)
                                            `shouldBe` True
                                        FTAGen.ranksOf bounded term `shouldSatisfy` either (const False) (rank `elem`)
                                )
                                (everyRank count)
                        (Left err, _, _) -> expectationFailure $ show err
                        (_, Left err, _) -> expectationFailure $ show err
                        (_, _, Left err) -> expectationFailure $ show err
            traverse (FTAGen.unrank $ FTAGen.upToSize 3 chain) [0 .. 3] `shouldBe` Right [0, 1, 2, 3]
            map (\generator -> traverse (FTAGen.unrank $ FTAGen.upToSize 3 generator) [0 .. 3]) inspected
                `shouldBe` replicate (length inspected) (Right [0, 1, 2, 3])
            FTAGen.values changing `shouldBe` Right [99]
            FTAGen.countAtSize selected 0 `shouldBe` Right 1
            FTAGen.minimumSize selected `shouldBe` Right (Just 0)
            FTAGen.minimumSize (FTAGen.atKey False changingMinimum)
                `shouldBe` Left FTAGen.InconsistentRecursiveFamily
            FTAGen.countsAtSize changingMinimum 0
                `shouldBe` Left FTAGen.InconsistentRecursiveFamily
            mapM_ check $
                [chain, spine, changing, selected]
                    <> inspected
                    <> [ wrap generator
                       | generator <- [chain, spine]
                       , wrap <- [FTAGen.node "outer", apply, FTAGen.node "outer" . FTAGen.upToSize 3, apply . FTAGen.upToSize 3]
                       ]

    describe "ordinary FTA compilation" $ do
        it "indexes recursive runs by size and bounds them by depth" $ do
            let rows = [((), [Automaton.Transition "z" [] noConstraint, Automaton.Transition "s" [()] noConstraint])]
                terms = take 5 $ iterate (\term -> Term.Node "s" [term]) (Term.Node "z" [])
            case Automaton.mkFTA () rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let node = Common.fromFTA automaton
                        check generator = do
                            FTAGen.cardinality generator `shouldBe` Right 5
                            traverse (FTAGen.unrank generator) [0 .. 4] `shouldBe` Right terms
                            map (FTAGen.sizeOfRank generator) [0 .. 4] `shouldBe` map Just [1 .. 5]
                            FTAGen.shrinkRank generator 4 `shouldSatisfy` (not . null)
                            map (FTAGen.unrank generator) (FTAGen.shrinkRank generator 4)
                                `shouldSatisfy` all (`elem` map Right (take 4 terms))
                    check $ FTAGen.upToSize 5 $ FTAGen.fromAutomaton node
                    check $ FTAGen.fromAutomatonUpToDepth 4 node
                    -- The terms rank back to their ranks, also by size in the recursive import.
                    let bounded = FTAGen.fromAutomatonUpToDepth 4 node
                        recursive = FTAGen.fromAutomaton node
                        deeper = Term.Node "s" [last terms]
                        wrongArity = Term.Node "s" []
                    ranksEveryMemberBack FTAGen.rankOfTerm bounded
                    ranksBack FTAGen.rankOfTerm recursive [0 .. 9]
                    map (FTAGen.rankOfTerm bounded) [deeper, wrongArity]
                        `shouldBe` [Left FTAGen.TermNotInLanguage, Left FTAGen.TermNotInLanguage]
                    map (FTAGen.rankOfTerm recursive) [deeper, wrongArity]
                        `shouldBe` [Right 5, Left FTAGen.TermNotInLanguage]
                    -- The recursive import decodes the term of a size-major rank.
                    traverse (FTAGen.termAt $ FTAGen.fromAutomaton node) [0 .. 4]
                        `shouldBe` Right (map (fmap FTAGen.Label) terms)
                    FTAGen.cardinality (FTAGen.upToSize 0 $ FTAGen.fromAutomaton node)
                        `shouldBe` Left FTAGen.EmptyGenerator

        it "keeps empty recursion distinct from ambiguity and counts distinct finite terms" $ do
            let rows =
                    [ (0 :: Int, [Automaton.Transition "step" [1] noConstraint])
                    , (1, [Automaton.Transition "again" [0] noConstraint])
                    ]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right empty -> do
                    FTAGen.cardinality (FTAGen.upToSize 10 $ FTAGen.fromAutomaton $ Common.fromFTA empty)
                        `shouldBe` Left FTAGen.EmptyGenerator
                    FTAGen.rankOfTerm (FTAGen.fromAutomaton $ Common.fromFTA empty) (Term.Node "step" [Term.Node "again" []])
                        `shouldBe` Left FTAGen.EmptyGenerator
            let productive =
                    [
                        ( 0 :: Int
                        ,
                            [ Automaton.Transition "z" [] noConstraint
                            , Automaton.Transition "step" [1] noConstraint
                            , Automaton.Transition "step" [2] noConstraint
                            ]
                        )
                    , (1, [Automaton.Transition "again" [0] noConstraint, Automaton.Transition "extra" [] noConstraint])
                    , (2, [Automaton.Transition "again" [0] noConstraint])
                    ]
            case Automaton.mkFTA 0 productive of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    -- Size counting sums over accepting runs, so it rejects
                    -- the ambiguous recursion; the finite bound counts each
                    -- distinct term once.
                    let node = Common.fromFTA automaton
                        bounded = FTAGen.fromAutomatonUpToDepth 4 node
                    FTAGen.cardinality (FTAGen.upToSize 5 $ FTAGen.fromAutomaton node)
                        `shouldBe` Left FTAGen.AmbiguousAutomaton
                    FTAGen.cardinality bounded `shouldBe` Right 5
                    fmap (length . nub) (traverse (FTAGen.unrank bounded) [0 .. 4])
                        `shouldBe` Right 5
                    -- The two step alternatives overlap, so the bound ranks symbolically.
                    ranksEveryMemberBack FTAGen.rankOfTerm bounded
                    FTAGen.rankOfTerm (FTAGen.fromAutomaton node) (Term.Node "z" [])
                        `shouldBe` Left FTAGen.AmbiguousAutomaton

        it "compiles the common interned unit-constraint graph without ECTA" $ do
            let leaves = Common.Node [Common.Edge "zero" [], Common.Edge "one" []] :: Common.Node String
                root = Common.Node [Common.Edge "pair" [leaves, leaves]]
                expected =
                    [ Term.Node "pair" [Term.Node left [], Term.Node right []]
                    | left <- ["one", "zero"]
                    , right <- ["one", "zero"]
                    ]
                generator = FTAGen.fromAutomaton root
            case Common.toFTA root of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    FTAGen.cardinality generator `shouldBe` Right 4
                    traverse (FTAGen.unrank generator) [0 .. 3] `shouldBe` Right expected
                    all (Automaton.accepts automaton) expected `shouldBe` True
                    ranksEveryMemberBack FTAGen.rankOfTerm generator
                    map (FTAGen.rankOfTerm generator) [Term.Node "pair" [Term.Node "one" []], Term.Node "zero" []]
                        `shouldBe` [Left FTAGen.TermNotInLanguage, Left FTAGen.TermNotInLanguage]

        it "ranks imported alternatives in symbol order, not in interning order" $ do
            -- Interning is global: these symbols appear in no other test.
            let leaves = [Term.Node "order-a" [], Term.Node "order-b" []]
                flat = Common.Node [Common.Edge "order-a" [], Common.Edge "order-b" []] :: Common.Node String
                transitions =
                    [Automaton.Transition symbol [] noConstraint | symbol <- ["order-b", "order-a"]]
                        <> [Automaton.Transition "order-s" [()] noConstraint]
            -- Intern the later symbol first.
            void $ evaluate $ Common.nodeCount (Common.Node [Common.Edge "order-b" []] :: Common.Node String)
            FTAGen.values (FTAGen.fromAutomaton flat) `shouldBe` Right leaves
            ranksEveryMemberBack FTAGen.rankOfTerm $ FTAGen.fromAutomaton flat
            case Automaton.mkFTA () [((), transitions)] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    FTAGen.values (FTAGen.upToSize 1 $ FTAGen.fromAutomaton $ Common.fromFTA automaton)
                        `shouldBe` Right leaves
                    ranksBack FTAGen.rankOfTerm (FTAGen.fromAutomaton $ Common.fromFTA automaton) [0 .. 9]

        it "keeps the constructors of one arity apart when the order key does not tell them apart" $ do
            -- Every symbol has the key (), so only the symbol keeps "tie-a" and "tie-b" apart.
            let rows =
                    [ ("q", [Automaton.Transition "tie-f" ["r"] noConstraint, Automaton.Transition "tie-f" ["s"] noConstraint])
                    , ("r", [Automaton.Transition "tie-a" [] noConstraint, Automaton.Transition "tie-b" [] noConstraint])
                    , ("s", [Automaton.Transition "tie-a" [] noConstraint])
                    ]
            case Automaton.mkFTA ("q" :: String) rows of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    FTAGen.values (Flat.fromAutomaton (const ()) $ Common.fromFTA automaton)
                        `shouldBe` Right [Term.Node "tie-f" [Term.Node symbol []] | symbol <- ["tie-a", "tie-b"]]

        it "ranks alternatives with one symbol by their children, not in interning order" $ do
            -- Interning is global: these symbols appear in no other test.
            let leaf symbol = Common.Node [Common.Edge symbol []] :: Common.Node String
                pair symbol = Common.Edge "canonical-pair" [leaf symbol]
                flat = Common.Node [pair "canonical-a", pair "canonical-b"]
            -- Intern the later alternative first.
            void $ evaluate $ Common.nodeCount (Common.Node [pair "canonical-b"])
            FTAGen.values (FTAGen.fromAutomaton flat)
                `shouldBe` Right [Term.Node "canonical-pair" [Term.Node symbol []] | symbol <- ["canonical-a", "canonical-b"]]
            ranksEveryMemberBack FTAGen.rankOfTerm $ FTAGen.fromAutomaton flat

        it "ranks alternatives with one symbol in a cyclic automaton by their children" $ do
            -- Interning is global: these symbols appear in no other test.
            let leaf symbol = Common.Node [Common.Edge symbol []] :: Common.Node String
                pair symbol = Common.Edge "cyclic-pair" [leaf symbol]
                cyclic = Common.createMu $ \self -> Common.Node [Common.Edge "cyclic-end" [], Common.Edge "cyclic-wrap" [self], pair "cyclic-a", pair "cyclic-b"]
                paired symbol = Term.Node "cyclic-pair" [Term.Node symbol []]
            -- Intern the later alternative first.
            void $ evaluate $ Common.nodeCount (Common.Node [pair "cyclic-b"])
            FTAGen.values (FTAGen.upToSize 2 $ FTAGen.fromAutomaton cyclic)
                `shouldBe` Right
                    [ Term.Node "cyclic-end" []
                    , paired "cyclic-a"
                    , paired "cyclic-b"
                    , Term.Node "cyclic-wrap" [Term.Node "cyclic-end" []]
                    ]

        it "shares state compilation and decoding across a large finite DAG" $ do
            let depth = 64 :: Int
                rows =
                    (0, [Automaton.Transition "z" [] noConstraint])
                        : [ (state, [Automaton.Transition "a" [state - 1] noConstraint, Automaton.Transition "b" [state - 1] noConstraint])
                          | state <- [1 .. depth]
                          ]
                chain symbol = iterate (\term -> Term.Node symbol [term]) (Term.Node "z" []) !! depth
            case Automaton.mkFTA depth rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let generator = FTAGen.fromAutomaton $ Common.fromFTA automaton
                    completed <-
                        timeout 60000000
                            $ evaluate
                            $ FTAGen.cardinality generator == Right (2 ^ depth)
                                && FTAGen.unrank generator 0 == Right (chain "a")
                                && FTAGen.unrank generator (2 ^ depth - 1) == Right (chain "b")
                    completed `shouldBe` Just True
                    -- The size and shrink walks read each shared state once.
                    walked <-
                        timeout 60000000
                            $ evaluate
                            $ FTAGen.minimumSize generator == Right (Just (toEnum depth + 1))
                                && FTAGen.smallest generator == Right (Just (chain "a"))
                                && null (FTAGen.smallerMembers generator 0)
                                && take 1 (FTAGen.shrinkRank generator (2 ^ depth - 1)) == [0]
                    walked `shouldBe` Just True
                    ranksBack FTAGen.rankOfTerm generator [0, 1, 2 ^ (depth - 1), 2 ^ depth - 1]

        it "preserves ranks and structural shrinking through shared states" $ do
            let rows =
                    [ (0, [Automaton.Transition "x" [] noConstraint, Automaton.Transition "y" [] noConstraint])
                    , (1, [Automaton.Transition "a" [] noConstraint, Automaton.Transition "wrap" [0] noConstraint])
                    , (2, [Automaton.Transition "pair" [1, 1] noConstraint])
                    ]
                -- Each node of an imported term pays one, so each node of the reference pays.
                reference = do
                    leaves <- Ranked.oneof [Ranked.pay $ pure $ Term.Node "x" [], Ranked.pay $ pure $ Term.Node "y" []]
                    alternatives <-
                        Ranked.oneof
                            [ Ranked.pay $ pure $ Term.Node "a" []
                            , Ranked.pay $ pure (\child -> Term.Node "wrap" [child]) <*> leaves
                            ]
                    pure $ Ranked.pay $ pure (\left right -> Term.Node "pair" [left, right]) <*> alternatives <*> alternatives
            case Automaton.mkFTA (2 :: Int) rows of
                Left err -> expectationFailure $ show err
                Right automaton -> case reference of
                    Left err -> expectationFailure $ show err
                    Right expected -> do
                        let actual = FTAGen.fromAutomaton $ Common.fromFTA automaton
                            ranks = everyRank $ Ranked.cardinality expected
                            members = either (const Nothing) Just
                        FTAGen.cardinality actual `shouldBe` Right (Ranked.cardinality expected)
                        members (traverse (FTAGen.unrank actual) ranks) `shouldBe` members (traverse (Ranked.unrank expected) ranks)
                        map (FTAGen.sizeOfRank actual) ranks `shouldBe` map (Ranked.sizeOfRank expected) ranks
                        map (FTAGen.shrinkRank actual) ranks `shouldBe` map (Ranked.shrinkRank expected) ranks
                        map (FTAGen.smallerMembers actual) ranks `shouldBe` map (Ranked.smallerMembers expected) ranks
                        ranksEveryMemberBack FTAGen.rankOfTerm actual

        it "positions left-deep terms of transitions that share a symbol" $ do
            -- Both f transitions accept every left child, and only the right
            -- child tells them apart. A search from the root would visit the
            -- left child once for each transition at each level.
            let rows =
                    [
                        ( "list"
                        ,
                            [ Automaton.Transition "a" [] noConstraint
                            , Automaton.Transition "f" ["list", "b"] noConstraint
                            , Automaton.Transition "f" ["list", "c"] noConstraint
                            ]
                        )
                    , ("b", [Automaton.Transition "b" [] noConstraint])
                    , ("c", [Automaton.Transition "c" [] noConstraint])
                    ]
                deep = foldl' (\term right -> Term.Node "f" [term, Term.Node right []]) (Term.Node "a" []) (replicate 40 "c")
            case Automaton.mkFTA "list" rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let generator = FTAGen.fromAutomaton $ Common.fromFTA automaton
                    ranksBack FTAGen.rankOfTerm generator [0 .. 30]
                    FTAGen.rankOfTerm generator (Term.Node "f" [Term.Node "a" [], Term.Node "a" []])
                        `shouldBe` Left FTAGen.TermNotInLanguage
                    (FTAGen.rankOfTerm generator deep >>= \rank -> (,) (FTAGen.sizeOfRank generator rank) <$> FTAGen.unrank generator rank)
                        `shouldBe` Right (Just 81, deep)

    describe "ordinary FTA integer expressions" $ do
        it "has the exact structural cardinality at every bounded depth" $
            map (FTAGen.cardinality . Expressions.expressionsAtDepth) [0 .. 4]
                `shouldBe` map (Right . Cardinality . Expressions.expressionCount) [0 .. 4]

        it "decodes every rank of the depth-two language" $ do
            let expressions = Expressions.expressionsAtDepth 2
                total = fromRight 0 $ FTAGen.cardinality expressions
                generated =
                    [ expression
                    | rank <- everyRank total
                    , Right expression <- [FTAGen.unrank expressions rank]
                    ]
            toEnum (length generated) `shouldBe` total

        modifyMaxSuccess (const 500)
            $ it "keeps both reference generators in the exact-depth language"
            $ QC.conjoin
                [ QC.forAll (generator 3) $ \expression ->
                    QC.counterexample (show expression) $
                        expressionDepth expression QC.=== 3
                | generator <-
                    [ Expressions.naiveExpressionGen
                    , Expressions.handwrittenExpressionGen
                    ]
                ]

-- | Number of constructor layers in an untyped expression.
expressionDepth :: Expressions.Expression -> Int
expressionDepth (Expressions.Literal _) = 0
expressionDepth (Expressions.Add left right) =
    1 + max (expressionDepth left) (expressionDepth right)
expressionDepth (Expressions.Multiply left right) =
    1 + max (expressionDepth left) (expressionDepth right)

-- | Membership in a plain interned support.
acceptsPlain :: Common.Node (FTAGen.Label String) -> Term (FTAGen.Label String) -> Bool
acceptsPlain = Common.acceptsWith (\_ _ -> True)

-- | The generator symbol of a derived constructor.
constructorSymbol :: Datatype.Constructor -> FTAGen.Label Symbol
constructorSymbol = FTAGen.Label . fromString . Datatype.constructorLabel
