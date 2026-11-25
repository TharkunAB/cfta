{-# LANGUAGE OverloadedStrings #-}

{- | Principal sorts of a signature with sort variables: exact sorts, the
errors of the type check, the occurs check, the signature check, and a
reference that instantiates each function at closed sorts without
unification. The equality automaton: against the saturated search space of
"Data.CFTA.Gen.Synthesis", against the type check, and the counts of its
generator.
-}
module Data.CFTA.Gen.ManySorted.PolymorphicSpec (spec) where

import Control.Monad (foldM)
import Data.Either (isRight)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Equality as Equality
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.ManySorted (SortedFunction (..), TypeError (..))
import Data.CFTA.Gen.ManySorted.Polymorphic
import Data.CFTA.Gen.Synthesis (
    Library (..),
    Program (..),
    Query (..),
    Saturation (..),
    distinctSaturatedSolutionsOfSize,
    library,
    parseType,
 )
import Data.CFTA.Index (Cardinality (..), Size (..), everyRank)
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Sized (countOfSize, sized, termsOfSize)
import Data.CFTA.Symbol (Symbol (Symbol), symbolText)
import Data.CFTA.Term (Term (Node))

-- | The sort variables 0 and 1.
a, b :: SortTerm
a = SortVariable 0
b = SortVariable 1

int, bool :: SortTerm
int = SortApply "Int" []
bool = SortApply "Bool" []

list :: SortTerm -> SortTerm
list element = SortApply "List" [element]

pair :: SortTerm -> SortTerm -> SortTerm
pair left right = SortApply "Pair" [left, right]

-- | Table 1: zero, true, ite, eq, nil, cons, and length.
table1 :: PolymorphicSignature
table1 =
    PolymorphicSignature
        [ SortedFunction "zero" [] int
        , SortedFunction "true" [] bool
        , SortedFunction "ite" [bool, a, a] a
        , SortedFunction "eq" [a, a] bool
        , SortedFunction "nil" [] (list a)
        , SortedFunction "cons" [a, list a] (list a)
        , SortedFunction "length" [list a] int
        ]

-- | Table 2: table 1 with pair, fst, and snd.
table2 :: PolymorphicSignature
table2 =
    PolymorphicSignature $
        polymorphicFunctions table1
            <> [ SortedFunction "pair" [a, b] (pair a b)
               , SortedFunction "fst" [pair a b] a
               , SortedFunction "snd" [pair a b] b
               ]

-- | Table 2 with @same : Pair a (List a) -> Bool@ and @dup : a -> Pair a a@, which need the occurs check.
occursTable :: PolymorphicSignature
occursTable =
    PolymorphicSignature $
        polymorphicFunctions table2
            <> [SortedFunction "same" [pair a (list a)] bool, SortedFunction "dup" [a] (pair a a)]

zero, true, nil :: Term Symbol
zero = Node "zero" []
true = Node "true" []
nil = Node "nil" []

-- | The closed sorts over Int, Bool, and List, with at most three List.
closedSorts :: [SortTerm]
closedSorts = concat (take 4 (iterate (map list) [int, bool]))

{- | Every sort in 'closedSorts' of a term over 'table1'. It tries each
instance of each function at the sorts of 'closedSorts', bottom-up, and it
uses no unification. The sort of each node must be in 'closedSorts'.
-}
sortsOf :: Term Symbol -> Set.Set SortTerm
sortsOf (Node symbol children) =
    Set.fromList
        [ result
        | function <- polymorphicFunctions table1
        , functionSymbol function == symbol
        , length (functionArguments function) == length children
        , choice <- mapM (\variable -> [(variable, closed) | closed <- closedSorts]) (variablesOf function)
        , let instantiate = substituteWith (Map.fromList choice)
              result = instantiate (functionResult function)
        , result `elem` closedSorts
        , and
            (zipWith (\argument childSorts -> Set.member (instantiate argument) childSorts) (functionArguments function) childSets)
        ]
  where
    childSets = map sortsOf children
    variablesOf function = Set.toList (Set.fromList (concatMap occurrences (functionResult function : functionArguments function)))
    occurrences (SortVariable variable) = [variable]
    occurrences (SortApply _ arguments) = concatMap occurrences arguments
    substituteWith choice sortTerm = case sortTerm of
        SortVariable variable -> Map.findWithDefault sortTerm variable choice
        SortApply constructor arguments -> SortApply constructor (map (substituteWith choice) arguments)

-- | Whether a closed sort is an instance of a sort, by one-way matching.
instanceOf :: SortTerm -> SortTerm -> Bool
instanceOf general closed = isJust (match Map.empty general closed)
  where
    match bound (SortVariable variable) sortTerm = case Map.lookup variable bound of
        Nothing -> Just (Map.insert variable sortTerm bound)
        Just earlier -> if earlier == sortTerm then Just bound else Nothing
    match bound (SortApply one left) (SortApply other right)
        | one == other && length left == length right = foldM (\current (l, r) -> match current l r) bound (zip left right)
    match _ _ _ = Nothing

-- | Every term with the given number of nodes, over some symbols, with any arity from zero to three.
untypedTerms :: [Symbol] -> Int -> [Term Symbol]
untypedTerms symbols size =
    [ Node symbol children
    | symbol <- symbols
    , arity <- [0 .. 3 :: Int]
    , children <- split arity (size - 1)
    ]
  where
    split 0 0 = [[]]
    split 0 _ = []
    split n budget =
        [ first : rest
        | firstSize <- [1 .. budget]
        , first <- untypedTerms symbols firstSize
        , rest <- split (n - 1) (budget - firstSize)
        ]

-- | Every tree up to size 5 over the symbols of 'table1', with any arity from zero to three.
smallTrees :: [Term Symbol]
smallTrees = concatMap (untypedTerms (map functionSymbol (polymorphicFunctions table1))) [1 .. 5]

-- | Table 2 with @nil\@Int : List Int@ and @nil\@Bool : List Bool@ in the place of @nil@. No function is open.
closedTable :: PolymorphicSignature
closedTable =
    PolymorphicSignature $
        [function | function <- polymorphicFunctions table2, functionSymbol function /= "nil"]
            <> [SortedFunction "nil@Int" [] (list int), SortedFunction "nil@Bool" [] (list bool)]

-- | The root sorts of the tests of the automaton.
roots1, roots2 :: [SortTerm]
roots1 = [int, bool, list int, list bool]
roots2 = roots1 <> [pair int bool]

-- | A sort as a type of "Data.CFTA.Gen.Synthesis": the variables 0 to 3 are a to d.
hectareType :: SortTerm -> Text
hectareType sortTerm = case sortTerm of
    SortVariable variable -> Text.singleton (toEnum (fromEnum 'a' + variable))
    SortApply "List" [element] -> "[" <> hectareType element <> "]"
    SortApply "Pair" [left, right] -> "(" <> hectareType left <> ", " <> hectareType right <> ")"
    SortApply constructor _ -> symbolText constructor

{- | The library and the saturation of a signature for "Data.CFTA.Gen.Synthesis",
and the names of the components by their group representatives.
-}
hectare :: PolymorphicSignature -> (Library, Saturation, Map.Map Text Text)
hectare signature = (lib, saturation, members)
  where
    functions = polymorphicFunctions signature
    name = symbolText . functionSymbol
    functionType function = Text.intercalate " -> " (map hectareType (functionArguments function <> [functionResult function]))
    lib = library [(name function, either error id (parseType (functionType function))) | function <- functions] [] []
    representatives = Map.fromList [(member, representative) | (representative, _, [member]) <- libraryGroups lib]
    members = Map.fromList [(representative, member) | (member, representative) <- Map.toList representatives]
    saturation =
        Saturation
            { saturationArities =
                Map.fromList
                    [ (representatives Map.! name function, length (functionArguments function))
                    | function <- functions
                    , not (null (functionArguments function))
                    ]
            , saturationValues = [representatives Map.! name function | function <- functions, null (functionArguments function)]
            }

-- | A program of "Data.CFTA.Gen.Synthesis" as a plain term, with the names of the components.
programTerm :: Map.Map Text Text -> Program -> Term Symbol
programTerm members = go []
  where
    go arguments (App function argument) = go (argument : arguments) function
    go arguments (Var name) = Node (Symbol (Map.findWithDefault name name members)) (map (go []) arguments)

spec :: Spec
spec = describe "Data.CFTA.Gen.ManySorted.Polymorphic" $ do
    describe "principalSort" $ do
        it "gives the principal sorts of table 1" $ do
            principalSort table1 nil `shouldBe` Right (list a)
            principalSort table1 (Node "cons" [nil, nil]) `shouldBe` Right (list (list a))
            principalSort table1 (Node "length" [nil]) `shouldBe` Right int
            principalSort table1 (Node "eq" [nil, nil]) `shouldBe` Right bool
            principalSort table1 (Node "ite" [true, nil, Node "cons" [zero, nil]]) `shouldBe` Right (list int)

        it "renames the variables of the children apart, in table 2" $ do
            principalSort table2 (Node "pair" [nil, nil]) `shouldBe` Right (pair (list a) (list b))
            principalSort table2 (Node "fst" [Node "pair" [zero, nil]]) `shouldBe` Right int
            principalSort table2 (Node "snd" [Node "pair" [zero, nil]]) `shouldBe` Right (list a)
            principalSort table2 (Node "pair" [Node "snd" [Node "pair" [zero, nil]], true]) `shouldBe` Right (pair (list a) bool)

        it "numbers the variables from 0, for any numbers in the signature" $ do
            let renumbered =
                    PolymorphicSignature
                        [ SortedFunction "zero" [] int
                        , SortedFunction "nil" [] (list (SortVariable 5))
                        , SortedFunction "pair" [SortVariable 5, SortVariable 3] (pair (SortVariable 3) (SortVariable 5))
                        ]
            principalSort renumbered nil `shouldBe` Right (list a)
            principalSort renumbered (Node "pair" [zero, nil]) `shouldBe` Right (pair (list a) int)
            principalSort renumbered (Node "pair" [nil, nil]) `shouldBe` Right (pair (list a) (list b))

        it "reports children whose sorts do not unify with the argument sorts" $ do
            principalSort table1 (Node "eq" [zero, true])
                `shouldBe` Left (WrongChildSort (path []) "eq" [a, a] [Just int, Just bool])
            principalSort table1 (Node "cons" [zero, Node "cons" [true, nil]])
                `shouldBe` Left (WrongChildSort (path []) "cons" [a, list a] [Just int, Just (list bool)])

        it "names the parent when the children with a sort do not unify, and the child otherwise" $ do
            principalSort table1 (Node "ite" [zero, Node "foo" [], zero])
                `shouldBe` Left (WrongChildSort (path []) "ite" [bool, a, a] [Just int, Nothing, Just int])
            principalSort table1 (Node "cons" [Node "eq" [zero, true], nil])
                `shouldBe` Left (WrongChildSort (path [ChildIndex 0]) "eq" [a, a] [Just int, Just bool])

        it "reports a wrong number of children and an unknown symbol" $ do
            principalSort table1 (Node "cons" [zero]) `shouldBe` Left (WrongArity (path []) "cons" 2 1)
            principalSort table1 (Node "length" [Node "foo" []]) `shouldBe` Left (UnknownFunction (path [ChildIndex 0]) "foo")

        it "makes the occurs check" $ do
            principalSort occursTable (Node "same" [Node "dup" [nil]])
                `shouldBe` Left (WrongChildSort (path []) "same" [pair a (list a)] [Just (pair (list a) (list a))])
            principalSort occursTable (Node "same" [Node "pair" [zero, nil]]) `shouldBe` Right bool

        it "agrees with an instantiation at closed sorts on every term up to size 5" $ do
            let trees = smallTrees
                wellSorted = filter (isRight . principalSort table1) trees
            length trees `shouldSatisfy` (> 200000)
            length wellSorted `shouldSatisfy` (> 40)
            mapM_
                ( \term -> do
                    let reference = sortsOf term
                    case principalSort table1 term of
                        Left _ -> do
                            (term, reference) `shouldBe` (term, Set.empty)
                            (term, hasSort table1 a term) `shouldBe` (term, False)
                        Right principal -> do
                            let instances = filter (instanceOf principal) closedSorts
                            (term, Set.null reference) `shouldBe` (term, False)
                            (term, Set.fromList instances) `shouldBe` (term, reference)
                            (term, filter (\closed -> hasSort table1 closed term) closedSorts) `shouldBe` (term, instances)
                            (term, hasSort table1 a term) `shouldBe` (term, True)
                )
                trees

    describe "checkPolymorphic" $
        it "rejects a repeated symbol and a sort constructor with two numbers of arguments" $ do
            checkPolymorphic table1 `shouldBe` Right ()
            checkPolymorphic table2 `shouldBe` Right ()
            checkPolymorphic (PolymorphicSignature (polymorphicFunctions table1 <> [SortedFunction "nil" [] (list int)]))
                `shouldBe` Left (RepeatedSymbol "nil")
            checkPolymorphic
                (PolymorphicSignature (polymorphicFunctions table1 <> [SortedFunction "zip" [SortApply "List" [a, b]] int]))
                `shouldBe` Left (ConstructorArity "List" 1 2)

    describe "hasSort" $
        it "tests whether a term has an instance of a sort" $ do
            hasSort table1 (list int) nil `shouldBe` True
            hasSort table1 (list bool) nil `shouldBe` True
            hasSort table1 (list a) nil `shouldBe` True
            hasSort table1 int nil `shouldBe` False
            hasSort table1 (list int) (Node "cons" [zero, nil]) `shouldBe` True
            hasSort table1 (list a) (Node "cons" [zero, nil]) `shouldBe` True
            hasSort table1 (list bool) (Node "cons" [zero, nil]) `shouldBe` False
            hasSort table1 a (Node "eq" [zero, true]) `shouldBe` False
            -- The variable 0 of the root and of the principal sort are different variables.
            hasSort table2 (pair a bool) (Node "pair" [nil, true]) `shouldBe` True
            hasSort table2 (pair a a) (Node "pair" [nil, nil]) `shouldBe` True
            hasSort table2 (pair a a) (Node "pair" [zero, true]) `shouldBe` False

    describe "polymorphicSpace" $ do
        mapM_
            ( \(name, signature, roots, maxSize, totals) ->
                it ("lists the programs of the saturated search space of Data.CFTA.Gen.Synthesis, each once, for " <> name) $ do
                    let (lib, saturation, members) = hectare signature
                        cells =
                            [ (root, size, polymorphicTerms signature root size, programs)
                            | size <- [1 .. maxSize]
                            , root <- roots
                            , let goal = either error id (parseType (hectareType root))
                                  programs = map (programTerm members) (distinctSaturatedSolutionsOfSize saturation lib (Query [] goal) size)
                            ]
                    mapM_
                        ( \(root, size, listed, programs) -> do
                            (root, size, Set.fromList listed) `shouldBe` (root, size, Set.fromList programs)
                            (root, size, length listed) `shouldBe` (root, size, Set.size (Set.fromList listed))
                        )
                        cells
                    -- The distinct plain terms of a size over the roots Int, Bool, List Int, and List Bool.
                    [ Set.size (Set.fromList [term | (root, size', listed, _) <- cells, size' == size, root `elem` roots1, term <- listed])
                      | size <- [1 .. maxSize]
                      ]
                        `shouldBe` totals
            )
            [ ("table 1", table1, roots1, 6, [3, 1, 5, 9, 22, 58])
            , ("table 2", table2, roots2, 6, [3, 1, 5, 27, 40, 251])
            ]

        it "lists exactly the trees up to size 5 that have an instance of the root sort, in table 1" $ do
            let roots = roots1 <> [a]
                listed = Map.fromList [((root, size), polymorphicTerms table1 root size) | root <- roots, size <- [1 .. 5]]
                listedSets = Map.map Set.fromList listed
            sum (map length (Map.elems listed)) `shouldSatisfy` (> 40)
            mapM_
                (\((root, _), terms) -> mapM_ (\term -> (root, term, hasSort table1 root term) `shouldBe` (root, term, True)) terms)
                (Map.toList listed)
            mapM_
                ( \(root, tree) ->
                    (root, tree, Set.member tree (listedSets Map.! (root, length tree))) `shouldBe` (root, tree, hasSort table1 root tree)
                )
                [(root, tree) | root <- roots, tree <- smallTrees]

        it "counts every space of a table without an open function" $ do
            openFunctions closedTable `shouldBe` []
            let cells = [(root, size) | root <- roots2, size <- [1 .. 5]]
            mapM_
                ( \(root, size) -> do
                    let listed = polymorphicTerms closedTable root size
                        typed = Equality.terms (polymorphicSpace closedTable root size)
                        generator = polymorphicGen closedTable root size
                    -- Each plain term has one typed term.
                    (root, size, length typed) `shouldBe` (root, size, length listed)
                    if null listed
                        then (root, size, Gen.cardinality generator) `shouldBe` (root, size, Left Gen.EmptyGenerator)
                        else do
                            (root, size, Gen.cardinality generator) `shouldBe` (root, size, Right (Cardinality (fromIntegral (length listed))))
                            (root, size, fmap sort (Gen.values generator)) `shouldBe` (root, size, Right (sort listed))
                )
                cells
            let large = [(root, size) | (root, size) <- cells, length (polymorphicTerms closedTable root size) > 20]
            length [() | (root, size) <- cells, null (polymorphicTerms closedTable root size)] `shouldSatisfy` (> 0)
            length large `shouldSatisfy` (> 0)
            mapM_
                ( \(root, size) -> do
                    let generator = polymorphicGen closedTable root size
                        typed = Equality.terms (polymorphicSpace closedTable root size)
                    mapM_
                        (\rank -> (root, size, Gen.termAt generator rank >>= Gen.rankOf generator) `shouldBe` (root, size, Right rank))
                        (everyRank (Cardinality (fromIntegral (length typed))))
                    mapM_
                        ( \term -> (root, size, Gen.rankOfTerm generator term >>= Gen.unrank generator) `shouldBe` (root, size, Right (plainTerm term))
                        )
                        typed
                )
                large

        it "lists a term with an open sort once, and the generator refuses to count its space" $ do
            openFunctions table1 `shouldBe` ["nil"]
            polymorphicTerms table1 int 2 `shouldBe` [Node "length" [nil]]
            Gen.cardinality (polymorphicGen table1 int 2) `shouldBe` Left Gen.CannotCountConstrainedEdges

        it "removes the sort children by position, for any function names" $ do
            let named =
                    PolymorphicSignature
                        [SortedFunction "root" [] int, SortedFunction "Int" [int] int, SortedFunction "List" [a] (list a)]
            polymorphicTerms named int 1 `shouldBe` [Node "root" []]
            polymorphicTerms named int 2 `shouldBe` [Node "Int" [Node "root" []]]
            polymorphicTerms named (list int) 2 `shouldBe` [Node "List" [Node "root" []]]
            polymorphicTerms named (list int) 3 `shouldBe` [Node "List" [Node "Int" [Node "root" []]]]
            polymorphicTerms named (list (list int)) 3 `shouldBe` [Node "List" [Node "List" [Node "root" []]]]

        it "makes the occurs check" $ do
            mapM_
                ( \size ->
                    mapM_
                        (\term -> (size, term, hasSort occursTable bool term) `shouldBe` (size, term, True))
                        (polymorphicTerms occursTable bool size)
                )
                [1 .. 4]
            polymorphicTerms occursTable bool 3 `shouldSatisfy` notElem (Node "same" [Node "dup" [nil]])
            polymorphicTerms occursTable bool 4 `shouldSatisfy` elem (Node "same" [Node "pair" [zero, nil]])

        it "makes the occurrences of a variable of the root sort equal" $
            Set.fromList (polymorphicTerms table2 (pair a a) 3)
                `shouldBe` Set.fromList [Node "pair" [zero, zero], Node "pair" [true, true], Node "pair" [nil, nil]]

        it "gives no term for a size below 1" $ do
            polymorphicSpace table1 int 0 `shouldBe` Equality.EmptyNode
            polymorphicTerms table1 int 0 `shouldBe` []

    describe "principalAutomaton" $ do
        mapM_
            ( \(name, signature, roots) ->
                it ("counts each term one time, as polymorphicTerms lists it, for " <> name) $
                    mapM_
                        ( \root -> do
                            automaton <- either (fail . show) pure (principalAutomaton 100000 signature root 6)
                            classes <- either (fail . show) pure (sized automaton)
                            mapM_
                                ( \size -> do
                                    let listed = polymorphicTerms signature root size
                                    (root, size, countOfSize classes (Size (fromIntegral size)))
                                        `shouldBe` (root, size, Cardinality (fromIntegral (length listed)))
                                    (root, size, Set.fromList (termsOfSize classes (Size (fromIntegral size))))
                                        `shouldBe` (root, size, Set.fromList listed)
                                )
                                [1 .. 6]
                        )
                        roots
            )
            [("table 1", table1, roots1 <> [a]), ("table 2", table2, roots2 <> [a])]

        it "counts length(nil) one time, where the generator of the equality automaton refuses to count" $ do
            automaton <- either (fail . show) pure (principalAutomaton 1000 table1 int 2)
            classes <- either (fail . show) pure (sized automaton)
            termsOfSize classes (Size 2) `shouldBe` [Node "length" [nil]]
            countOfSize classes (Size 2) `shouldBe` Cardinality 1
            Gen.cardinality (polymorphicGen table1 int 2) `shouldBe` Left Gen.CannotCountConstrainedEdges

        it "is a generator with distinct values and the rank round trip, in table 1 at the root Int" $ do
            automaton <- either (fail . show) pure (principalAutomaton 100000 table1 int 5)
            let generator = Gen.upToSize 5 (Gen.fromAutomaton (Interned.fromRows (FTA.initialState automaton) (FTA.transitionTable automaton)))
                expected = sum [length (polymorphicTerms table1 int size) | size <- [1 .. 5]]
                generated = either (error . show) id (Gen.values generator)
            expected `shouldSatisfy` (> 5)
            Gen.cardinality generator `shouldBe` Right (Cardinality (fromIntegral expected))
            length generated `shouldBe` expected
            Set.fromList generated `shouldBe` Set.fromList (concat [polymorphicTerms table1 int size | size <- [1 .. 5]])
            generated `shouldSatisfy` elem (Node "length" [nil])
            mapM_
                (\rank -> (Gen.unrank generator rank >>= Gen.rankOfTerm generator) `shouldBe` Right rank)
                (everyRank (Cardinality (fromIntegral expected)))

        it "accepts exactly the trees up to the bound that have an instance of the root sort, in table 1" $
            mapM_
                ( \root -> do
                    automaton <- either (fail . show) pure (principalAutomaton 100000 table1 root 5)
                    mapM_ (\tree -> (root, tree, FTA.accepts automaton tree) `shouldBe` (root, tree, hasSort table1 root tree)) smallTrees
                )
                (roots1 <> [a])

        it "is sound above the bound, and accepts some terms above the bound and not others" $ do
            automaton <- either (fail . show) pure (principalAutomaton 100000 table1 a 3)
            let larger = [tree | tree <- smallTrees, length tree >= 4]
            mapM_
                (\tree -> (tree, hasSort table1 a tree) `shouldBe` (tree, True))
                (filter (FTA.accepts automaton) smallTrees)
            filter (FTA.accepts automaton) larger `shouldSatisfy` (not . null)
            [tree | tree <- larger, hasSort table1 a tree, not (FTA.accepts automaton tree)] `shouldSatisfy` (not . null)
            -- The children of eq have the states Int and Int, of smallest size 1.
            FTA.accepts automaton (Node "eq" [Node "length" [nil], zero]) `shouldBe` True
            -- ite has three children, so its smallest sizes sum to 3, more than the bound minus 1.
            FTA.accepts automaton (Node "ite" [true, zero, zero]) `shouldBe` False

        it "has one state for each principal sort, at the bounds 21 and 3, 5, 7" $ do
            let states signature bound =
                    either (const (-1)) (\automaton -> length [() | Just _ <- Map.keys (FTA.transitionTable automaton)]) $
                        principalAutomaton 100000 signature a bound
            states table1 21 `shouldBe` (33 :: Int)
            map (states table2) [3, 5, 7] `shouldBe` [15, 99, 831]

        it "stops at the limit on the number of states, and checks the signature" $ do
            either Just (const Nothing) (principalAutomaton 100 table2 a 7) `shouldBe` Just (TooManySorts 100)
            principalAutomaton 831 table2 a 7 `shouldSatisfy` isRight
            either
                Just
                (const Nothing)
                ( principalAutomaton
                    100
                    (PolymorphicSignature (polymorphicFunctions table1 <> [SortedFunction "nil" [] (list int)]))
                    int
                    3
                )
                `shouldBe` Just (RepeatedSymbol "nil")
