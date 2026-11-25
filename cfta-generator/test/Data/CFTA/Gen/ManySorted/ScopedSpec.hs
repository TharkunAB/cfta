{- | Binders and variables in a run-time signature: counts against brute force
and against the typed arithmetic language of "Data.CFTA.Gen.Typing", closed
and well-typed terms, rank round trips, the type checker, and symbols with
instances.
-}
module Data.CFTA.Gen.ManySorted.ScopedSpec (spec) where

import Data.Either (isRight)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import Data.CFTA.Gen (Gen)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.ManySorted
import Data.CFTA.Gen.ManySorted.Scoped
import Data.CFTA.Gen.TypedArithmeticLanguage (Arith (..), ArithType (..), arithRules, arithType)
import Data.CFTA.Gen.Typing (Bound (..), Typing (Typing), fromTypingRules)
import Data.CFTA.Index (Cardinality (..), everyRank)
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term (Node))

data Sort = Int | Bool
    deriving (Eq, Ord, Show)

codec :: ScopedCodec Sort String
codec =
    ScopedCodec
        { variableSymbol = \index -> 'v' : show index
        , variableIndex = \case
            'v' : digits | [(n, "")] <- reads digits -> Just n
            _ -> Nothing
        , scopedValueCodec =
            Just
                ValueCodec
                    { injectInteger = \n -> '#' : show n
                    , projectInteger = \case
                        '#' : digits | [(n, "")] <- reads digits -> Just n
                        _ -> Nothing
                    , valueSymbol = \s -> '<' : show s <> ">"
                    }
        }

-- | The typed arithmetic language: literals 0 and 1, booleans, plus, less, if, and let.
arithmetic :: [Sort] -> Int -> ScopedSignature Sort String
arithmetic inputs bound =
    ScopedSignature
        { scopedBase =
            SortedSignature
                { sortedSorts = [Int, Bool]
                , sortedFunctions =
                    [ SortedFunction "plus" [Int, Int] Int
                    , SortedFunction "less" [Int, Int] Bool
                    , SortedFunction "ifInt" [Bool, Int, Int] Int
                    , SortedFunction "ifBool" [Bool, Bool, Bool] Bool
                    ]
                        <> [SortedFunction (letName rhs result) [rhs, result] result | rhs <- [Int, Bool], result <- [Int, Bool]]
                , sortedRoots = [Int, Bool]
                , sortedValues = [ValueSort Int (Interval 0 1), ValueSort Bool (Pool ["false", "true"])]
                }
        , scopedBinders = [Binding (letName rhs result) [[], [rhs]] | rhs <- [Int, Bool], result <- [Int, Bool]]
        , scopedInputs = inputs
        , scopedBound = bound
        }

letName :: Sort -> Sort -> String
letName rhs result = "let" <> show rhs <> show result

generator :: Int -> ScopedSignature Sort String -> Gen String (Term String)
generator size scoped = either (error . show) (Gen.upToSize (fromIntegral size)) (scopedGen codec scoped)

members :: Gen String (Term String) -> [Term String]
members = either (error . show) id . Gen.values

-- | Every term of a sort in an environment with exactly the given number of nodes.
bruteForce :: ScopedSignature Sort String -> [Sort] -> Sort -> Int -> [Term String]
bruteForce scoped = terms
  where
    base = scopedBase scoped
    scopes = Map.fromList [(bindingSymbol b, bindingScopes b) | b <- scopedBinders scoped]
    terms env sort' size =
        [Node value [] | size == 1, ValueSort s source <- sortedValues base, s == sort', value <- valuesOf source]
            <> [Node ('v' : show index) [] | size == 1, (index, s) <- zip [0 :: Int ..] env, s == sort']
            <> [ Node (functionSymbol f) children
               | f <- sortedFunctions base
               , functionResult f == sort'
               , let childEnvs = [binds <> env | binds <- fromMaybe (map (const []) (functionArguments f)) (Map.lookup (functionSymbol f) scopes)]
               , all (\childEnv -> length childEnv - length (scopedInputs scoped) <= scopedBound scoped) childEnvs
               , children <- arguments (zip childEnvs (functionArguments f)) (size - 1)
               ]
    arguments [] 0 = [[]]
    arguments [] _ = []
    arguments ((childEnv, argument) : rest) budget =
        [ first : others
        | firstSize <- [1 .. budget]
        , first <- terms childEnv argument firstSize
        , others <- arguments rest (budget - firstSize)
        ]
    valuesOf (Interval low high) = ['#' : show n | n <- [low .. high]]
    valuesOf (Pool symbols) = symbols

exact :: ScopedSignature Sort String -> Int -> [Term String]
exact scoped size = concat [bruteForce scoped (scopedInputs scoped) root size | root <- sortedRoots (scopedBase scoped)]

-- | The distinct terms of the root sorts with exactly the given number of nodes, in order.
distinctTerms :: ScopedSignature Sort String -> Int -> [Term String]
distinctTerms scoped size = Set.toList (Set.fromList (exact scoped size))

-- | zero, true, eq at Int and at Bool, and let with an Int variable in a body of either sort.
instanced :: [Sort] -> Int -> ScopedSignature Sort String
instanced inputs bound =
    ScopedSignature
        { scopedBase =
            SortedSignature
                { sortedSorts = [Int, Bool]
                , sortedFunctions =
                    [SortedFunction "zero" [] Int, SortedFunction "true" [] Bool]
                        <> [SortedFunction "eq" [s, s] Bool | s <- [Int, Bool]]
                        <> [SortedFunction "let" [Int, s] s | s <- [Int, Bool]]
                , sortedRoots = [Int, Bool]
                , sortedValues = []
                }
        , scopedBinders = [Binding "let" [[], [Int]]]
        , scopedInputs = inputs
        , scopedBound = bound
        }

allTerms :: ScopedSignature Sort String -> Int -> [Term String]
allTerms scoped size =
    concat [bruteForce scoped (scopedInputs scoped) root n | n <- [1 .. size], root <- sortedRoots (scopedBase scoped)]

-- | The closed typed arithmetic terms with at most the binders, from the typing rules.
arithBinders :: Int -> Gen Symbol Arith
arithBinders bound = either (error . show) id $ fromTypingRules (Typing (Binders bound) [] [IntType, BoolType] arithRules)

-- | Whether every variable of a term is bound, and whether its sorts agree, by an independent walk.
closed :: ScopedSignature Sort String -> Term String -> Bool
closed scoped = go (length (scopedInputs scoped))
  where
    scopes = Map.fromList [(bindingSymbol b, map length (bindingScopes b)) | b <- scopedBinders scoped]
    go depth (Node ('v' : digits) []) | [(n, "")] <- reads digits = n < depth
    go depth (Node symbol children) =
        and
            [ go (depth + extra) child
            | (extra, child) <- zip (Map.findWithDefault (repeat 0) symbol scopes) children
            ]

-- | A term of the typed arithmetic language as a term of the signature.
toTerm :: [ArithType] -> Arith -> Term String
toTerm env arith = case arith of
    Num n -> Node ('#' : show n) []
    Flag b -> Node (if b then "true" else "false") []
    Var index -> Node ('v' : show index) []
    Arg index -> Node ('v' : show (length env + index)) []
    Plus left right -> Node "plus" [toTerm env left, toTerm env right]
    Less left right -> Node "less" [toTerm env left, toTerm env right]
    If condition yes no -> Node (if typeOf env yes == IntType then "ifInt" else "ifBool") [toTerm env condition, toTerm env yes, toTerm env no]
    Let rhs body ->
        let rhsType = typeOf env rhs
         in Node (letName (sortOf rhsType) (sortOf (typeOf (rhsType : env) body))) [toTerm env rhs, toTerm (rhsType : env) body]
  where
    typeOf e = fromMaybe (error "ill-typed") . arithType e
    sortOf IntType = Int
    sortOf BoolType = Bool

spec :: Spec
spec = describe "Data.CFTA.Gen.ManySorted.Scoped" $ do
    let maxSize = 6
    mapM_
        ( \bound -> do
            let scoped = arithmetic [] bound
                gen = generator maxSize scoped
                generated = members gen
            describe ("a bound of " <> show bound <> " binders") $ do
                it "counts as a brute-force enumeration does" $
                    mapM_
                        ( \size ->
                            Gen.countAtSize gen (fromIntegral size)
                                `shouldBe` Right (Cardinality (fromIntegral (length (exact scoped size))))
                        )
                        [1 .. maxSize]
                it "generates the brute-force terms, smaller terms first" $ do
                    sort generated `shouldBe` sort (allTerms scoped maxSize)
                    let sizes = map length generated
                    sizes `shouldBe` sort sizes
                it "generates closed, well-typed terms" $
                    mapM_
                        ( \term -> do
                            term `shouldSatisfy` closed scoped
                            scopedTypeCheck codec scoped term `shouldSatisfy` either (const False) (`elem` [Int, Bool])
                        )
                        generated
                it "ranks every generated term back" $
                    mapM_
                        (\rank -> (Gen.unrank gen rank >>= Gen.rankOfTerm gen) `shouldBe` Right rank)
                        (everyRank (Cardinality (fromIntegral (length generated))))
                it "is the language of Data.CFTA.Gen.Typing with the same rules" $ do
                    let listed = either (error . show) id (Gen.values (Gen.upToSize (2 * fromIntegral maxSize) (arithBinders bound)))
                        mapped = [term | arith <- listed, let term = toTerm [] arith, length term <= maxSize]
                    sort mapped `shouldBe` sort generated
        )
        [0, 1, 2]

    describe "inputs" $ do
        it "are variables that are not binders" $ do
            let scoped = arithmetic [Int, Bool] 1
                gen = generator 5 scoped
            sort (members gen) `shouldBe` sort (allTerms scoped 5)
            members gen `shouldSatisfy` elem (Node "v1" [])
            members gen `shouldSatisfy` all (closed scoped)

    describe "scopedTypeCheck" $ do
        let scoped = arithmetic [] 1
        it "accepts exactly the generated terms among untyped terms" $ do
            let symbols = ["plus", "less", "ifInt", "ifBool", "letIntInt", "letBoolInt", "v0", "v1", "v2", "#0", "#2", "true", "foo"]
                untyped = concatMap (untypedTerms symbols) [1 .. 4]
                listed = Set.fromList (members (generator 4 scoped))
            length untyped `shouldSatisfy` (> 1000)
            mapM_
                ( \term ->
                    (term, either (const False) (const True) (scopedTypeCheck codec scoped term)) `shouldBe` (term, Set.member term listed)
                )
                untyped
        it "reports a variable that no binder holds, with its path" $
            scopedTypeCheck codec scoped (Node "plus" [Node "#0" [], Node "v0" []])
                `shouldBe` Left (UnboundVariable (path [ChildIndex 1]) 0 0)
        it "reports a variable of a sort the place does not accept" $
            scopedTypeCheck codec scoped (Node "letBoolInt" [Node "true" [], Node "plus" [Node "v0" [], Node "#1" []]])
                `shouldBe` Left (WrongChildSort (path [ChildIndex 1]) "plus" [Int, Int] [Just Bool, Just Int])
        it "reports binders over the bound" $
            scopedTypeCheck codec scoped (Node "letIntInt" [Node "#0" [], Node "letIntInt" [Node "#1" [], Node "v1" []]])
                `shouldBe` Left (TooManyBinders (path [ChildIndex 1]) "letIntInt")
        it "accepts a variable under a binder" $
            scopedTypeCheck codec scoped (Node "letIntInt" [Node "#0" [], Node "plus" [Node "v0" [], Node "#1" []]])
                `shouldBe` Right Int

    describe "scopedAutomaton" $ do
        it "reports an invalid signature" $ do
            let failure = either Just (const Nothing) . scopedAutomaton codec
                valid = arithmetic [] 1
            failure valid{scopedBound = -1} `shouldBe` Just (NegativeBound (-1))
            failure valid{scopedBinders = Binding "nothing" [] : scopedBinders valid}
                `shouldBe` Just (BindingOfUnknownFunction "nothing")
            failure valid{scopedBinders = Binding "letIntInt" [[]] : scopedBinders valid}
                `shouldBe` Just (DuplicateBinding "letIntInt")
            failure valid{scopedBinders = [Binding "letIntInt" [[]]]} `shouldBe` Just (BindingArity "letIntInt")
            failure valid{scopedInputs = [Int, Int]} `shouldBe` Nothing
            failure
                valid
                    { scopedBase = (scopedBase valid){sortedFunctions = SortedFunction "v7" [] Int : sortedFunctions (scopedBase valid)}
                    }
                `shouldBe` Just (VariableSymbolClash "v7")

    describe "instances of a symbol" $ do
        let withValues =
                let scoped = instanced [Bool] 1
                 in scoped{scopedBase = (scopedBase scoped){sortedValues = [ValueSort Int (Interval 1 2), ValueSort Bool (Pool ["false"])]}}
        mapM_
            ( \(name, scoped) -> do
                let gen = generator maxSize scoped
                    generated = members gen
                it ("counts and generates the distinct brute-force terms, " <> name) $ do
                    mapM_
                        ( \size ->
                            Gen.countAtSize gen (fromIntegral size)
                                `shouldBe` Right (Cardinality (fromIntegral (length (distinctTerms scoped size))))
                        )
                        [1 .. maxSize]
                    length generated `shouldSatisfy` (> 50)
                    sort generated `shouldBe` sort (concatMap (distinctTerms scoped) [1 .. maxSize])
                    Set.size (Set.fromList generated) `shouldBe` length generated
                    mapM_ (\term -> scopedTypeCheck codec scoped term `shouldSatisfy` isRight) generated
                it ("ranks every generated term back, " <> name) $
                    mapM_
                        (\rank -> (Gen.unrank gen rank >>= Gen.rankOfTerm gen) `shouldBe` Right rank)
                        (everyRank (Cardinality (fromIntegral (length generated))))
            )
            [("without value sorts", instanced [Bool] 2), ("with value sorts", withValues)]

        it "type checks exactly the terms that the automaton accepts, among untyped terms" $ do
            let scoped = instanced [Bool] 1
                untyped = concatMap (untypedTerms ["zero", "true", "eq", "let", "v0", "v1", "v2", "foo"]) [1 .. 4]
            automaton <- either (fail . show) pure $ scopedAutomaton codec scoped
            length untyped `shouldSatisfy` (> 10000)
            mapM_
                (\term -> (term, isRight (scopedTypeCheck codec scoped term)) `shouldBe` (term, FTA.accepts automaton term))
                untyped
            sort (filter (isRight . scopedTypeCheck codec scoped) untyped) `shouldBe` Set.toList (Set.fromList (allTerms scoped 4))

        it "gives eq of one variable the sort Bool, with the variable of either sort" $ do
            scopedTypeCheck codec (instanced [Int] 0) (Node "eq" [Node "v0" [], Node "v0" []]) `shouldBe` Right Bool
            scopedTypeCheck codec (instanced [Bool] 0) (Node "eq" [Node "v0" [], Node "v0" []]) `shouldBe` Right Bool
            scopedTypeCheck codec (instanced [Bool] 1) (Node "let" [Node "zero" [], Node "eq" [Node "v0" [], Node "v0" []]])
                `shouldBe` Right Bool

        it "rejects eq of two variables of different sorts" $
            scopedTypeCheck codec (instanced [Int, Bool] 0) (Node "eq" [Node "v0" [], Node "v1" []])
                `shouldBe` Left (NoInstance (path []) "eq" [[Int, Int], [Bool, Bool]] [Just Int, Just Bool])

        it "gives let the sort of its body" $ do
            let scoped = instanced [] 1
            scopedTypeCheck codec scoped (Node "let" [Node "zero" [], Node "v0" []]) `shouldBe` Right Int
            scopedTypeCheck codec scoped (Node "let" [Node "zero" [], Node "true" []]) `shouldBe` Right Bool
            scopedTypeCheck codec scoped (Node "let" [Node "zero" [], Node "eq" [Node "v0" [], Node "zero" []]])
                `shouldBe` Right Bool

        it "checks the arity, then the bound, then the instances, then the children" $ do
            scopedTypeCheck codec (instanced [] 0) (Node "let" [Node "zero" []]) `shouldBe` Left (WrongArity (path []) "let" 2 1)
            scopedTypeCheck codec (instanced [] 0) (Node "let" [Node "true" [], Node "zero" []])
                `shouldBe` Left (TooManyBinders (path []) "let")
            scopedTypeCheck codec (instanced [] 1) (Node "let" [Node "true" [], Node "zero" []])
                `shouldBe` Left (NoInstance (path []) "let" [[Int, Int], [Int, Bool]] [Just Bool, Just Int])
            scopedTypeCheck codec (instanced [] 1) (Node "let" [Node "zero" [], Node "eq" [Node "v0" [], Node "true" []]])
                `shouldBe` Left (NoInstance (path [ChildIndex 1]) "eq" [[Int, Int], [Bool, Bool]] [Just Int, Just Bool])

-- | Every term with the given number of nodes, over some symbols, with any arity from zero to three.
untypedTerms :: [String] -> Int -> [Term String]
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
