{- | Typed languages from a signature that is data at run time.

"Data.CFTA.Gen.Typing" builds a typed language from a Haskell datatype that
is known at compile time. This module takes a first-order many-sorted
signature as a plain value instead: the sorts, the function symbols with
their argument sorts and result sort, and the root sorts. A constant is a
function symbol with no argument sorts. A symbol can have several functions.
Each of these functions is an instance of the symbol. See
Note [Instances of a symbol] for the rule on instances.

'signatureAutomaton' reads the signature as a tree automaton. Its states are
the sorts and its transitions are the functions. So the operations of
"Data.CFTA" and "Data.CFTA.Template" apply to it. 'signatureGen' reads the
same automaton as a generator of terms, as 'Data.CFTA.Gen.fromAutomaton'
does. Apply 'Data.CFTA.Gen.upToSize' to the generator to get size-major
ranks, and use 'Data.CFTA.Gen.rankOfTerm' and 'Data.CFTA.Gen.unrank' to
convert between a rank and a term. 'typeCheck' tests whether a term is a term
of the signature.

The word "signature" here has the meaning it has in universal algebra. It is
not 'Data.CFTA.Gen.Sig.Sig', which is a type-level signature of join keys.
It is also not 'Data.CFTA.Formula.Sort', which is a sort of a formula.

@
data Sort = Int | Bool deriving (Eq, Ord, Show)

arithmetic :: SortedSignature Sort String
arithmetic =
    SortedSignature
        { sortedSorts = [Int, Bool]
        , sortedFunctions =
            [ SortedFunction "zero" [] Int
            , SortedFunction "add" [Int, Int] Int
            , SortedFunction "lt" [Int, Int] Bool
            , SortedFunction "ite" [Bool, Int, Int] Int
            ]
        , sortedRoots = [Int]
        }
@
-}
module Data.CFTA.Gen.ManySorted (
    SortedSignature (..),
    SortedFunction (..),
    ValueSort (..),
    ValueSource (..),
    ValueCodec (..),
    SignatureError (..),
    signatureAutomaton,
    signatureAutomatonWith,
    signatureGen,
    signatureGenWith,
    TypeError (..),
    typeCheck,
    typeCheckWith,
    SortingError (..),
    checkSorts,
    checkSortsWith,

    -- * For modules that extend signatures
    checkSignatureWith,
    instancesOf,
    valueLeaves,
    valueSortOf,
) where

import qualified Data.Array as Array
import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable)
import Data.List (find, tails)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Gen (Gen, LeafSource (..))
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (Cardinality (..), Rank (..))
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (ChildIndex (..), Path, path)
import Data.CFTA.Signature (
    SortedFunction (..),
    SortedSignature (..),
    ValueSort (..),
    ValueSource (..),
 )
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

{- | How the values of the sorts of a signature are symbols.

The functions must agree: @projectInteger (injectInteger n) == Just n@, and
@projectInteger@ gives 'Nothing' for a symbol that is not an integer.
-}
data ValueCodec sort symbol = ValueCodec
    { injectInteger :: Integer -> symbol
    -- ^ The symbol of an integer of an 'Interval'.
    , projectInteger :: symbol -> Maybe Integer
    -- ^ The integer of a symbol, if it has one.
    , valueSymbol :: sort -> symbol
    {- ^ A symbol that stands for the values of a sort in the automaton. It
    is not a term. It must differ from every function symbol, every value,
    and the symbol of every other sort.
    -}
    }

-- | A reason why a signature is not valid.
data SignatureError sort symbol
    = -- | A function or a root names a sort that is not in the signature.
      UnknownSort !sort
    | {- | Two functions of this symbol have the same argument sorts or a
      different number of arguments, or two values have this symbol, or a
      function and a value have this symbol. See Note [Instances of a symbol].
      -}
      DuplicateSymbol !symbol
    | -- | A sort is in two value sorts.
      DuplicateValueSort !sort
    | -- | A value sort has no value.
      EmptyValueSource !sort
    | -- | The signature has value sorts, and no codec was given.
      ValueSortsNeedCodec
    | {- | The automaton check rejected the signature. The checks of this
      module find every such case first, so this error is not expected.
      -}
      AutomatonRejected !(FTA.FTAError (Maybe sort))
    deriving (Eq, Show)

{- | The automaton of a signature, for the operations of "Data.CFTA".

A state is a sort, as 'Just' of the sort. The initial state is 'Nothing'. It
has the transitions of all root sorts. Each function is one transition, from
its result sort. A term has at most one sort, so it has at most one run. See
Note [Instances of a symbol].

The signature must have no value sort. Use 'signatureAutomatonWith' for a
signature with value sorts.
-}
signatureAutomaton ::
    (Ord sort, Ord symbol) =>
    SortedSignature sort symbol ->
    Either (SignatureError sort symbol) (FTA.FTA (Maybe sort) symbol Constraint)
signatureAutomaton signature
    | null (sortedValues signature) = automatonOf Nothing signature
    | otherwise = Left ValueSortsNeedCodec

{- | The automaton of a signature with value sorts.

A value sort has one more transition with no child, from its state. Its symbol
is 'valueSymbol' of the sort, and it stands for all values of the sort. So the
automaton stays small. It accepts the symbol and not the values. Read the
values through 'signatureGenWith'.
-}
signatureAutomatonWith ::
    (Ord sort, Ord symbol) =>
    ValueCodec sort symbol ->
    SortedSignature sort symbol ->
    Either (SignatureError sort symbol) (FTA.FTA (Maybe sort) symbol Constraint)
signatureAutomatonWith codec = automatonOf (Just codec)

automatonOf ::
    (Ord sort, Ord symbol) =>
    Maybe (ValueCodec sort symbol) ->
    SortedSignature sort symbol ->
    Either (SignatureError sort symbol) (FTA.FTA (Maybe sort) symbol Constraint)
automatonOf codec signature = do
    checkSignatureWith codec signature
    let transitions =
            [ (functionResult function, FTA.Transition (functionSymbol function) (map Just (functionArguments function)) noConstraint)
            | function <- sortedFunctions signature
            ]
                <> [ (valueSort value, FTA.Transition (valueSymbol codec' (valueSort value)) [] noConstraint)
                   | Just codec' <- [codec]
                   , value <- sortedValues signature
                   ]
        rows = Map.fromListWith (flip (<>)) [(Just sort, [transition]) | (sort, transition) <- transitions]
        sortRows = [(Just sort, Map.findWithDefault [] (Just sort) rows) | sort <- nubOrd (sortedSorts signature)]
        rootRow = concat [Map.findWithDefault [] (Just root) rows | root <- nubOrd (sortedRoots signature)]
    either (Left . AutomatonRejected) Right $ FTA.mkFTA Nothing ((Nothing, rootRow) : sortRows)

{- | The terms of a signature as a generator.

The generator is the one that 'Data.CFTA.Gen.fromAutomaton' gives for
'signatureAutomaton'. It is recursive when a sort is, so apply
'Data.CFTA.Gen.upToSize' before the queries of "Data.CFTA.Gen".

The signature must have no value sort. Use 'signatureGenWith' for a signature
with value sorts.
-}
signatureGen ::
    (Ord sort, Ord symbol, Hashable symbol, Typeable symbol) =>
    SortedSignature sort symbol ->
    Either (SignatureError sort symbol) (Gen symbol (Term symbol))
signatureGen signature = do
    automaton <- signatureAutomaton signature
    pure $ Gen.fromAutomaton $ Interned.fromRows (FTA.initialState automaton) (FTA.transitionTable automaton)

{- | The terms of a signature with value sorts as a generator.

The generator is 'Data.CFTA.Gen.fromAutomatonWithLeaves' for
'signatureAutomatonWith'. The leaves of a value sort are its values, each of
size one. They are not listed, so the cost of a count, of 'Data.CFTA.Gen.unrank',
and of 'Data.CFTA.Gen.rankOfTerm' does not depend on the number of values. The
ranks order the leaves of a sort by the integer of an 'Interval', or by the
order of a 'Pool'. In the order of a node, the leaves come with the other
symbols of no child, by the symbol 'valueSymbol'.

Apply 'Data.CFTA.Gen.upToSize' before the queries of "Data.CFTA.Gen". The
generator is always counted by size, also when the signature has no recursion.
'Data.CFTA.Gen.support' and 'Data.CFTA.Gen.inspect' show the symbol
'valueSymbol' in the place of the values.
-}
signatureGenWith ::
    (Ord sort, Ord symbol, Hashable symbol, Typeable symbol) =>
    ValueCodec sort symbol ->
    SortedSignature sort symbol ->
    Either (SignatureError sort symbol) (Gen symbol (Term symbol))
signatureGenWith codec signature = do
    automaton <- signatureAutomatonWith codec signature
    let leaves =
            Map.fromList
                [(valueSymbol codec (valueSort value), leafSourceOf codec (valueSource value)) | value <- sortedValues signature]
    pure
        $ Gen.fromAutomatonWithLeaves leaves
        $ Interned.fromRows (FTA.initialState automaton) (FTA.transitionTable automaton)

{- | The leaf sources of the value sorts of a signature, by the symbol
'valueSymbol' of the sort.
-}
valueLeaves ::
    (Ord symbol) => ValueCodec sort symbol -> SortedSignature sort symbol -> Map.Map symbol (LeafSource symbol)
valueLeaves codec signature =
    Map.fromList
        [(valueSymbol codec (valueSort value), leafSourceOf codec (valueSource value)) | value <- sortedValues signature]

-- | The value sort that holds a symbol, if any.
valueSortOf :: (Ord symbol) => ValueCodec sort symbol -> SortedSignature sort symbol -> symbol -> Maybe sort
valueSortOf codec signature symbol =
    valueSort <$> find (\value -> holds codec (valueSource value) symbol) (sortedValues signature)

-- | The leaves of a value source, with the inverse of their ranks.
leafSourceOf :: (Ord symbol) => ValueCodec sort symbol -> ValueSource symbol -> LeafSource symbol
leafSourceOf codec (Interval low high) =
    LeafSource
        { leafCount = Cardinality (high - low + 1)
        , leafTerm = \(Rank rank) -> Term.Node (injectInteger codec (low + rank)) []
        , leafRank = \case
            Term.Node symbol [] | Just n <- projectInteger codec symbol, low <= n, n <= high -> Just (Rank (n - low))
            _ -> Nothing
        }
leafSourceOf _ (Pool symbols) =
    LeafSource
        { leafCount = Cardinality (fromIntegral count)
        , leafTerm = \(Rank rank) -> Term.Node (members Array.! fromInteger rank) []
        , leafRank = \case
            Term.Node symbol [] -> Rank . toInteger <$> Map.lookup symbol positions
            _ -> Nothing
        }
  where
    count = length symbols
    members = Array.listArray (0, count - 1) symbols
    positions = Map.fromList (zip symbols [0 :: Int ..])

-- | Whether a value source holds a symbol.
holds :: (Ord symbol) => ValueCodec sort symbol -> ValueSource symbol -> symbol -> Bool
holds codec (Interval low high) symbol = maybe False (\n -> low <= n && n <= high) (projectInteger codec symbol)
holds _ (Pool symbols) symbol = symbol `elem` symbols

{- Note [Instances of a symbol]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A symbol can have several functions in a signature. Each of these functions
is an instance of the symbol. For example, @eq : Int, Int -> Bool@ and
@eq : Bool, Bool -> Bool@ are two instances of @eq@.

The rule: the functions of a symbol have the same number of arguments, and no
two of them have the same argument sorts. 'checkSignatureWith' refuses a
signature that breaks the rule with 'DuplicateSymbol'.

With the rule, a term has at most one sort. The proof is by induction on the
term. A value has one sort, because two value sorts share no value and a value
is not a function symbol. At a node, suppose that each child has at most one
sort. Then the sorts of the children decide the instance: at most one function
of the symbol has these sorts as its argument sorts. So the node has at most
one sort.

Then 'signatureAutomaton' has at most one run for each term. The states of
two sorts accept no common term, because a term has at most one sort. So
'Data.CFTA.Gen.fromAutomaton' does not find the automaton ambiguous. The
generator then gives each term one rank, and its counts are the numbers of
distinct terms.

The rule refuses a constant at two sorts, for example @nil : List Int@ and
@nil : List Bool@. The two constants have the same argument sorts: none. So
the term @nil@ would have two sorts and two runs, and a count would count it
two times.

All the functions of a symbol have one number of arguments. So 'WrongArity'
gives one number of arguments for the symbol.
-}

{- | Find the first unknown sort, the first symbol that breaks the rule of
Note [Instances of a symbol], or the first value problem.
-}
checkSignatureWith ::
    (Ord sort, Ord symbol) =>
    Maybe (ValueCodec sort symbol) -> SortedSignature sort symbol -> Either (SignatureError sort symbol) ()
checkSignatureWith codec signature = do
    case find (`notElem` sortedSorts signature) used of
        Just sort -> Left $ UnknownSort sort
        Nothing -> Right ()
    case [symbol | (symbol, functions) <- Map.toList (instancesOf signature), clash (map functionArguments functions)] of
        symbol : _ -> Left $ DuplicateSymbol symbol
        [] -> Right ()
    case codec of
        Nothing -> Right ()
        Just codec' -> checkValues codec' signature
  where
    used =
        concat [functionResult function : functionArguments function | function <- sortedFunctions signature]
            <> sortedRoots signature
            <> map valueSort (sortedValues signature)
    -- The same argument sorts two times, or two numbers of arguments.
    clash arguments = length (nubOrd arguments) /= length arguments || length (nubOrd (map length arguments)) /= 1

-- | The functions of each symbol, in the order of the signature.
instancesOf :: (Ord symbol) => SortedSignature sort symbol -> Map.Map symbol [SortedFunction sort symbol]
instancesOf signature = Map.fromListWith (flip (<>)) [(functionSymbol function, [function]) | function <- sortedFunctions signature]

duplicates :: (Ord a) => [a] -> [a]
duplicates symbols = Map.keys $ Map.filter (> (1 :: Int)) $ Map.fromListWith (+) [(symbol, 1) | symbol <- symbols]

-- | Check that every value, and every symbol of a value sort, has one meaning.
checkValues ::
    (Ord sort, Ord symbol) =>
    ValueCodec sort symbol -> SortedSignature sort symbol -> Either (SignatureError sort symbol) ()
checkValues codec signature = do
    case duplicates (map valueSort values) of
        sort : _ -> Left $ DuplicateValueSort sort
        [] -> Right ()
    case [valueSort value | value <- values, emptySource (valueSource value)] of
        sort : _ -> Left $ EmptyValueSource sort
        [] -> Right ()
    case duplicates (functionSymbols <> placeholders <> concat [symbols | ValueSort _ (Pool symbols) <- values]) of
        symbol : _ -> Left $ DuplicateSymbol symbol
        [] -> Right ()
    -- A function symbol and a value must differ.
    case [symbol | symbol <- functionSymbols, value <- values, holds codec (valueSource value) symbol] of
        symbol : _ -> Left $ DuplicateSymbol symbol
        [] -> Right ()
    -- Two value sorts must not share a value.
    case mapMaybe shared (pairs values) of
        symbol : _ -> Left $ DuplicateSymbol symbol
        [] -> Right ()
  where
    values = sortedValues signature
    -- The instances of a symbol share the symbol, so each symbol occurs once here.
    functionSymbols = nubOrd (map functionSymbol (sortedFunctions signature))
    placeholders = [valueSymbol codec (valueSort value) | value <- values]
    pairs xs = [(x, y) | x : rest <- tails xs, y <- rest]
    emptySource (Interval low high) = high < low
    emptySource (Pool symbols) = null symbols
    shared (ValueSort _ left, ValueSort _ right) = case (left, right) of
        (Interval l1 h1, Interval l2 h2) | max l1 l2 <= min h1 h2 -> Just (injectInteger codec (max l1 l2))
        (Pool symbols, other) -> find (holds codec other) symbols
        (other, Pool symbols) -> find (holds codec other) symbols
        _ -> Nothing

{- | The first node of a term, in preorder, that is not well-typed.

Each error has the 'Path' of the node.
-}
data TypeError sort symbol
    = -- | The symbol is not a function of the signature.
      UnknownFunction !Path !symbol
    | -- | The node has a different number of children than its function has arguments.
      WrongArity
        !Path
        !symbol
        -- | The number of arguments of the function.
        !Int
        -- | The number of children of the node.
        !Int
    | {- | The symbol has one function, and a child has a sort that differs
      from the argument sort of the function.
      -}
      WrongChildSort
        !Path
        !symbol
        -- | The argument sorts of the function.
        [sort]
        -- | The sorts of the children, from left to right. A child that is not well-typed has no sort.
        [Maybe sort]
    | {- | The symbol has several instances, and the sorts of the children fit
      no instance. An instance fits when each child with a sort has the
      argument sort of the instance at its position. See
      Note [Instances of a symbol].
      -}
      NoInstance
        !Path
        !symbol
        -- | The argument sorts of each instance, in the order of the signature.
        [[sort]]
        -- | The sorts of the children, from left to right. A child that is not well-typed has no sort.
        [Maybe sort]
    | -- | The term is well-typed at the root, but its sort is not a root sort.
      NotRootSort !sort
    | {- | A variable has an index that no binder or input holds. The fields
      are the path, the index, and the number of variables in scope.
      -}
      UnboundVariable !Path !Int !Int
    | {- | The binders of a child would exceed the bound on the binders of
      the signature.
      -}
      TooManyBinders !Path !symbol
    deriving (Eq, Show)

{- | Check that a term is a term of the signature, and find its sort.

A node is not well-typed if its symbol is unknown, if it has the wrong number
of children, or if the sorts of its well-typed children fit no function of the
symbol. A function fits when each well-typed child has the argument sort of the
function at its position. The error names the first such node in preorder. A
child that is not well-typed has no sort, so its parent is not in error for
that child. The error then names the node in that child.

For a symbol with one function, the error at the node is 'WrongChildSort'.
For a symbol with several instances, it is 'NoInstance'. The sorts of the
children decide the instance. See Note [Instances of a symbol].

The sort of the term must be a root sort. Then 'typeCheck' accepts exactly the
terms that 'signatureAutomaton' accepts.

The signature must have no value sort. Use 'typeCheckWith' for a signature with
value sorts.
-}
typeCheck ::
    (Ord sort, Ord symbol) =>
    SortedSignature sort symbol ->
    Term symbol ->
    Either (TypeError sort symbol) sort
typeCheck signature = checkWith (const Nothing) signature

{- | 'typeCheck' for a signature with value sorts.

A leaf is a value of a sort if the value source of the sort holds its symbol.
A symbol of a function is never a value. A leaf with a symbol outside every
value source and every function is an 'UnknownFunction'. The accepted terms
are the terms of 'signatureGenWith'.
-}
typeCheckWith ::
    (Ord sort, Ord symbol) =>
    ValueCodec sort symbol ->
    SortedSignature sort symbol ->
    Term symbol ->
    Either (TypeError sort symbol) sort
typeCheckWith codec signature = checkWith valueOf signature
  where
    valueOf = valueSortOf codec signature

checkWith ::
    (Ord sort, Ord symbol) =>
    (symbol -> Maybe sort) ->
    SortedSignature sort symbol ->
    Term symbol ->
    Either (TypeError sort symbol) sort
checkWith valueOf signature term0 = check [] term0 >>= rootSort
  where
    rootSort sort'
        | sort' `elem` sortedRoots signature = Right sort'
        | otherwise = Left $ NotRootSort sort'

    functions = instancesOf signature

    -- The instances of a symbol have one number of arguments, so the first
    -- instance gives it. See Note [Instances of a symbol].
    check reversed term = case Map.findWithDefault [] symbol functions of
        [] -> case valueOf symbol of
            Just sort'
                | null children -> Right sort'
                | otherwise -> Left $ WrongArity here symbol 0 (length children)
            Nothing -> Left $ UnknownFunction here symbol
        instances@(function : _)
            | arity /= length children -> Left $ WrongArity here symbol arity (length children)
            | otherwise -> case filter fits instances of
                fitting : _ -> functionResult fitting <$ sequence results
                [] -> Left $ case instances of
                    [_] -> WrongChildSort here symbol (functionArguments function) found
                    _ -> NoInstance here symbol (map functionArguments instances) found
          where
            arity = length (functionArguments function)
            results = [check (index : reversed) subterm | (index, subterm) <- zip [0 ..] children]
            found = map (either (const Nothing) Just) results
            fits candidate = not (any mismatch (zip (functionArguments candidate) found))
      where
        symbol = Term.rootLabel term
        children = Term.subForest term
        here = path (map ChildIndex (reverse reversed))

    mismatch (sort, Just actual) = sort /= actual
    mismatch (_, Nothing) = False

-- | Why a map from the states of an automaton to sorts does not fit a signature.
data SortingError state sort symbol
    = -- | A state with transitions has no sort.
      UnsortedState !state
    | {- | A transition of a state fits no function of its symbol, from the
      sorts of its children to the sort of the state, and it is not a value of
      the sort of the state.
      -}
      IllSortedTransition
        !state
        !symbol
        -- | The sorts of the children, or 'Nothing' for a child without a sort.
        ![Maybe sort]
    deriving (Eq, Show)

{- | Check that a map from the states of an automaton to sorts fits a
signature. Each transition @f(q1, ..., qn)@ of a state @q@ must fit a function
of the symbol @f@: the function has the sorts of @q1, ..., qn@ as its argument
sorts and the sort of @q@ as its result sort. For a symbol with several
instances, one instance must fit. See Note [Instances of a symbol]. The map is
then a homomorphism from the automaton to 'signatureAutomaton' of the
signature, so each term of a state is a term of its sort. A state without
transitions needs no sort.

The symbols of the automaton must be the symbols of the signature. For an
automaton with refined symbols, check @'FTA.mapSymbols' unrefined@ of it.

The signature must have no value sort. Use 'checkSortsWith' for a signature
with value sorts.
-}
checkSorts ::
    (Ord state, Ord sort, Ord symbol) =>
    SortedSignature sort symbol ->
    Map.Map state sort ->
    FTA.FTA state symbol annotation ->
    Either (SortingError state sort symbol) ()
checkSorts = checkSortsOf (const Nothing)

-- | 'checkSorts' for a signature with value sorts: a leaf can also be a value of the sort of its state.
checkSortsWith ::
    (Ord state, Ord sort, Ord symbol) =>
    ValueCodec sort symbol ->
    SortedSignature sort symbol ->
    Map.Map state sort ->
    FTA.FTA state symbol annotation ->
    Either (SortingError state sort symbol) ()
checkSortsWith codec signature = checkSortsOf (valueSortOf codec signature) signature

-- | Check the sorts with the sort of the value of a leaf symbol, if it has one.
checkSortsOf ::
    (Ord state, Ord sort, Ord symbol) =>
    (symbol -> Maybe sort) ->
    SortedSignature sort symbol ->
    Map.Map state sort ->
    FTA.FTA state symbol annotation ->
    Either (SortingError state sort symbol) ()
checkSortsOf valueOf signature sorts automaton = mapM_ row $ Map.toList $ FTA.transitionTable automaton
  where
    functions = instancesOf signature
    row (_, []) = Right ()
    row (state, edges) = case Map.lookup state sorts of
        Nothing -> Left $ UnsortedState state
        Just sort -> mapM_ (edge state sort) edges
    -- See Note [Instances of a symbol].
    edge state sort transition
        | any fits (Map.findWithDefault [] symbol functions) = Right ()
        | null children, valueOf symbol == Just sort = Right ()
        | otherwise = Left $ IllSortedTransition state symbol childSorts
      where
        symbol = FTA.transitionSymbol transition
        children = FTA.transitionChildren transition
        childSorts = map (`Map.lookup` sorts) children
        fits function = map Just (functionArguments function) == childSorts && functionResult function == sort
