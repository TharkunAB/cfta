{- | Typed languages from a signature that is data at run time.

"Data.CFTA.Gen.Typing" builds a typed language from a Haskell datatype that
is known at compile time. This module takes a first-order many-sorted
signature as a plain value instead: the sorts, the function symbols with
their argument sorts and result sort, and the root sorts. A constant is a
function symbol with no argument sorts.

'signatureAutomaton' reads the signature as a tree automaton. Its states are
the sorts and its transitions are the function symbols. So the operations of
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
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A first-order many-sorted signature.
data SortedSignature sort symbol = SortedSignature
    { sortedSorts :: [sort]
    -- ^ The sorts. Every other sort in the signature must be in this list.
    , sortedFunctions :: [SortedFunction sort symbol]
    -- ^ The function symbols. Two functions must not have the same symbol.
    , sortedRoots :: [sort]
    -- ^ The sorts of the terms in the language.
    , sortedValues :: [ValueSort sort symbol]
    -- ^ The sorts that have values. A value is a leaf of size one.
    }
    deriving (Eq, Show)

-- | A sort with values. The values are leaves, so the sort can also have function symbols.
data ValueSort sort symbol = ValueSort
    { valueSort :: sort
    , valueSource :: ValueSource symbol
    }
    deriving (Eq, Show)

{- | The values of a sort. Neither kind lists its values: an interval of a
million integers costs the same as one integer.
-}
data ValueSource symbol
    = -- | The integers from the first bound to the second bound, both included.
      Interval !Integer !Integer
    | -- | Some symbols, in this order. Each symbol must occur once.
      Pool [symbol]
    deriving (Eq, Show)

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

-- | A function symbol with its argument sorts and its result sort.
data SortedFunction sort symbol = SortedFunction
    { functionSymbol :: symbol
    , functionArguments :: [sort]
    -- ^ The sorts of the arguments, from left to right. A constant has none.
    , functionResult :: sort
    }
    deriving (Eq, Show)

-- | A reason why a signature is not valid.
data SignatureError sort symbol
    = -- | A function or a root names a sort that is not in the signature.
      UnknownSort !sort
    | -- | Two functions, two values, or a function and a value have this symbol.
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
      AutomatonRejected !(FTA.FTAError (Maybe sort) symbol)
    deriving (Eq, Show)

{- | The automaton of a signature, for the operations of "Data.CFTA".

A state is a sort, as 'Just' of the sort. The initial state is 'Nothing'. It
has the transitions of all root sorts. Each function symbol is one transition,
from its result sort. A signature has one transition for each symbol, so a
term has at most one run.

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
    checkSignature codec signature
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

-- | The leaves of a value source, with the inverse of their ranks.
leafSourceOf :: (Ord symbol) => ValueCodec sort symbol -> ValueSource symbol -> LeafSource symbol
leafSourceOf codec (Interval low high) =
    LeafSource
        { leafCount = Cardinality (high - low + 1)
        , leafTerm = \(Rank rank) -> Term.Node (injectInteger codec (low + rank)) []
        , leafRank = \term -> case term of
            Term.Node symbol [] | Just n <- projectInteger codec symbol, low <= n, n <= high -> Just (Rank (n - low))
            _ -> Nothing
        }
leafSourceOf _ (Pool symbols) =
    LeafSource
        { leafCount = Cardinality (fromIntegral count)
        , leafTerm = \(Rank rank) -> Term.Node (members Array.! fromInteger rank) []
        , leafRank = \term -> case term of
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

-- | Find the first unknown sort, the first duplicate symbol, or the first value problem.
checkSignature ::
    (Ord sort, Ord symbol) =>
    Maybe (ValueCodec sort symbol) -> SortedSignature sort symbol -> Either (SignatureError sort symbol) ()
checkSignature codec signature = do
    case find (`notElem` sortedSorts signature) used of
        Just sort -> Left $ UnknownSort sort
        Nothing -> Right ()
    case duplicates (map functionSymbol (sortedFunctions signature)) of
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
    functionSymbols = map functionSymbol (sortedFunctions signature)
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
    | {- | A child has a sort that differs from the argument sort of the
      function.
      -}
      WrongChildSort
        !Path
        !symbol
        -- | The argument sorts of the function.
        [sort]
        -- | The sorts of the children, from left to right. A child that is not well-typed has no sort.
        [Maybe sort]
    | -- | The term is well-typed at the root, but its sort is not a root sort.
      NotRootSort !sort
    deriving (Eq, Show)

{- | Check that a term is a term of the signature, and find its sort.

A node is not well-typed if its symbol is unknown, if it has the wrong number
of children, or if a well-typed child has a sort that the function does not
accept at that argument. The error names the first such node in preorder. A
child that is not well-typed has no sort, so its parent is not in error for
that child. The error then names the node in that child.

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
    valueOf symbol = valueSort <$> find (\value -> holds codec (valueSource value) symbol) (sortedValues signature)

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

    functions = Map.fromList [(functionSymbol function, function) | function <- sortedFunctions signature]

    check reversed term = case Map.lookup symbol functions of
        Nothing -> case valueOf symbol of
            Just sort'
                | null children -> Right sort'
                | otherwise -> Left $ WrongArity here symbol 0 (length children)
            Nothing -> Left $ UnknownFunction here symbol
        Just function
            | length expected /= length children -> Left $ WrongArity here symbol (length expected) (length children)
            | any mismatch (zip expected found) ->
                Left $ WrongChildSort here symbol expected (map (either (const Nothing) Just) results)
            | otherwise -> (functionResult function <$ sequence results)
          where
            expected = functionArguments function
            results = [check (index : reversed) subterm | (index, subterm) <- zip [0 ..] children]
            found = map (either (const Nothing) Just) results
      where
        symbol = Term.rootLabel term
        children = Term.subForest term
        here = path (map ChildIndex (reverse reversed))

    mismatch (sort, Just actual) = sort /= actual
    mismatch (_, Nothing) = False
