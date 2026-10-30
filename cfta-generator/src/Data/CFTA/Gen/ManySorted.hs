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
    SignatureError (..),
    signatureAutomaton,
    signatureGen,
    TypeError (..),
    typeCheck,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Gen (Gen)
import qualified Data.CFTA.Gen as Gen
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
    }
    deriving (Eq, Show)

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
    | -- | Two functions have this symbol.
      DuplicateSymbol !symbol
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
-}
signatureAutomaton ::
    (Ord sort, Ord symbol) =>
    SortedSignature sort symbol ->
    Either (SignatureError sort symbol) (FTA.FTA (Maybe sort) symbol Constraint)
signatureAutomaton signature = do
    checkSignature signature
    let transitions =
            [ (functionResult function, FTA.Transition (functionSymbol function) (map Just (functionArguments function)) noConstraint)
            | function <- sortedFunctions signature
            ]
        rows = Map.fromListWith (flip (<>)) [(Just sort, [transition]) | (sort, transition) <- transitions]
        sortRows = [(Just sort, Map.findWithDefault [] (Just sort) rows) | sort <- nubOrd (sortedSorts signature)]
        rootRow = concat [Map.findWithDefault [] (Just root) rows | root <- nubOrd (sortedRoots signature)]
    either (Left . AutomatonRejected) Right $ FTA.mkFTA Nothing ((Nothing, rootRow) : sortRows)

{- | The terms of a signature as a generator.

The generator is the one that 'Data.CFTA.Gen.fromAutomaton' gives for
'signatureAutomaton'. It is recursive when a sort is, so apply
'Data.CFTA.Gen.upToSize' before the queries of "Data.CFTA.Gen".
-}
signatureGen ::
    (Ord sort, Ord symbol, Hashable symbol, Typeable symbol) =>
    SortedSignature sort symbol ->
    Either (SignatureError sort symbol) (Gen symbol (Term symbol))
signatureGen signature = do
    automaton <- signatureAutomaton signature
    pure $ Gen.fromAutomaton $ Interned.fromRows (FTA.initialState automaton) (FTA.transitionTable automaton)

-- | Find the first unknown sort or the first duplicate symbol.
checkSignature :: (Ord sort, Ord symbol) => SortedSignature sort symbol -> Either (SignatureError sort symbol) ()
checkSignature signature = do
    case find (`notElem` sortedSorts signature) used of
        Just sort -> Left $ UnknownSort sort
        Nothing -> Right ()
    case duplicates (map functionSymbol (sortedFunctions signature)) of
        symbol : _ -> Left $ DuplicateSymbol symbol
        [] -> Right ()
  where
    used =
        concat [functionResult function : functionArguments function | function <- sortedFunctions signature]
            <> sortedRoots signature
    duplicates symbols = Map.keys $ Map.filter (> (1 :: Int)) $ Map.fromListWith (+) [(symbol, 1) | symbol <- symbols]

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
-}
typeCheck ::
    (Ord sort, Ord symbol) =>
    SortedSignature sort symbol ->
    Term symbol ->
    Either (TypeError sort symbol) sort
typeCheck signature term0 = check [] term0 >>= rootSort
  where
    rootSort sort'
        | sort' `elem` sortedRoots signature = Right sort'
        | otherwise = Left $ NotRootSort sort'

    functions = Map.fromList [(functionSymbol function, function) | function <- sortedFunctions signature]

    check reversed term = case Map.lookup symbol functions of
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
