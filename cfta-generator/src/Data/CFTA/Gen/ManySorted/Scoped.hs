{- | Binders and variables in a run-time signature.

A function symbol of a "Data.CFTA.Gen.ManySorted" signature can bind
variables in some of its children. A 'Binding' lists, for each child, the
sorts that the child binds. So @let x: Int = e1 in e2@ is a function symbol
with two arguments and the scopes @[[], [Int]]@: its second child has one more
variable, of the sort Int. A variable is a leaf with a de Bruijn index. The
index 0 is the variable that the nearest binder binds. The sort of a variable
is the sort of its place in the environment.

The approach is that of "Data.CFTA.Gen.Typing", which has the same language for
a Haskell datatype known at compile time:

* A state of the automaton is an environment and a sort, as 'Data.CFTA.Gen.Typing.Goal' is.
  The environment is the list of the sorts of the variables in scope, innermost
  first, and then the inputs.
* A bound limits the number of binders around each position. The inputs are not
  binders. A transition whose child would pass the bound is not in the
  automaton. This is the bound 'Data.CFTA.Gen.Typing.Binders'.
* A variable is one transition for each place of the environment that holds the
  goal sort, as 'Data.CFTA.Gen.Typing.variable' is.
* The automaton is cyclic when a function has an argument, so the generator is
  counted by size. Apply 'Data.CFTA.Gen.upToSize'.

This module adds what the typing module does not need: the signature is data,
so a function lists its scopes in a 'Binding' and not in a node view, and the
variables and the values are symbols that a codec makes.
-}
module Data.CFTA.Gen.ManySorted.Scoped (
    ScopedSignature (..),
    Binding (..),
    ScopedCodec (..),
    ScopeError (..),
    ScopedState (..),
    scopedAutomaton,
    scopedGen,
    scopedTypeCheck,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Gen (Gen)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.ManySorted
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A signature with binders.
data ScopedSignature sort symbol = ScopedSignature
    { scopedBase :: SortedSignature sort symbol
    -- ^ The sorts, the functions, the roots, and the value sorts.
    , scopedBinders :: [Binding sort symbol]
    -- ^ The functions that bind variables. A function without a 'Binding' binds none.
    , scopedInputs :: [sort]
    -- ^ The sorts of the variables in scope at the root. The input @i@ has the index @i@ there.
    , scopedBound :: Int
    -- ^ The number of binders around each position, at most. The inputs are not binders.
    }
    deriving (Eq, Show)

-- | The variables that the children of a function bind.
data Binding sort symbol = Binding
    { bindingSymbol :: symbol
    -- ^ A function of the base signature. At most one 'Binding' names it.
    , bindingScopes :: [[sort]]
    -- ^ One list for each argument of the function. The first sort of a list is the variable with the index 0 in that child.
    }
    deriving (Eq, Show)

{- | How the variables, and the values of the value sorts, are symbols.

The variables are leaves. A variable symbol must not be a function symbol, a
value, or a 'valueSymbol'. The check finds the symbols of the functions, the
pools, and the sorts, and it cannot find all integers of an interval.
-}
data ScopedCodec sort symbol = ScopedCodec
    { variableSymbol :: Int -> symbol
    -- ^ The symbol of the variable with an index.
    , variableIndex :: symbol -> Maybe Int
    -- ^ The index of a variable symbol. It gives 'Nothing' for another symbol.
    , scopedValueCodec :: Maybe (ValueCodec sort symbol)
    -- ^ Needed when the base signature has value sorts.
    }

-- | A reason why a scoped signature is not valid.
data ScopeError sort symbol
    = -- | The base signature is not valid.
      BaseError !(SignatureError sort symbol)
    | -- | A 'Binding' names a symbol that is not a function.
      BindingOfUnknownFunction !symbol
    | -- | Two 'Binding' name one function.
      DuplicateBinding !symbol
    | -- | The scopes of a 'Binding' are not one for each argument.
      BindingArity !symbol
    | -- | A symbol of a function, a pool, or a sort is also a variable symbol.
      VariableSymbolClash !symbol
    | -- | The bound is negative.
      NegativeBound !Int
    | -- | The automaton check rejected the signature. This error is not expected.
      ScopedAutomatonRejected !(FTA.FTAError (ScopedState sort) symbol)
    deriving (Eq, Show)

{- | A state of the automaton of a scoped signature: the root, or a term of a
sort in an environment.
-}
data ScopedState sort = ScopedRoot | ScopedGoal ![sort] !sort
    deriving (Eq, Ord, Show)

checkScoped ::
    (Ord sort, Ord symbol) =>
    ScopedCodec sort symbol -> ScopedSignature sort symbol -> Either (ScopeError sort symbol) ()
checkScoped codec scoped = do
    either (Left . BaseError) Right $ case (sortedValues base, scopedValueCodec codec) of
        (_ : _, Nothing) -> Left ValueSortsNeedCodec
        _ -> checkSignatureWith (scopedValueCodec codec) base
    if scopedBound scoped < 0 then Left $ NegativeBound $ scopedBound scoped else Right ()
    case [bindingSymbol b | b <- bindings, bindingSymbol b `notElem` map functionSymbol (sortedFunctions base)] of
        symbol : _ -> Left $ BindingOfUnknownFunction symbol
        [] -> Right ()
    case duplicates (map bindingSymbol bindings) of
        symbol : _ -> Left $ DuplicateBinding symbol
        [] -> Right ()
    case [ functionSymbol f
         | f <- sortedFunctions base
         , Just scopes <- [Map.lookup (functionSymbol f) bindingMap]
         , length scopes /= length (functionArguments f)
         ] of
        symbol : _ -> Left $ BindingArity symbol
        [] -> Right ()
    case [sort | sort <- concat (concatMap bindingScopes bindings) <> scopedInputs scoped, sort `notElem` sortedSorts base] of
        sort : _ -> Left $ BaseError $ UnknownSort sort
        [] -> Right ()
    case filter isVariable (map functionSymbol (sortedFunctions base) <> poolSymbols <> placeholders) of
        symbol : _ -> Left $ VariableSymbolClash symbol
        [] -> Right ()
  where
    base = scopedBase scoped
    bindings = scopedBinders scoped
    bindingMap = Map.fromList [(bindingSymbol b, bindingScopes b) | b <- bindings]
    isVariable = isJust . variableIndex codec
    poolSymbols = concat [symbols | ValueSort _ (Pool symbols) <- sortedValues base]
    placeholders = maybe [] (\valueCodec -> [valueSymbol valueCodec (valueSort v) | v <- sortedValues base]) (scopedValueCodec codec)
    duplicates xs = Map.keys $ Map.filter (> (1 :: Int)) $ Map.fromListWith (+) [(x, 1) | x <- xs]

{- | The automaton of a scoped signature.

The states are 'ScopedState'. The root has the transitions of the root sorts in
the environment of the inputs. A function symbol is a transition from a state
of its result sort, and each child is a state with the environment of the
child. A variable is a transition with no child. A value sort has a
transition with no child for its values, as in 'signatureAutomatonWith'.
-}
scopedAutomaton ::
    (Ord sort, Ord symbol) =>
    ScopedCodec sort symbol ->
    ScopedSignature sort symbol ->
    Either (ScopeError sort symbol) (FTA.FTA (ScopedState sort) symbol Constraint)
scopedAutomaton codec scoped = do
    checkScoped codec scoped
    either (Left . ScopedAutomatonRejected) Right $ FTA.mkFTA ScopedRoot (Map.toList (close Map.empty [ScopedRoot]))
  where
    base = scopedBase scoped
    inputs = scopedInputs scoped
    scopesOf f = Map.findWithDefault (map (const []) (functionArguments f)) (functionSymbol f) bindingMap
    bindingMap = Map.fromList [(bindingSymbol b, bindingScopes b) | b <- scopedBinders scoped]

    close rows [] = rows
    close rows (state : pending)
        | Map.member state rows = close rows pending
        | otherwise = close (Map.insert state transitions rows) (concatMap FTA.transitionChildren transitions <> pending)
      where
        transitions = row state

    row ScopedRoot = concat [row (ScopedGoal inputs root) | root <- nubOrd (sortedRoots base)]
    row (ScopedGoal env goal) =
        [ FTA.Transition (functionSymbol f) (zipWith ScopedGoal childEnvs (functionArguments f)) noConstraint
        | f <- sortedFunctions base
        , functionResult f == goal
        , let childEnvs = [binds <> env | binds <- scopesOf f]
        , all (\childEnv -> length childEnv - length inputs <= scopedBound scoped) childEnvs
        ]
            <> [FTA.Transition (variableSymbol codec index) [] noConstraint | (index, sort) <- zip [0 ..] env, sort == goal]
            <> [ FTA.Transition (valueSymbol valueCodec goal) [] noConstraint
               | Just valueCodec <- [scopedValueCodec codec]
               , v <- sortedValues base
               , valueSort v == goal
               ]

{- | The terms of a scoped signature as a generator.

The generator reads the automaton as 'Data.CFTA.Gen.fromAutomaton' does, or as
'Data.CFTA.Gen.fromAutomatonWithLeaves' does when there are value sorts. Apply
'Data.CFTA.Gen.upToSize' before the queries of "Data.CFTA.Gen". Every term is
closed over the inputs and well-typed.
-}
scopedGen ::
    (Ord sort, Ord symbol, Hashable symbol, Typeable symbol) =>
    ScopedCodec sort symbol ->
    ScopedSignature sort symbol ->
    Either (ScopeError sort symbol) (Gen symbol (Term symbol))
scopedGen codec scoped = do
    automaton <- scopedAutomaton codec scoped
    let graph = Interned.fromRows (FTA.initialState automaton) (FTA.transitionTable automaton)
    pure $ case scopedValueCodec codec of
        Just valueCodec
            | not (null (sortedValues (scopedBase scoped))) ->
                Gen.fromAutomatonWithLeaves (valueLeaves valueCodec (scopedBase scoped)) graph
        _ -> Gen.fromAutomaton graph

{- | Check that a term is a term of a scoped signature, and find its sort.

The rules of 'typeCheck' hold. A child is checked in its environment. A
variable symbol needs an index below the number of variables in scope, or it is
an 'UnboundVariable' with the path. A function whose child would pass the bound
on the binders is a 'TooManyBinders'. So the accepted terms are the terms of
'scopedGen'.
-}
scopedTypeCheck ::
    (Ord sort, Ord symbol) =>
    ScopedCodec sort symbol ->
    ScopedSignature sort symbol ->
    Term symbol ->
    Either (TypeError sort symbol) sort
scopedTypeCheck codec scoped term0 = check (scopedInputs scoped) [] term0 >>= rootSort
  where
    base = scopedBase scoped
    inputs = scopedInputs scoped
    rootSort sort'
        | sort' `elem` sortedRoots base = Right sort'
        | otherwise = Left $ NotRootSort sort'

    functions = Map.fromList [(functionSymbol f, f) | f <- sortedFunctions base]
    scopes = Map.fromList [(bindingSymbol b, bindingScopes b) | b <- scopedBinders scoped]
    valueOf symbol = scopedValueCodec codec >>= \valueCodec -> valueSortOf valueCodec base symbol

    check env reversed term = case Map.lookup symbol functions of
        Just f
            | length expected /= length children -> Left $ WrongArity here symbol (length expected) (length children)
            | any (\childEnv -> length childEnv - length inputs > scopedBound scoped) childEnvs -> Left $ TooManyBinders here symbol
            | any mismatch (zip expected found) ->
                Left $ WrongChildSort here symbol expected found
            | otherwise -> functionResult f <$ sequence results
          where
            expected = functionArguments f
            childEnvs = [binds <> env | binds <- Map.findWithDefault (map (const []) expected) symbol scopes]
            results = [check childEnv (index : reversed) child | (index, childEnv, child) <- zip3 [0 ..] childEnvs children]
            found = map (either (const Nothing) Just) results
        Nothing -> case variableIndex codec symbol of
            Just index
                | not (null children) -> Left $ WrongArity here symbol 0 (length children)
                | index < 0 || index >= length env -> Left $ UnboundVariable here index (length env)
                | otherwise -> Right (env !! index)
            Nothing -> case valueOf symbol of
                Just sort'
                    | null children -> Right sort'
                    | otherwise -> Left $ WrongArity here symbol 0 (length children)
                Nothing -> Left $ UnknownFunction here symbol
      where
        symbol = Term.rootLabel term
        children = Term.subForest term
        here = path (map ChildIndex (reverse reversed))

    mismatch (sort, Just actual) = sort /= actual
    mismatch (_, Nothing) = False
