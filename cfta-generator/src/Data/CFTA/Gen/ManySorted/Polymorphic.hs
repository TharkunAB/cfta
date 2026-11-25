{- | Signatures whose sorts have variables.

A signature of "Data.CFTA.Gen.ManySorted" has closed sorts. So a polymorphic
function needs one function for each sort: one @cons@ for lists of integers,
one more for lists of Booleans, and so on. In this module a sort can hold sort
variables, as a Haskell type can. So one function @cons : a, List a -> List a@
is sufficient. A sort variable stands for every sort. It does not stand for a
declared list of sorts.

A sort is a 'SortTerm': a variable, or a sort constructor with its arguments.
A sort constructor is a 'Symbol' with a fixed number of arguments: @Int@ has
none, @List@ has one, and @Pair@ has two. The scope of a variable is one
function. The variable 0 of one function and the variable 0 of another
function are different variables.

Each symbol has one function. The variables do the work that the instances of
a symbol do in "Data.CFTA.Gen.ManySorted". Each sort constructor has one
number of arguments in all the signature. 'checkPolymorphic' checks the two
rules.

'principalSort' gives the most general sort of a term, as Haskell gives
@[] :: [a]@. See Note [Principal sorts]. 'hasSort' tests whether a term has a
sort that is an instance of a given sort.
-}
module Data.CFTA.Gen.ManySorted.Polymorphic (
    SortTerm (..),
    PolymorphicSignature (..),
    PolymorphicError (..),
    checkPolymorphic,
    principalSort,
    hasSort,
) where

import Control.Monad (foldM, foldM_)
import Data.Containers.ListUtils (nubOrd)
import Data.List (mapAccumL)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)

import Data.CFTA.Gen.ManySorted (SortedFunction (..), TypeError (..))
import Data.CFTA.Path (ChildIndex (..), path)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A sort that can hold sort variables.
data SortTerm
    = -- | A sort variable. Its scope is one function, or one principal sort.
      SortVariable !Int
    | -- | A sort constructor and its arguments.
      SortApply !Symbol [SortTerm]
    deriving (Eq, Ord, Show)

-- | A signature whose sorts can hold sort variables.
newtype PolymorphicSignature = PolymorphicSignature
    { polymorphicFunctions :: [SortedFunction SortTerm Symbol]
    -- ^ The functions. Each symbol has one function.
    }
    deriving (Eq, Show)

-- | A reason why a polymorphic signature is not valid.
data PolymorphicError
    = -- | Two functions have this symbol.
      RepeatedSymbol !Symbol
    | {- | A sort constructor has two different numbers of arguments. The
      fields are the constructor, the first number, and the different number.
      -}
      ConstructorArity !Symbol !Int !Int
    deriving (Eq, Show)

{- | Check that each symbol has one function, and that each sort constructor
has one number of arguments in all the sorts of the signature. The first
error comes: a repeated symbol in the order of the symbols, then a sort
constructor in the order of the functions, with the argument sorts before the
result sort.
-}
checkPolymorphic :: PolymorphicSignature -> Either PolymorphicError ()
checkPolymorphic signature = do
    case Map.keys (Map.filter (> (1 :: Int)) (Map.fromListWith (+) [(functionSymbol function, 1) | function <- functions])) of
        symbol : _ -> Left $ RepeatedSymbol symbol
        [] -> Right ()
    foldM_
        arity
        Map.empty
        [ use
        | function <- functions
        , sortTerm <- functionArguments function <> [functionResult function]
        , use <- constructors sortTerm
        ]
  where
    functions = polymorphicFunctions signature
    arity seen (constructor, count) = case Map.lookup constructor seen of
        Just first | first /= count -> Left $ ConstructorArity constructor first count
        _ -> Right (Map.insert constructor count seen)

-- | The sort constructors of a sort term with their numbers of arguments, in preorder.
constructors :: SortTerm -> [(Symbol, Int)]
constructors (SortVariable _) = []
constructors (SortApply constructor arguments) = (constructor, length arguments) : concatMap constructors arguments

{- Note [Principal sorts]
~~~~~~~~~~~~~~~~~~~~~~
A sort of a term is principal when each sort of the term is an instance of
it. An instance of a sort replaces some of its variables with sorts. For
example, @nil@ has the principal sort @List a@. Its sorts are @List Int@,
@List Bool@, @List (List a)@, and all the other instances of @List a@.

When each symbol has one function, a well-sorted term has one principal sort,
up to the names of its variables. The proof is by induction on the term.
Suppose that each child of @f(t1, ..., tn)@ has a principal sort. Each sort
of the term comes from the function of @f@: one instance of the argument sorts
of the function gives a sort of each child, and the same instance of the
result sort is the sort of the term. If the argument sorts and the principal
sorts of the children unify, first-order unification gives a most general
unifier. The result sort under this unifier is a sort of the term, and each
other sort of the term is an instance of it. So it is the principal sort. Two
principal sorts of one term are instances of each other, so they differ only
in the names of their variables. 'principalSort' numbers the variables in the
order of their first occurrence, so equal principal sorts are equal values.

The unification needs the occurs check. The equation @a = List a@ has no
solution in finite sorts, so a unifier must not bind @a@ to a sort that holds
@a@.

Before the unification, the variables of the function and of each child must
be different. Two children can both have the principal sort @List a@, but the
@a@ of one child and the @a@ of the other child are different variables. For
example, @pair(nil, nil)@ has the principal sort @Pair (List a) (List b)@, not
@Pair (List a) (List a)@. So 'principalSort' renames the variables of the
function to 0, 1, ..., and the variables of each child to the numbers after
those of the function and of the children before it.

A variable is open when it stays in the principal sort of a subterm and the
context does not fix it. In @length(nil)@, the subterm @nil@ has the sort
@List a@, and @length : List a -> Int@ gives no sort for @a@. The term has the
sort @Int@ for each sort of @a@.
-}

{- | The principal sort of a term. Its variables are numbered 0, 1, 2, ... in
the order of their first occurrence, from left to right. See
Note [Principal sorts].

The errors are those of 'Data.CFTA.Gen.ManySorted.typeCheck', in the same
order: the error names the first node in preorder that is not well-sorted. A
node is not well-sorted if its symbol has no function ('UnknownFunction'), if
it has a different number of children than its function has arguments
('WrongArity'), or if no one substitution makes each argument sort equal to
the sort of its well-sorted child ('WrongChildSort'). A child that is not
well-sorted has no sort, so it does not constrain its parent. The error then
names the node in that child. The fields of 'WrongChildSort' are the argument
sorts as the signature gives them, and the principal sorts of the children.

The signature must pass 'checkPolymorphic'.
-}
principalSort :: PolymorphicSignature -> Term Symbol -> Either (TypeError SortTerm Symbol) SortTerm
principalSort signature = sortAt []
  where
    functions = Map.fromList [(functionSymbol function, function) | function <- polymorphicFunctions signature]

    sortAt reversed term = case Map.lookup symbol functions of
        Nothing -> Left $ UnknownFunction here symbol
        Just function
            | length (functionArguments function) /= length children ->
                Left $ WrongArity here symbol (length (functionArguments function)) (length children)
            | otherwise -> case foldM unifyChild Map.empty (zip arguments renamed) of
                Nothing -> Left $ WrongChildSort here symbol (functionArguments function) found
                Just substitution -> canonical (resolve substitution result) <$ sequence results
          where
            -- The variables of the function are 0 to count - 1. The variables
            -- of each child come after them and after those of the children
            -- before it. See Note [Principal sorts].
            names = renaming 0 (functionResult function : functionArguments function)
            arguments = map (rename names) (functionArguments function)
            result = rename names (functionResult function)
            results = [sortAt (index : reversed) child | (index, child) <- zip [0 ..] children]
            found = map (either (const Nothing) Just) results
            renamed = snd (mapAccumL apart (Map.size names) found)
      where
        symbol = Term.rootLabel term
        children = Term.subForest term
        here = path (map ChildIndex (reverse reversed))

    apart next = maybe (next, Nothing) (fmap Just . renameFrom next)
    unifyChild substitution (argument, Just child) = unify substitution argument child
    unifyChild substitution (_, Nothing) = Just substitution

{- | Whether a term is well-sorted and has a sort that is an instance of the
given sort. The principal sort of the term and the given sort must have a
common instance, after their variables are made different. For a sort without
variables, this means that the sort is an instance of the principal sort. The
sort @'SortVariable' 0@ holds every well-sorted term.
-}
hasSort :: PolymorphicSignature -> SortTerm -> Term Symbol -> Bool
hasSort signature root term = case principalSort signature term of
    Left _ -> False
    Right principal ->
        let (next, principal') = renameFrom 0 principal
         in isJust (unify Map.empty principal' (snd (renameFrom next root)))

-- | Replace each variable of a sort term. The result of a replacement is not replaced again.
substitute :: (Int -> SortTerm) -> SortTerm -> SortTerm
substitute replace (SortVariable variable) = replace variable
substitute replace (SortApply constructor arguments) = SortApply constructor (map (substitute replace) arguments)

-- | The variables of some sort terms, each one time, in the order of their first occurrence, from left to right.
variables :: [SortTerm] -> [Int]
variables = nubOrd . concatMap occurrences
  where
    occurrences (SortVariable variable) = [variable]
    occurrences (SortApply _ arguments) = concatMap occurrences arguments

-- | New names for the variables of some sort terms: start, start + 1, ..., in the order of 'variables'.
renaming :: Int -> [SortTerm] -> Map.Map Int Int
renaming start sortTerms = Map.fromList (zip (variables sortTerms) [start ..])

-- | Give the variables of a sort term their new names.
rename :: Map.Map Int Int -> SortTerm -> SortTerm
rename names = substitute (\variable -> SortVariable (Map.findWithDefault variable variable names))

-- | Rename the variables of a sort term to start, start + 1, ..., and give the first number after them.
renameFrom :: Int -> SortTerm -> (Int, SortTerm)
renameFrom start sortTerm = (start + Map.size names, rename names sortTerm)
  where
    names = renaming start [sortTerm]

-- | A sort term with its variables numbered 0, 1, 2, ... in the order of their first occurrence.
canonical :: SortTerm -> SortTerm
canonical = snd . renameFrom 0

{- | The sort term that a substitution gives for a sort term, at the root
only. A bound variable gives its binding, until the result is not a bound
variable.
-}
walk :: Map.Map Int SortTerm -> SortTerm -> SortTerm
walk substitution (SortVariable variable)
    | Just bound <- Map.lookup variable substitution = walk substitution bound
walk _ sortTerm = sortTerm

-- | Apply a substitution to all the variables of a sort term.
resolve :: Map.Map Int SortTerm -> SortTerm -> SortTerm
resolve substitution =
    substitute (\variable -> maybe (SortVariable variable) (resolve substitution) (Map.lookup variable substitution))

-- | Whether a variable occurs in a sort term under a substitution.
occurs :: Map.Map Int SortTerm -> Int -> SortTerm -> Bool
occurs substitution variable sortTerm = case walk substitution sortTerm of
    SortVariable other -> variable == other
    SortApply _ arguments -> any (occurs substitution variable) arguments

{- | Extend a substitution so that two sort terms become equal, if a
substitution can do it. The result is the most general such substitution.
The occurs check keeps each binding finite.
-}
unify :: Map.Map Int SortTerm -> SortTerm -> SortTerm -> Maybe (Map.Map Int SortTerm)
unify substitution left right = case (walk substitution left, walk substitution right) of
    (SortVariable one, SortVariable other) | one == other -> Just substitution
    (SortVariable variable, other) -> bind variable other
    (other, SortVariable variable) -> bind variable other
    (SortApply one leftArguments, SortApply other rightArguments)
        | one == other && length leftArguments == length rightArguments ->
            foldM (\current (l, r) -> unify current l r) substitution (zip leftArguments rightArguments)
        | otherwise -> Nothing
  where
    bind variable other
        | occurs substitution variable other = Nothing
        | otherwise = Just (Map.insert variable other substitution)
