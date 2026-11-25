{-# LANGUAGE OverloadedStrings #-}

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

The module gives three things:

* The data: 'SortTerm' and 'PolymorphicSignature', with the check
  'checkPolymorphic'.
* The type check: 'principalSort' gives the most general sort of a term, as
  Haskell gives @[] :: [a]@. See Note [Principal sorts]. 'hasSort' tests
  whether a term has a sort that is an instance of a given sort.
* The automaton: 'polymorphicSpace' gives the typed terms of a size and a root
  sort as an automaton with equality constraints. 'polymorphicTerms' lists
  their plain terms, and 'polymorphicGen' reads the automaton as a generator.
  See Note [Sorts as children].
-}
module Data.CFTA.Gen.ManySorted.Polymorphic (
    SortTerm (..),
    PolymorphicSignature (..),
    PolymorphicError (..),
    checkPolymorphic,
    principalSort,
    hasSort,
    polymorphicSpace,
    plainTerm,
    polymorphicTerms,
    polymorphicGen,
    openFunctions,
) where

import Control.Monad (foldM, foldM_)
import Data.Containers.ListUtils (nubOrd)
import Data.List (mapAccumL)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)

import Data.CFTA.Constraint (Constraint, equalityConstraint)
import Data.CFTA.Equality (Edge (Edge), Node (EmptyNode, Node), createMu, mkEdge, mkEqConstraints, terms, union)
import Data.CFTA.Gen.Equality (ECTAGen)
import qualified Data.CFTA.Gen.Equality as ECTAGen
import Data.CFTA.Gen.ManySorted (SortedFunction (..), TypeError (..))
import Data.CFTA.Gen.Synthesis (reduceFully)
import Data.CFTA.Path (ChildIndex (..), Path, path)
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

{- Note [Sorts as children]
~~~~~~~~~~~~~~~~~~~~~~~~
'polymorphicSpace' encodes a term together with its sorts. A typed term of a
function with n arguments has 1 + 2n children: the result sort, the n
argument sorts, and then the n subterms. Each sort child is the node of the
sort as the signature writes it, with the node of all sorts in the place of
each variable. The node of all sorts is recursive: it is the union of each
sort constructor of the signature and of the root sort, applied to the node
of all sorts. Two kinds of equality constraint on each edge do the typing.
First, the occurrences of one variable in the sort children are equal.
Second, the argument sort child i is equal to the result sort child of the
subterm i.

For @cons : a, List a -> List a@, the edge has the children
@[List *, *, List *, t1, t2]@, where @*@ is the node of all sorts. The
constraints make the @*@ below the result sort, the argument sort 1, and the
@*@ below the argument sort 2 equal. They also make the argument sorts equal
to the sorts of @t1@ and @t2@. So @cons(zero, nil)@ has the sort @List Int@:
the sort of @zero@ fixes the variable, and the constraints carry it to the
result sort and to the sort of @nil@. The root edge has the children
@[root sort, typed term]@, and its constraint makes the root sort equal to the
sort of the term.

The sort is a child and not a state, because a state for each sort is a state
for each shape of nested sorts. For the signature of @zero@, @true@, @ite@,
@eq@, @nil@, @cons@, @length@, @pair@, @fst@, and @snd@, an automaton with a
state for each sort has 15, 99, and 831 states for the terms up to the sizes
3, 5, and 7. This automaton has one node for the terms of each size, and the
constraints relate the sort children.

The terms are unrolled by size: there is one node for each size from 1 to the
size, and a function has one edge for each way to divide the size minus 1
among its subterms. The size of a term is the number of its function symbols.
The sort children do not count. The enumeration of "Data.CFTA.Equality" stops
at a recursive node, so a recursive node of terms would hide the terms below
it. Only the node of all sorts is recursive.

The reduction 'Data.CFTA.Gen.Synthesis.reduceFully' propagates the
constraints. When the sort children of each term are fixed, the reduction
resolves each constraint, and the generator of "Data.CFTA.Gen.Equality"
counts the terms. A term with an open sort keeps the node of all sorts in a
sort child (see Note [Principal sorts]). In @length(nil)@, the sort of @nil@ is
@List *@, and no constraint fixes the @*@. Then the generator can refuse to
count the space, with 'Data.CFTA.Gen.Error.CannotCountConstrainedEdges'.
'openFunctions' tells when this can occur.

"Data.CFTA.Gen.Synthesis" uses the same encoding for the components of a
library and for application, with a goal type and arguments that a program
must use. The instances of "Data.CFTA.Gen.ManySorted" are a different
approach: they resolve the constraints in advance, over a closed list of
sorts.
-}

{- | The typed terms of a size whose sort is an instance of a root sort, as an
automaton with equality constraints, after the reduction
'Data.CFTA.Gen.Synthesis.reduceFully'. See Note [Sorts as children]. The size
of a term is the number of its function symbols. A size below 1 gives
'EmptyNode'.

A term of the automaton is a typed term below a root edge, and 'plainTerm'
gives its plain term. The signature must pass 'checkPolymorphic'.
-}
polymorphicSpace :: PolymorphicSignature -> SortTerm -> Int -> Node Symbol
polymorphicSpace signature root size
    | size < 1 = EmptyNode
    | otherwise =
        reduceFully $
            Node [mkEdge "root" [sortNode root, table LazyMap.! size] (equalities [root] [[at [0], at [1, 0]]])]
  where
    functions = polymorphicFunctions signature
    sortsOf function = functionResult function : functionArguments function
    -- The node of all sorts. See Note [Sorts as children].
    allSorts =
        createMu $ \sorts ->
            union
                [ Node [Edge constructor (replicate count sorts)]
                | (constructor, count) <- nubOrd (concatMap constructors (root : concatMap sortsOf functions))
                ]
    sortNode (SortVariable _) = allSorts
    sortNode (SortApply constructor arguments) = Node [Edge constructor (map sortNode arguments)]
    -- The typed terms of each size from 1 to the size. The lazy map builds each node one time.
    table = LazyMap.fromList [(part, termsOf part) | part <- [1 .. size]]
    termsOf part =
        union
            [Node [edgeOf function parts] | function <- functions, parts <- splits (part - 1) (length (functionArguments function))]
    edgeOf function parts =
        mkEdge
            (functionSymbol function)
            (map sortNode (sortsOf function) <> map (table LazyMap.!) parts)
            (equalities (sortsOf function) [[at [index], at [count + index, 0]] | index <- [1 .. count]])
      where
        count = length (functionArguments function)
    at = path . map ChildIndex

{- | The equality constraint of an edge whose first children are the given
sorts: the occurrences of each variable in these sorts are equal. The other
equalities come after them.
-}
equalities :: [SortTerm] -> [[Path]] -> Constraint
equalities sortChildren others =
    equalityConstraint
        $ mkEqConstraints
        $ [ places
          | variable <- variables sortChildren
          , let places =
                    [ path (map ChildIndex (index : place))
                    | (index, sortTerm) <- zip [0 ..] sortChildren
                    , place <- positions variable sortTerm
                    ]
          , length places > 1
          ]
            <> others

-- | The positions of a variable in a sort term, as lists of child indexes.
positions :: Int -> SortTerm -> [[Int]]
positions variable (SortVariable other) = [[] | variable == other]
positions variable (SortApply _ arguments) =
    [index : place | (index, argument) <- zip [0 ..] arguments, place <- positions variable argument]

-- | The ways to divide a number into the given count of parts, in order, each part at least 1.
splits :: Int -> Int -> [[Int]]
splits 0 0 = [[]]
splits _ 0 = []
splits budget parts = [first : rest | first <- [1 .. budget - parts + 1], rest <- splits (budget - first) (parts - 1)]

{- | The plain term of a typed term of 'polymorphicSpace': the term without its
sort children and without the root edge. It uses the positions of the
children and not the symbols, so a function can have any symbol. The root
edge has two children, and a typed term of a function with n arguments has
1 + 2n children. So the root edge is the only node with an even number of
children.
-}
plainTerm :: Term Symbol -> Term Symbol
plainTerm term = case Term.subForest term of
    [_, typed] -> plain typed
    _ -> plain term
  where
    plain typed = Term.Node (Term.rootLabel typed) (map plain (drop ((length children + 1) `div` 2) children))
      where
        children = Term.subForest typed

{- | The plain terms of 'polymorphicSpace', each one time, in the order in
which 'Data.CFTA.Equality.terms' first gives them. The signature must pass
'checkPolymorphic'.
-}
polymorphicTerms :: PolymorphicSignature -> SortTerm -> Int -> [Term Symbol]
polymorphicTerms signature root size = nubOrd (map plainTerm (terms (polymorphicSpace signature root size)))

{- | The generator of 'polymorphicSpace', as 'Data.CFTA.Gen.Equality.fromAutomaton'
reads it, with 'plainTerm' applied to each term. Its counts and its ranks are
those of the typed terms. When 'openFunctions' is empty, each plain term has
one typed term, so the counts are those of 'polymorphicTerms'. The signature
must pass 'checkPolymorphic'.
-}
polymorphicGen :: PolymorphicSignature -> SortTerm -> Int -> ECTAGen (Term Symbol)
polymorphicGen signature root size = plainTerm <$> ECTAGen.fromAutomaton (polymorphicSpace signature root size)

{- | The symbols whose function has a variable in its result sort that is in
none of its argument sorts, as @nil : List a@.

If the list is empty, each well-sorted term has a principal sort without
variables. The proof is by induction on the term: the sorts of the children
fix each variable of the argument sorts, and so each variable of the result
sort. So each plain term has one typed term, the reduction resolves each
constraint, and 'polymorphicGen' counts each space.

If the list is not empty, a term can keep an open sort, as @length(nil)@
does. Then the generator can refuse to count a space that holds such a term,
with 'Data.CFTA.Gen.Error.CannotCountConstrainedEdges'. 'polymorphicTerms'
still lists the term one time. See Note [Sorts as children].
-}
openFunctions :: PolymorphicSignature -> [Symbol]
openFunctions signature =
    [ functionSymbol function
    | function <- polymorphicFunctions signature
    , any (`notElem` variables (functionArguments function)) (variables [functionResult function])
    ]

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
