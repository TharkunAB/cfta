{- | Predicate definitions in the formula language, and their unfolding.

A 'Definition' gives a global predicate name parameters and a body in the
formula language. 'unfold' replaces each application of a defined predicate
by its body, with the arguments in place of the parameters. Then a solver
that has no predicates, such as the Z3 entailment, can decide the formula.
The unfolded formula has the same meaning as the original formula, so the
lowering is exact.

'unfold' checks the sorts of the complete original formula first. An unused
argument disappears in the unfolding, so a later check cannot see it.

'unfoldKeeping' keeps the predicates of a signature map in place, so that
another solver can interpret them.
-}
module Data.CFTA.Refinement.Definition (
    Definition (..),
    Definitions,
    DefinitionError (..),
    unfold,
    unfoldKeeping,
) where

import Control.Monad (forM_, unless, when)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), SubstitutionError, Term (..), substituteChecked)

{- | A predicate with parameters and a body in the formula language.

The body can refer to its parameters, to names that its quantifiers bind, and
to other defined predicates. It has no other free names, so its meaning does
not depend on the place of an application.
-}
data Definition = Definition
    { definitionParameters :: ![(Name, Sort)]
    , definitionBody :: !Formula
    }
    deriving (Eq, Show, Read)

-- | The definitions of the global predicates, by name.
type Definitions = Map Name Definition

-- | Why a formula does not unfold.
data DefinitionError
    = -- | A predicate has no definition and no signature.
      UndefinedPredicate !Name
    | -- | An application of a predicate has the wrong number of arguments: the parameters, then the arguments.
      ArityMismatch !Name !Int !Int
    | -- | An argument does not have the sort of its parameter: the argument index, the parameter sort, and the argument sort.
      ArgumentSort !Name !Int !Sort !Sort
    | -- | The parts of a term have sorts that do not fit together.
      IllSortedTerm !Term
    | -- | The two terms of an atom have sorts that do not fit the relation.
      IllSortedAtom !Relation !Term !Term
    | -- | A binder list names the same value twice.
      DuplicateBinder !Name
    | -- | The body of a definition has a free name: the predicate, then the name.
      FreeName !Name !Name
    | -- | A definition uses itself, directly or through other definitions.
      DefinitionCycle !Name
    | -- | The arguments of a predicate cannot replace its parameters.
      SubstitutionFailed !Name !SubstitutionError
    deriving (Eq, Show)

{- | Check the sorts of a formula, then replace each defined predicate by its body.

The declarations give the sorts of the free names. As in the Z3 entailment, a
name without a declaration is an integer, and a function without a
declaration takes integers and gives an integer.

Substitution renames a bound name of a body that an argument would capture.
Every quantifier of the original formula and of the bodies stays, so the
result has the same meaning as the original formula.
-}
unfold :: Definitions -> [(Name, Sort)] -> Formula -> Either DefinitionError Formula
unfold = unfoldKeeping Map.empty

{- | 'unfold', but keep the predicates of the signature map in place.

The signature map gives the parameter sorts of predicates that have no
definition. The sort check reads these sorts. Defined predicates in the
arguments of such a predicate unfold. A definition of the same name takes
precedence over a signature.
-}
unfoldKeeping :: Map Name [Sort] -> Definitions -> [(Name, Sort)] -> Formula -> Either DefinitionError Formula
unfoldKeeping kept definitions declarations original = do
    checkFormula signatures (Map.fromList declarations) original
    expand Set.empty original
  where
    -- The parameter sorts of each predicate that the check accepts.
    signatures = Map.map (map snd . definitionParameters) definitions <> kept

    -- Replace the predicates. The active set holds the definitions that are unfolding now.
    expand :: Set Name -> Formula -> Either DefinitionError Formula
    expand active formula = case formula of
        Top -> Right Top
        Bottom -> Right Bottom
        And parts -> And <$> traverse (expand active) parts
        Or parts -> Or <$> traverse (expand active) parts
        Not inner -> Not <$> expand active inner
        Atom relation left right -> Atom relation <$> expandTerm active left <*> expandTerm active right
        Forall bindings inner -> Forall bindings <$> expand active inner
        Exists bindings inner -> Exists bindings <$> expand active inner
        Predicate name arguments -> case Map.lookup name definitions of
            Nothing
                | name `Map.member` kept -> Predicate name <$> traverse (expandTerm active) arguments
                | otherwise -> Left $ UndefinedPredicate name
            Just (Definition parameters body) -> do
                when (name `Set.member` active) $ Left $ DefinitionCycle name
                checkDefinition signatures name parameters body
                expandedArguments <- traverse (expandTerm active) arguments
                expandedBody <- expand (Set.insert name active) body
                first (SubstitutionFailed name) $ substituteChecked (zip (map fst parameters) expandedArguments) expandedBody

    expandTerm :: Set Name -> Term -> Either DefinitionError Term
    expandTerm active term = case term of
        Lit _ -> Right term
        Var _ -> Right term
        App name arguments -> App name <$> traverse (expandTerm active) arguments
        Neg inner -> Neg <$> expandTerm active inner
        Add left right -> Add <$> expandTerm active left <*> expandTerm active right
        Sub left right -> Sub <$> expandTerm active left <*> expandTerm active right
        Mul left right -> Mul <$> expandTerm active left <*> expandTerm active right
        Div left right -> Div <$> expandTerm active left <*> expandTerm active right
        Mod left right -> Mod <$> expandTerm active left <*> expandTerm active right
        Ite condition yes no -> Ite <$> expand active condition <*> expandTerm active yes <*> expandTerm active no
        Cast inner sort -> (`Cast` sort) <$> expandTerm active inner

-- | Check a body: distinct parameters, no free names, and the sorts under the parameters.
checkDefinition :: Map Name [Sort] -> Name -> [(Name, Sort)] -> Formula -> Either DefinitionError ()
checkDefinition signatures predicate parameters body = do
    checkBinders parameters
    closed (Set.fromList $ map fst parameters) body
    checkFormula signatures (Map.fromList parameters) body
  where
    closed :: Set Name -> Formula -> Either DefinitionError ()
    closed bound formula = case formula of
        Top -> Right ()
        Bottom -> Right ()
        And parts -> mapM_ (closed bound) parts
        Or parts -> mapM_ (closed bound) parts
        Not inner -> closed bound inner
        Atom _ left right -> closedTerm bound left >> closedTerm bound right
        Forall bindings inner -> closed (bound <> Set.fromList (map fst bindings)) inner
        Exists bindings inner -> closed (bound <> Set.fromList (map fst bindings)) inner
        Predicate _ arguments -> mapM_ (closedTerm bound) arguments

    closedTerm :: Set Name -> Term -> Either DefinitionError ()
    closedTerm bound term = case term of
        Lit _ -> Right ()
        Var name -> known bound name
        App name arguments -> known bound name >> mapM_ (closedTerm bound) arguments
        Neg inner -> closedTerm bound inner
        Add left right -> closedTerm bound left >> closedTerm bound right
        Sub left right -> closedTerm bound left >> closedTerm bound right
        Mul left right -> closedTerm bound left >> closedTerm bound right
        Div left right -> closedTerm bound left >> closedTerm bound right
        Mod left right -> closedTerm bound left >> closedTerm bound right
        Ite condition yes no -> closed bound condition >> closedTerm bound yes >> closedTerm bound no
        Cast inner _ -> closedTerm bound inner

    known bound name = unless (name `Set.member` bound) $ Left $ FreeName predicate name

-- | Reject a binder list that names a value twice.
checkBinders :: [(Name, Sort)] -> Either DefinitionError ()
checkBinders bindings = go Set.empty bindings
  where
    go _ [] = Right ()
    go seen ((name, _) : rest)
        | name `Set.member` seen = Left $ DuplicateBinder name
        | otherwise = go (Set.insert name seen) rest

{- | Check the sorts of a formula. The first map gives the parameter sorts of
each predicate, and the second map gives the sorts of the names in scope. The
application of a predicate must fit its parameter sorts.
-}
checkFormula :: Map Name [Sort] -> Map Name Sort -> Formula -> Either DefinitionError ()
checkFormula signatures = go
  where
    go :: Map Name Sort -> Formula -> Either DefinitionError ()
    go sorts formula = case formula of
        Top -> Right ()
        Bottom -> Right ()
        And parts -> mapM_ (go sorts) parts
        Or parts -> mapM_ (go sorts) parts
        Not inner -> go sorts inner
        Atom relation left right -> do
            leftSort <- termSort sorts left
            rightSort <- termSort sorts right
            let ordered = relation `notElem` [Eq, Ne]
            unless (leftSort == rightSort && (not ordered || numeric leftSort))
                $ Left
                $ IllSortedAtom relation left right
        Forall bindings inner -> checkBinders bindings >> go (Map.fromList bindings <> sorts) inner
        Exists bindings inner -> checkBinders bindings >> go (Map.fromList bindings <> sorts) inner
        Predicate name arguments -> do
            parameters <- maybe (Left $ UndefinedPredicate name) Right $ Map.lookup name signatures
            unless (length parameters == length arguments)
                $ Left
                $ ArityMismatch name (length parameters) (length arguments)
            argumentSorts <- traverse (termSort sorts) arguments
            forM_ (zip3 [0 ..] parameters argumentSorts) $ \(index, expected, found) ->
                unless (expected == found) $ Left $ ArgumentSort name index expected found

    termSort :: Map Name Sort -> Term -> Either DefinitionError Sort
    termSort sorts term = case term of
        Lit _ -> Right IntSort
        Var name -> Right $ Map.findWithDefault IntSort name sorts
        App name arguments -> do
            argumentSorts <- traverse (termSort sorts) arguments
            case Map.findWithDefault (FunctionSort (IntSort <$ arguments) IntSort) name sorts of
                FunctionSort parameters result | parameters == argumentSorts -> Right result
                sort | null arguments, not (isFunction sort) -> Right sort
                _ -> Left $ IllSortedTerm term
        Neg inner -> do
            sort <- termSort sorts inner
            unless (numeric sort) $ Left $ IllSortedTerm term
            Right sort
        Add left right -> arithmetic left right
        Sub left right -> arithmetic left right
        Mul left right -> arithmetic left right
        Div left right -> arithmetic left right
        Mod left right -> arithmetic left right
        Ite condition yes no -> do
            go sorts condition
            yesSort <- termSort sorts yes
            noSort <- termSort sorts no
            unless (yesSort == noSort) $ Left $ IllSortedTerm term
            Right yesSort
        Cast inner sort -> termSort sorts inner >> Right sort
      where
        arithmetic left right = do
            leftSort <- termSort sorts left
            rightSort <- termSort sorts right
            unless (leftSort == rightSort && numeric leftSort) $ Left $ IllSortedTerm term
            Right leftSort

    numeric sort = sort == IntSort || sort == RealSort

    isFunction FunctionSort{} = True
    isFunction _ = False
