{- | An 'Entailment' that evaluates ground refinements with Haskell interpretations.

A ground value is an integer, or a data constructor applied to ground values.
The caller gives a Haskell function for each named function and predicate
that the solver interprets.

For each query, the solver first checks the sorts and unfolds the defined
predicates ("Data.CFTA.Refinement.Definition"). A predicate with an
interpretation stays in place. A query that fails the sort check, for example
because a predicate has no definition and no interpretation, gives 'Unknown'.

Then the solver reads the top-level equalities of the assumptions and the
antecedent, such as @v == append(x, y)@ and @x == cons(1, nil)@. It gives a
value to each name whose other side it can evaluate, until no equality adds a
value. Then it evaluates the antecedent and the consequent with these values,
in three-valued logic. A part that it cannot evaluate is unknown: a name
without a value, a quantifier, a cast, a term of sort 'BoolSort' or
'RealSort', a division by a divisor that is not positive, or an argument
outside the domain of an interpretation. A false part decides a conjunction,
and a true part decides a disjunction.

Each equality is a conjunct of the antecedent, so each model of the
antecedent gives a name the value that the solver gives it. Thus a false
antecedent or a true consequent gives 'Yes'. A true antecedent and a false
consequent give 'No': a countermodel. The 'No' is sound when these four
conditions hold:

1. The interpretations agree with the meaning of the names. They are trusted
   code.
2. The data constructors are free, and each data function gives the
   canonical value: the value that the constructors build. Then structural
   equality of values is the equality of the logic.
3. Each declared sort has a value. 'IntSort', 'RealSort', and 'BoolSort' have
   values, a function sort has a value when its result sort has one, and a
   named sort has a value when 'inhabitedSorts' contains it. The solver
   checks this condition: when it fails, a 'No' becomes 'Unknown'.
4. The query is well sorted. The solver checks this condition: a query that
   fails the sort check gives 'Unknown'.

Combine this solver with another through 'Data.CFTA.Refinement.fallback'.
-}
module Data.CFTA.Refinement.Ground (
    Value (..),
    Interpretations (..),
    groundEntailment,
) where

import Control.Monad (zipWithM)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Data.CFTA.Formula (Formula (..), Name, Relation (..), Sort (..), Term (..))
import Data.CFTA.Refinement.Definition (Definitions, unfoldKeeping)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), entailmentWithBindings)

-- | A ground value: an integer, or a data constructor applied to its values.
data Value
    = IntValue !Integer
    | DataValue !Name ![Value]
    deriving (Eq, Ord, Show)

{- | The Haskell meanings of named functions and predicates, and the named
sorts that have a value. A function gives 'Nothing' for arguments outside its
domain, and the application is then unknown.
-}
data Interpretations = Interpretations
    { interpretedFunctions :: Map Name ([Value] -> Maybe Value)
    -- ^ The functions of 'App'. The declarations give their sorts.
    , interpretedPredicates :: Map Name ([Sort], [Value] -> Maybe Bool)
    -- ^ The predicates of 'Predicate', with their parameter sorts.
    , inhabitedSorts :: Set Sort
    -- ^ The named sorts that have a value.
    }

{- | Decide entailments by evaluation under fixed declarations and ambient
assumptions.

The declarations give the sorts of values and functions, as for
'Data.CFTA.Refinement.LiquidFixpoint.withZ3Definitions'. A name without a
declaration is an integer. A fresh value name of a binding has the sort of the
name that it stands for. A binding does not assert equality, so a fresh name
gets a value only from an equality of the antecedent. An assumption that
fails the sort check makes every query 'Unknown'.
-}
groundEntailment :: Interpretations -> Definitions -> [(Name, Sort)] -> [Formula] -> Entailment
groundEntailment interpretations definitions declarations assumptions =
    entailmentWithBindings $ \bindings antecedent consequent ->
        let scope = [(fresh, fromMaybe IntSort $ lookup original declarations) | (fresh, original) <- bindings] <> declarations
         in pure $ case (unfolded, prepare scope antecedent, prepare scope consequent) of
                (Right premises, Right premise, Right conclusion) ->
                    case groundVerdict interpretations (premises <> [premise]) conclusion of
                        No | not allInhabited -> Unknown
                        verdict -> verdict
                _ -> Unknown
  where
    prepare = unfoldKeeping (Map.map fst $ interpretedPredicates interpretations) definitions
    unfolded = traverse (prepare declarations) assumptions
    allInhabited = all (inhabited (inhabitedSorts interpretations) . snd) declarations

-- | Whether a sort has a value. A function sort has a constant function when its result sort has a value.
inhabited :: Set Sort -> Sort -> Bool
inhabited named sort = case sort of
    IntSort -> True
    RealSort -> True
    BoolSort -> True
    FunctionSort _ result -> inhabited named result
    NamedSort _ _ -> sort `Set.member` named

-- | Decide whether the conjunction of the premises implies the conclusion.
groundVerdict :: Interpretations -> [Formula] -> Formula -> Verdict
groundVerdict interpretations premises conclusion =
    case (formulaValue interpretations values premise, formulaValue interpretations values conclusion) of
        (Just False, _) -> Yes
        (_, Just True) -> Yes
        (Just True, Just False) -> No
        _ -> Unknown
  where
    premise = And premises
    values = groundValues interpretations (conjuncts premise)

-- | The parts of nested conjunctions.
conjuncts :: Formula -> [Formula]
conjuncts (And parts) = concatMap conjuncts parts
conjuncts formula = [formula]

{- | Give values to names from equalities @x == t@ or @t == x@, until no
equality adds a value. The first value of a name stays. A name with a
function interpretation has a fixed meaning, so it gets no value.
-}
groundValues :: Interpretations -> [Formula] -> Map Name Value
groundValues interpretations parts = go Map.empty
  where
    equations =
        [ (name, term)
        | Atom Eq left right <- parts
        , (named, term) <- [(left, right), (right, left)]
        , Just name <- [solvable named]
        ]
    solvable term = case term of
        Var name | free name -> Just name
        App name [] | free name -> Just name
        _ -> Nothing
    free name = Map.notMember name (interpretedFunctions interpretations)
    go values =
        case [ (name, value)
             | (name, term) <- equations
             , Map.notMember name values
             , Just value <- [termValue interpretations values term]
             ] of
            [] -> values
            (name, value) : _ -> go (Map.insert name value values)

{- | The truth of a formula, or 'Nothing' when it is unknown. A false part
decides a conjunction and a true part decides a disjunction, also when other
parts are unknown.
-}
formulaValue :: Interpretations -> Map Name Value -> Formula -> Maybe Bool
formulaValue interpretations values formula = case formula of
    Top -> Just True
    Bottom -> Just False
    And parts -> conjoin (map (formulaValue interpretations values) parts)
    Or parts -> not <$> conjoin (map (fmap not . formulaValue interpretations values) parts)
    Not inner -> not <$> formulaValue interpretations values inner
    Atom relation left right -> do
        leftValue <- termValue interpretations values left
        rightValue <- termValue interpretations values right
        compareValues relation leftValue rightValue
    Predicate name arguments -> do
        (_, predicate) <- Map.lookup name (interpretedPredicates interpretations)
        predicate =<< traverse (termValue interpretations values) arguments
    Forall _ _ -> Nothing
    Exists _ _ -> Nothing
  where
    conjoin results
        | Just False `elem` results = Just False
        | all (== Just True) results = Just True
        | otherwise = Nothing

{- | Compare two values. Only integers have an order. An integer and a data
value have different sorts, so their comparison is unknown.
-}
compareValues :: Relation -> Value -> Value -> Maybe Bool
compareValues relation left right = case (relation, left, right) of
    (Eq, _, _) -> sameValue left right
    (Ne, _, _) -> not <$> sameValue left right
    (Gt, IntValue x, IntValue y) -> Just (x > y)
    (Ge, IntValue x, IntValue y) -> Just (x >= y)
    (Lt, IntValue x, IntValue y) -> Just (x < y)
    (Le, IntValue x, IntValue y) -> Just (x <= y)
    _ -> Nothing
  where
    sameValue (IntValue x) (IntValue y) = Just (x == y)
    sameValue (DataValue x xs) (DataValue y ys)
        | x /= y || length xs /= length ys = Just False
        | otherwise = and <$> zipWithM sameValue xs ys
    sameValue _ _ = Nothing

{- | The value of a term, or 'Nothing' when it is unknown. A name is a nullary
application: its function interpretation, or else its value. Division and
remainder require a positive divisor. Then the Haskell, SMT-LIB, and
Euclidean operations agree.
-}
termValue :: Interpretations -> Map Name Value -> Term -> Maybe Value
termValue interpretations values term = case term of
    Lit literal -> Just (IntValue literal)
    Var name -> applied name []
    App name arguments -> applied name =<< traverse value arguments
    Neg inner -> do
        IntValue x <- value inner
        Just (IntValue (negate x))
    Add left right -> integer (+) left right
    Sub left right -> integer (-) left right
    Mul left right -> integer (*) left right
    Div left right -> division div left right
    Mod left right -> division mod left right
    Ite condition yes no -> do
        holds <- formulaValue interpretations values condition
        value (if holds then yes else no)
    Cast _ _ -> Nothing
  where
    value = termValue interpretations values
    applied name arguments = case Map.lookup name (interpretedFunctions interpretations) of
        Just function -> function arguments
        Nothing
            | null arguments -> Map.lookup name values
            | otherwise -> Nothing
    integer operation left right = do
        IntValue x <- value left
        IntValue y <- value right
        Just (IntValue (operation x y))
    division operation left right = do
        IntValue x <- value left
        IntValue y <- value right
        if y > 0 then Just (IntValue (operation x y)) else Nothing
