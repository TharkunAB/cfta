{- | Restriction and exclusion with templates that repeat a name.

A template with a repeated name (a non-linear template) matches a term when
the term matches the template's 'skeleton' and holds equal subterms at the
paths of each name ('repeatedNames'). The set of these terms is not a regular
tree language in general. So the results here carry the equalities as
transition constraints:

* 'restrictNamedFTA' puts positive 'Same' atoms on the root transitions.
  This is an equality constraint, as in an ECTA.
* 'excludeNamedFTA' and 'excludeNamedAnywhereFTA' put the guard
  @Not (And [Same p q, ...])@ on each transition whose term matches the
  skeleton of a non-linear template at its root.

The exclusions apply the linear templates with 'excludeFTA' and
'excludeAnywhereFTA', unchanged. Then they take the product with a
deterministic bottom-up automaton whose state is the set of skeleton parts
that a term matches. The pattern automaton is deterministic, so an
unambiguous input gives an unambiguous result.

A guard of 'Same', 'Not', and 'And' has an inclusion-exclusion form
('Data.CFTA.Constraint.indicators'), so a counter of equality languages can
count the result without enumeration.
-}
module Data.CFTA.Template.Named (
    PatternState,
    restrictNamedFTA,
    excludeNamedFTA,
    excludeNamedAnywhereFTA,
) where

import Data.Either (fromRight)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.CFTA (FTA, Transition (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, Guard (And, Not, Same), conjoinConstraints, semanticConstraint)
import Data.CFTA.Index (Arity (..))
import Data.CFTA.Template (
    Obligation,
    Template (..),
    childTemplates,
    excludeAnywhereFTA,
    excludeFTA,
    repeatedNames,
    restrictFTA,
    skeleton,
 )

{- | A state of a named exclusion: 'Nothing' for the root, or a state of the
input with the set of skeleton parts that its terms match.
-}
type PatternState state symbol = Maybe (state, Set (Template symbol))

{- | Keep exactly the terms of an automaton that match a template, also a
template with a repeated name.

The result is 'restrictFTA' of the skeleton, with the equalities of the
repeated names conjoined to the constraints of the root transitions. A
linear template gives no equality, so the result is 'restrictFTA'.
-}
restrictNamedFTA ::
    (Ord state, Ord symbol) =>
    Template symbol -> FTA state symbol Constraint -> FTA (state, Template symbol) symbol Constraint
restrictNamedFTA template automaton
    | null equalities = restricted
    | otherwise =
        -- The rows come from a ranked automaton, so validation cannot fail.
        fromRight (error "restrictNamedFTA: the restriction of a ranked automaton is ranked")
            $ FTA.mkFTA root
            $ Map.toList
            $ Map.adjust (map withEqualities) root (FTA.transitionTable restricted)
  where
    restricted = restrictFTA (skeleton template) automaton
    -- A child state holds a proper part of the skeleton, so only the root has this state.
    root = FTA.initialState restricted
    equalities = [Same first other | (_, first : others) <- repeatedNames template, other <- others]
    withEqualities transition =
        transition
            { transitionConstraint = conjoinConstraints (transitionConstraint transition) (semanticConstraint (And equalities))
            }

{- | Keep exactly the terms of an automaton that match none of the templates
at the root, as 'Data.CFTA.Template.matchesNone' says. The templates can
repeat names.

'excludeFTA' removes the linear templates. A root transition whose term
matches the skeleton of a non-linear template gets the guard that the
equalities of that template do not all hold.
-}
excludeNamedFTA ::
    (Ord state, Ord symbol) =>
    [Template symbol] ->
    FTA state symbol Constraint ->
    FTA (PatternState (state, Obligation symbol) symbol) symbol Constraint
excludeNamedFTA templates = guardMatches False nonLinear . excludeFTA linear
  where
    (nonLinear, linear) = splitLinear templates

{- | Keep exactly the terms of an automaton of which no subterm matches one
of the templates, as 'Data.CFTA.Template.matchesNowhere' says. The templates
can repeat names.

'excludeAnywhereFTA' removes the linear templates. Each transition whose
term matches the skeleton of a non-linear template gets the guard that the
equalities of that template do not all hold.
-}
excludeNamedAnywhereFTA ::
    (Ord state, Ord symbol) =>
    [Template symbol] ->
    FTA state symbol Constraint ->
    FTA (PatternState (state, Obligation symbol) symbol) symbol Constraint
excludeNamedAnywhereFTA templates = guardMatches True nonLinear . excludeAnywhereFTA linear
  where
    (nonLinear, linear) = splitLinear templates

-- | The templates with a repeated name, and the other templates.
splitLinear :: [Template symbol] -> ([Template symbol], [Template symbol])
splitLinear templates =
    ( [template | template <- templates, not (null (repeatedNames template))]
    , [template | template <- templates, null (repeatedNames template)]
    )

{- | The product of an automaton with the pattern automaton of the skeletons
of non-linear templates. A transition whose term matches the skeleton of
such a template gets its guard: at each state when the first argument is
'True', and at the root only otherwise.

The pattern state of a term is the set of skeleton parts that it matches.
'Hole' is in each set. The sets that the terms of each input state can have
are a least fixed point. A new root state has a copy of the rows of each
pair of the initial state and such a set.
-}
guardMatches ::
    (Ord state, Ord symbol) =>
    Bool ->
    [Template symbol] ->
    FTA state symbol Constraint ->
    FTA (PatternState state symbol) symbol Constraint
guardMatches everywhere templates automaton =
    -- The rows come from a ranked automaton, so validation cannot fail.
    fromRight (error "guardMatches: the product with a ranked automaton is ranked") $
        FTA.mkFTA Nothing (rootRows <> [(Just key, [transition]) | (key, transition, _) <- rows])
  where
    shapes = [(skeleton template, guardOf template) | template <- templates]
    guardOf template = Not (And [Same first other | (_, first : others) <- repeatedNames template, other <- others])
    parts = Set.toList (Set.fromList (Hole : concatMap (subtemplates . fst) shapes))
    subtemplates template = template : concatMap subtemplates (directParts template)
    directParts template = case template of
        AnyNode children -> children
        TemplateNode _ children -> children
        AnyPrefix children -> children
        TemplatePrefix _ children -> children
        _ -> []

    -- The pattern state of a term with this symbol and children with these pattern states.
    step symbol childStates =
        Set.fromList
            [ part
            | part <- parts
            , Just childParts <- [childTemplates part symbol (Arity (length childStates))]
            , and (zipWith Set.member childParts childStates)
            ]

    -- The pattern states that the terms of each input state can have.
    possible = grow Map.empty
    grow known
        | next == known = known
        | otherwise = grow next
      where
        next =
            Map.fromListWith
                (<>)
                [ (state, Set.singleton (step (transitionSymbol transition) childStates))
                | (state, transitions) <- Map.toList (FTA.transitionTable automaton)
                , transition <- transitions
                , childStates <- mapM (\child -> Set.toList (Map.findWithDefault Set.empty child known)) (transitionChildren transition)
                ]

    -- Each product transition with its state and whether it carries guards.
    rows =
        [ ((state, matched), transition{transitionChildren = map Just children, transitionConstraint = constraint}, guarded)
        | (state, transitions) <- Map.toList (FTA.transitionTable automaton)
        , transition <- transitions
        , childStates <-
            mapM (\child -> Set.toList (Map.findWithDefault Set.empty child possible)) (transitionChildren transition)
        , let matched = step (transitionSymbol transition) childStates
              children = zip (transitionChildren transition) childStates
              guards = [semanticConstraint guard | (shape, guard) <- shapes, Set.member shape matched]
              guarded = foldr (flip conjoinConstraints) (transitionConstraint transition) guards
              constraint = if everywhere then guarded else transitionConstraint transition
        ]
    rootRows =
        [ (Nothing, [transition{transitionConstraint = guarded}])
        | ((state, _), transition, guarded) <- rows
        , state == FTA.initialState automaton
        ]
