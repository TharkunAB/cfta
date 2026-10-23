{- | Checks that a later automaton is a definitional extension of an earlier
automaton, with counterexample terms.

In a definitional extension, the later automaton adds new constructors, and a
template lowering ("Data.CFTA.Lowering") gives each new constructor an
expansion in the earlier automaton. The two automata share their states.
'checkExtension' reports each reason why the later automaton is not such an
extension:

* Another initial state ('ChangedStart').
* A production of the earlier automaton that the later automaton does not
  have at the same state ('LostProduction'). The old productions must stay.
* A constructor of the earlier automaton that the lowering expands
  ('LoweredOldConstructor').
* A production of a new constructor with another number of children than its
  expansion ('NotTotal'). The terms through it do not lower.
* A production whose terms 'Lowering.checkLowering' does not show to lower
  into the earlier automaton at its state ('RejectedLowering' with a
  counterexample, or 'UnprovedLowering').

An empty report shows three facts. Every term of the later automaton lowers,
and its lowering is a term of the earlier automaton ('Lowering.checkLowering'
shows this by induction on terms). Every term of the earlier automaton is a
term of the later automaton, because the initial state and each production
stay. And
every old term keeps its meaning: the lowering has no expansion for an old
constructor, so the lowering of an old term is that term.

A counterexample is a term of the automaton from its initial state that uses
the production. Its other positions have the smallest terms of their states,
the first terms of the smallest size class in the order of "Data.CFTA.Sized",
in a context that a breadth-first search finds. Thus a counterexample is
small, but not always the smallest. In the later automaton, the context and
the smallest terms use only the productions that the check does not report,
so only the reported production can make the counterexample fail.

The check handles automata without constraints, as 'Lowering.lift' does. A
transition with a constraint is 'Lowering.ConstrainedTransition'.
-}
module Data.CFTA.Extension (
    Production,
    ExtensionError (..),
    checkExtension,
) where

import Control.Monad (forM_, unless)
import Data.Either (fromRight)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Gen.Internal.Table (minimumSizes)
import Data.CFTA.Lowering (Lowering, LoweringError (ArityMismatch, ConstrainedTransition))
import qualified Data.CFTA.Lowering as Lowering
import Data.CFTA.Sized (sized, termsOfSize)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A production of an automaton: a symbol, its child states, and its constraint.
type Production state = FTA.Transition state Symbol Constraint

-- | A reason why the later automaton is not a definitional extension of the earlier automaton.
data ExtensionError state
    = -- | The initial state of the earlier automaton and the other initial state of the later automaton.
      ChangedStart !state !state
    | {- | A production of the earlier automaton that the later automaton does
      not have at the same state, and a term of the earlier automaton that
      uses it. 'Nothing' when no term of the earlier automaton uses it.
      -}
      LostProduction !state !(Production state) !(Maybe (Term Symbol))
    | -- | A constructor of the earlier automaton that the lowering expands. Old terms with it change their meaning.
      LoweredOldConstructor !Symbol
    | {- | A production of a new constructor with another number of children
      than its expansion, and a term of the later automaton that uses it. The
      term does not lower. 'Nothing' when no term uses the production.
      -}
      NotTotal !state !(Production state) !(Maybe (Term Symbol))
    | {- | A production that does not lower into the earlier automaton at its
      state: a term of the later automaton that uses it, and the lowering of
      that term, which the earlier automaton does not accept.
      -}
      RejectedLowering !state !(Production state) !(Term Symbol) !(Term Symbol)
    | {- | A production that 'Lowering.checkLowering' does not show to lower,
      with a term of the later automaton that uses it and the lowering of that
      term, which the earlier automaton accepts. No counterexample is known.
      'Nothing' when no term of the later automaton uses the production.
      -}
      UnprovedLowering !state !(Production state) !(Maybe (Term Symbol, Term Symbol))
    deriving (Eq, Show)

{- | The reasons why the later automaton is not a definitional extension of
the earlier automaton by the lowering: another initial state, the lost
productions in state order,
then the lowered old constructors, then the productions of the later
automaton that do not lower, in state order. An empty list when it is a
definitional extension.
-}
checkExtension ::
    (Ord state) =>
    Lowering Symbol ->
    FTA.PlainFTA state Symbol ->
    FTA.PlainFTA state Symbol ->
    Either (LoweringError state Symbol) [ExtensionError state]
checkExtension lowering earlier later = do
    forM_ [earlier, later] $ \automaton ->
        forM_ (Map.toList $ FTA.transitionTable automaton) $ \(state, transitions) ->
            forM_ transitions $ \transition ->
                unless (FTA.transitionConstraint transition == noConstraint)
                    $ Left
                    $ ConstrainedTransition state (FTA.transitionSymbol transition)
    pure $ start <> lost <> loweredOld <> map failure failures
  where
    start =
        [ChangedStart (FTA.initialState earlier) (FTA.initialState later) | FTA.initialState earlier /= FTA.initialState later]
    oldWitness = witnesses earlier
    newWitness = witnesses proved
    lost =
        [ LostProduction state production (oldWitness state production)
        | (state, productions) <- Map.toList $ FTA.transitionTable earlier
        , production <- productions
        , production `notElem` Map.findWithDefault [] state (FTA.transitionTable later)
        ]
    oldConstructors =
        Set.fromList
            [FTA.transitionSymbol production | productions <- Map.elems $ FTA.transitionTable earlier, production <- productions]
    loweredOld = [LoweredOldConstructor symbol | symbol <- Lowering.newConstructors lowering, Set.member symbol oldConstructors]
    failures = Lowering.checkProductions lowering earlier later
    -- The later automaton without the reported productions, for the contexts and the smallest terms.
    proved =
        fromRight (error "cfta-generator bug: removing productions gave an invalid automaton") $
            FTA.replaceRows
                ( Map.mapWithKey
                    (\state productions -> Just [production | production <- productions, (state, production) `notElem` reported])
                    (FTA.transitionTable later)
                )
                later
    reported = [(state, production) | (state, production, _) <- failures]
    failure (state, production, reason) = case reason of
        ArityMismatch{} -> NotTotal state production (newWitness state production)
        _ -> case newWitness state production of
            Nothing -> UnprovedLowering state production Nothing
            Just term -> case Lowering.lower lowering term of
                Just lowered
                    | FTA.accepts earlier lowered -> UnprovedLowering state production (Just (term, lowered))
                    | otherwise -> RejectedLowering state production term lowered
                Nothing -> error "cfta-generator bug: a counterexample through proved productions does not lower"

{- | A term of the automaton from its initial state that uses a production at
a state. The production need not be in the automaton. 'Nothing' when the
automaton reaches no context at the state, or when a child state has no term.
The smallest terms and the contexts are computed once for the automaton.
-}
witnesses :: (Ord state) => FTA.PlainFTA state Symbol -> state -> Production state -> Maybe (Term Symbol)
witnesses automaton = \state production -> do
    context <- Map.lookup state reached
    children <- traverse (`Map.lookup` smallest) (FTA.transitionChildren production)
    pure $ context $ Term.Node (FTA.transitionSymbol production) children
  where
    smallest = smallestTerms automaton
    reached = contexts automaton smallest

{- | The smallest term of each state that has a term: the first term of its
smallest size class in the order of "Data.CFTA.Sized".
-}
smallestTerms :: (Ord state) => FTA.PlainFTA state Symbol -> Map state (Term Symbol)
smallestTerms automaton = Map.mapMaybeWithKey first $ minimumSizes $ FTA.transitionTable automaton
  where
    first state size = case termsOfSize (classes state) size of
        term : _ -> Just term
        [] -> Nothing
    classes state = case FTA.mkFTA state $ Map.toList $ FTA.transitionTable automaton of
        Left _ -> error "cfta-generator bug: a state of a valid automaton is not a valid initial state"
        Right rooted ->
            either (error . ("cfta-generator bug: the size classes of an automaton without constraints: " <>) . show) id $
                sized rooted

{- | For each state that a term of the automaton reaches, a context from the
initial state: a term with one hole at that state. The other positions have
the given smallest terms. The search is breadth first, so a context is shallow.
-}
contexts ::
    (Ord state) => FTA.PlainFTA state Symbol -> Map state (Term Symbol) -> Map state (Term Symbol -> Term Symbol)
contexts automaton smallest = search (Map.singleton initial id) [initial]
  where
    initial = FTA.initialState automaton
    search found [] = found
    search found (state : queue) = search found' (queue <> added)
      where
        context = found Map.! state
        steps =
            [ (child, \hole -> context $ Term.Node symbol $ take index others <> [hole] <> drop index others)
            | FTA.Transition symbol children _ <- Map.findWithDefault [] state $ FTA.transitionTable automaton
            , (index, child) <- zip [0 ..] children
            , Just others <- [traverse (`Map.lookup` smallest) (take index children <> drop (index + 1) children)]
            ]
        (found', added) = foldl' visit (found, []) steps
        visit (known, new) (child, plug)
            | Map.member child known = (known, new)
            | otherwise = (Map.insert child plug known, new <> [child])
