{-# LANGUAGE MultiWayIf #-}

{- | The edits of a term under an automaton with equality constraints.

The edits are those of "Data.CFTA.Edit": a replacement, a wrap, a context
wrap, or an unwrap at one position, which keeps the state of the position.
With equality constraints, an edit is valid only when the automaton accepts
the edited term. An equality class of a transition above the position, or of
the new root of a wrap or a context wrap, can name paths that reach the
edited part. 'constrainedEditAutomaton' moves each such class onto the edit.
Each path of a class is one of these kinds in the edited term:

* A fixed path stays outside the new material. Its subterm is a fixed
  subterm: of the term, of the old subterm below a wrap, or of the child that
  takes the place of an unwrapped subterm.
* An inside path leads into one child of the edit: the new subterm of a
  replacement, or one other child of the new root of a wrap or a context
  wrap.
* A through path stops on a node whose subterm contains the edit: a node
  above the position, or the new root of a wrap or a context wrap.
* A path into the child of a context wrap that has the hole. The hole can be
  at any place below that child, so the kind of the path depends on the edit.

Then:

* A class with a through path cannot hold after the edit. The class held for
  the term, and the edit changes the subterms at its through paths. So the
  site has no valid edit. A path that the edited term does not have has the
  same effect.
* A class with fixed paths and inside paths pins the child: its subterm at
  each inside path must be the fixed subterm. The child is restricted to a
  template with 'restrictFTA'. Two fixed subterms that differ give no valid
  edit.
* A class with only inside paths becomes an equality class on the root
  transition of the edit, with the paths moved into the children.
* A class without inside paths does not change.

The children of a replacement are the terms of the state other than the old
subterm, as in 'editAutomaton', and the pins restrict them. The other children
of a wrap or a context wrap are the terms of their states, restricted by
their pins. All of them keep the equality constraints of the automaton. An
unwrap has no child: each of its classes holds or cannot hold, so the site
has its one edit or none. The symbols are those of "Data.CFTA.Edit", so
'applyEdit' gives the edited term of an edit.

The result lists two kinds of site in 'leftOut', and leaves their edits out
instead of counting them under an assumption:

* 'Branching': the edits are exact when the transitions above a site are
  those of the run of the term. That is so when the state of each position
  above the site has one transition for the symbol of the term there.
  Otherwise another transition can accept an edited term with other
  constraints, or give the position another state.
* 'ConstrainedHole': a context wrap where a class reads the child with the
  hole, or where the new term can have a node with an equality constraint.
  Such a class or constraint reads the place of the hole, which differs from
  edit to edit. Otherwise the child with the hole is the terms with one hole
  of 'holedRows', as in 'editAutomaton'.

When the automaton is unambiguous, the result is unambiguous too. Each site
has a root symbol of its own, the children come from 'restrictFTA' and
'excludeFTA', which keep an unambiguous automaton unambiguous, and the
classes on the root transitions only remove edits. 'Data.CFTA.Sized' counts
the edits exactly. The generator import counts an acyclic result. For a
cyclic one, it reports 'Data.CFTA.Gen.CannotCountConstrainedEdges', as for
every cyclic automaton with equality constraints; use the depth-bounded
import or 'Data.CFTA.Sized'.
-}
module Data.CFTA.Edit.Constrained (
    ConstrainedState (..),
    ConstrainedEdits (..),
    LeftOut (..),
    constrainedEditAutomaton,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalities, equalityConstraint, noConstraint, residual)
import Data.CFTA.Edit (EditError (..), EditState (Free, Holed), EditSymbol (..), holedRows)
import Data.CFTA.Edit.Internal (sitePath)
import Data.CFTA.Equality.Constraint (EqConstraints (EqConstraints, EqContradiction), mkEqConstraints, unPathEClass)
import Data.CFTA.Index (ChildIndex (..), TransitionIndex (..))
import Data.CFTA.Path (Path, path, unPath)
import Data.CFTA.Template (Template (..), excludeFTA, restrictFTA)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A state of a constrained edit automaton.
data ConstrainedState
    = -- | The initial state: one transition for each edit site.
      ConstrainedRoot
    | -- | A state of one child of an edit: the site, the child index, and the state number.
      Child !Int !Int !Int
    deriving (Eq, Ord, Show)

-- | The automaton of the valid edits, and the sites that it leaves out.
data ConstrainedEdits symbol = ConstrainedEdits
    { edits :: !(FTA.PlainFTA ConstrainedState (EditSymbol symbol))
    -- ^ The valid edits of the sites that are not left out.
    , leftOut :: ![(EditSymbol symbol, LeftOut)]
    -- ^ The sites whose edits the result leaves out, with the reason, in path order.
    }

-- | Why the result leaves the edits of a site out.
data LeftOut
    = -- | A state above the site has two transitions for the symbol of the term there.
      Branching
    | {- | A context wrap whose hole an equality class reads, or whose new term
      can have a node with an equality constraint.
      -}
      ConstrainedHole
    deriving (Eq, Show)

-- | What the edited term has at a path of an equality class.
data Kind symbol
    = -- | A fixed subterm.
      Fixed !(Term symbol)
    | -- | A node whose subterm contains the edit.
      Through
    | -- | A path into a child of the edit: the child index and the path in it.
      Inside !Int ![Int]
    | -- | A path into the child of a context wrap that has the hole.
      IntoHole
    | -- | The edited term has no node at the path.
      Missing

-- | A child of an edit.
data ChildOf state symbol
    = -- | A term of the state, without the old subterm when there is one.
      Slot !state !(Maybe (Term symbol))
    | -- | A term of the state with one hole, whose state is one of the set.
      HoledSlot !(Set.Set state) !state

-- | What one equality class asks of an edit.
data Outcome symbol
    = -- | The class cannot hold after the edit.
      Impossible
    | -- | The class reads the child of a context wrap that has the hole.
      ReadsHole
    | -- | The class holds when the children have these pins and the root this class.
      Holds ![(Int, [Int], Term symbol)] !(Maybe [Path])

{- | The valid edits of a term under an automaton with equality constraints.

A guard beyond equality constraints gives 'ConstrainedAutomaton'. The term
must have exactly one run, as for 'editAutomaton'.
-}
constrainedEditAutomaton ::
    (Ord state, Ord symbol) => FTA.PlainFTA state symbol -> Term symbol -> Either EditError (ConstrainedEdits symbol)
constrainedEditAutomaton automaton given
    | any (any (residual . FTA.transitionConstraint)) (FTA.transitionTable automaton) = Left ConstrainedAutomaton
    | otherwise = case take 2 $ runsFrom (FTA.initialState automaton) given of
        [] -> Left NotAccepted
        [run] -> Right $ fromRun run
        _ -> Left SeveralRuns
  where
    rows = Map.toList $ FTA.transitionTable automaton
    rootedAt state =
        fromRight (error "Data.CFTA.Edit.Constrained: an automaton with another initial state is not valid") $
            FTA.mkFTA state rows
    acceptedAt state = FTA.accepts (rootedAt state)

    -- The runs from a state on a term: the state and the transition at each position.
    runsFrom state term@(Term.Node symbol children) =
        [ Map.insert [] (state, transition) $
            Map.unions [Map.mapKeys (index :) childRun | (index, childRun) <- zip [0 ..] childRuns]
        | transition <- FTA.transitionsFrom automaton state
        , FTA.transitionSymbol transition == symbol
        , length (FTA.transitionChildren transition) == length children
        , holds term (FTA.transitionConstraint transition)
        , childRuns <- traverse (uncurry runsFrom) (zip (FTA.transitionChildren transition) children)
        ]
    holds term constraint = case equalities constraint of
        EqContradiction -> False
        EqConstraints classes -> all (allEqual . map (subtermAtMaybe term . unIndexes) . Set.toList . unPathEClass) classes
    allEqual values = case values of
        Just first : rest -> all (== Just first) rest
        _ -> False

    -- The states whose terms can have a node with an equality constraint.
    constrainedBelow = Set.fromList [state | state <- FTA.states automaton, any constrained (reachable state)]
    constrained state = any ((/= noConstraint) . FTA.transitionConstraint) (FTA.transitionsFrom automaton state)
    reachable state = go Set.empty [state]
      where
        go seen [] = Set.toList seen
        go seen (next : pending)
            | Set.member next seen = go seen pending
            | otherwise =
                go (Set.insert next seen) (concatMap FTA.transitionChildren (FTA.transitionsFrom automaton next) <> pending)

    fromRun run =
        ConstrainedEdits
            { edits =
                FTA.trim
                    $ fromRight (error "Data.CFTA.Edit.Constrained: the edit automaton of a ranked automaton is not ranked")
                    $ FTA.mkFTA ConstrainedRoot
                    $ (ConstrainedRoot, [root | (_, Right (Just (root, _))) <- built])
                        : concat [children | (_, Right (Just (_, children))) <- built]
            , leftOut = [(symbol, reason) | (symbol, Left reason) <- built]
            }
      where
        positions = [(at, state, subtermAt given at) | (at, (state, _)) <- Map.toList run]
        sites =
            concat
                [ replaceSite at state old : unwrapSites at state old <> wrapSites at state old <> contextSites at state old
                | (at, state, old) <- positions
                ]
        built = [(symbol, site number symbol children constraints) | (number, (symbol, children, constraints)) <- zip [0 ..] sites]
        -- The site at a position is branching when a state above it has another transition for the symbol there.
        branching at =
            or
                [ length [() | other <- FTA.transitionsFrom automaton state, sameShape other transition] > 1
                | (prefix, (state, transition)) <- Map.toList run
                , prefix /= at
                , prefix `isPrefixOf` at
                ]
        sameShape one other =
            FTA.transitionSymbol one == FTA.transitionSymbol other
                && length (FTA.transitionChildren one) == length (FTA.transitionChildren other)
        above at = [(prefix, transition) | (prefix, (_, transition)) <- Map.toList run, prefix /= at, prefix `isPrefixOf` at]
        -- The classes of the transitions above the position, with the kind of the paths below it.
        aboveConstraints at inNew = [(FTA.transitionConstraint transition, kindAbove at prefix inNew) | (prefix, transition) <- above at]

        -- A replacement: one child, the terms of the state other than the old subterm.
        replaceSite at state old = (ReplaceAt (toPath at), [Slot state (Just old)], aboveConstraints at (Inside 0))
        -- The unwraps of a position: no child; the paths below it lead into the child that takes its place.
        unwrapSites at state (Term.Node _ grandchildren) =
            [ (UnwrapAt (toPath at) (ChildIndex index), [], aboveConstraints at (maybe Missing Fixed . subtermAtMaybe grandchild))
            | (index, grandchild) <- zip [0 ..] grandchildren
            , acceptedAt state grandchild
            ]
        -- The wraps of a position: one for each transition of its state and each child whose state accepts the old subterm.
        wrapSites at state old =
            [ ( WrapAt (toPath at) (FTA.transitionSymbol transition) (TransitionIndex index) (ChildIndex hole)
              , [Slot sibling Nothing | (other, sibling) <- zip [0 ..] children, other /= hole]
              , (FTA.transitionConstraint transition, inNew) : aboveConstraints at inNew
              )
            | (index, transition) <- zip [0 ..] (FTA.transitionsFrom automaton state)
            , let children = FTA.transitionChildren transition
            , (hole, child) <- zip [0 ..] children
            , acceptedAt child old
            , let inNew relative = case relative of
                    [] -> Through
                    other : rest
                        | other == hole -> maybe Missing Fixed $ subtermAtMaybe old rest
                        | other < length children -> Inside (if other < hole then other else other - 1) rest
                        | otherwise -> Missing
            ]
        -- The context wraps of a position: one for each transition of its state and each child that has the hole.
        contextSites at state old =
            [ ( ContextAt (toPath at) (FTA.transitionSymbol transition) (TransitionIndex index) (ChildIndex hole)
              , [if other == hole then HoledSlot holeStates child else Slot child Nothing | (other, child) <- zip [0 ..] children]
              , (FTA.transitionConstraint transition, inNew) : aboveConstraints at inNew
              )
            | let holeStates = Set.fromList [candidate | candidate <- FTA.states automaton, acceptedAt candidate old]
            , (index, transition) <- zip [0 ..] (FTA.transitionsFrom automaton state)
            , let children = FTA.transitionChildren transition
            , hole <- [0 .. length children - 1]
            , let inNew relative = case relative of
                    [] -> Through
                    other : rest
                        | other == hole -> IntoHole
                        | other < length children -> Inside other rest
                        | otherwise -> Missing
            ]

        {- The root transition and the child rows of a site: 'Left' for a site
        that the result leaves out, and 'Nothing' for a site without a valid
        edit.
        -}
        site number symbol children constraints
            | branching (unIndexes $ sitePath symbol) = Left Branching
            | any (null . ($ Hole)) childRows' = Right Nothing
            | any isImpossible outcomes = Right Nothing
            | any readsHole outcomes || any constrainedHole children = Left ConstrainedHole
            | otherwise = Right $ do
                templates <-
                    mapM (\child -> pinTemplate [(at, value) | (child', at, value) <- pins, child' == child]) [0 .. length children - 1]
                let pinned = zipWith ($) childRows' templates
                if any null pinned
                    then Nothing
                    else
                        pure (FTA.Transition symbol [Child number child 0 | child <- [0 .. length children - 1]] rootConstraint, concat pinned)
          where
            outcomes = [classOutcome kind paths | (constraint, kind) <- constraints, paths <- classesOf constraint]
            pins = concat [pins' | Holds pins' _ <- outcomes]
            classes = [shifted | Holds _ (Just shifted) <- outcomes]
            rootConstraint
                | null classes = noConstraint
                | otherwise = equalityConstraint $ mkEqConstraints classes
            -- The rows of each child, for its template of pins.
            childRows' = [childRows number index child | (index, child) <- zip [0 ..] children]
            isImpossible outcome = case outcome of
                Impossible -> True
                _ -> False
            readsHole outcome = case outcome of
                ReadsHole -> True
                _ -> False
            constrainedHole child = case child of
                HoledSlot _ state -> state `Set.member` constrainedBelow
                Slot _ _ -> False

        -- The kind of a path of a transition above the position.
        kindAbove at prefix inNew relative
            | relative `isPrefixOf` below && relative /= below = Through
            | below `isPrefixOf` relative = inNew (drop (length below) relative)
            | otherwise = maybe Missing Fixed $ subtermAtMaybe given (prefix <> relative)
          where
            below = drop (length prefix) at

        {- The rows of one child for a template of pins: the state restricted to
        the pins, without the old subterm for a replacement, or the terms with
        one hole. A child without terms has no rows.
        -}
        childRows number index child template = case child of
            Slot state exclusion ->
                let restricted = restrictFTA template (rootedAt state)
                 in case exclusion of
                        Just old -> tagged number index Material $ FTA.trim $ excludeFTA [exact old] restricted
                        Nothing -> tagged number index Material $ FTA.trim restricted
            HoledSlot holeStates state ->
                tagged number index id
                    $ FTA.trim
                    $ fromRight (error "Data.CFTA.Edit.Constrained: the terms with a hole of a ranked automaton are not ranked")
                    $ FTA.mkFTA (Holed holeStates state)
                    $ holedRows automaton holeStates
                        <> [ ( Free free
                             , [FTA.Transition (Material label) (map Free next) constraint | FTA.Transition label next constraint <- transitions]
                             )
                           | (free, transitions) <- rows
                           ]

    -- What one class asks of an edit.
    classOutcome kind paths =
        let kinds = map kind paths
            fixed = nubOrd [value | Fixed value <- kinds]
            inside = [(child, at) | Inside child at <- kinds]
         in if
                | or [True | Through <- kinds] || or [True | Missing <- kinds] || length fixed > 1 -> Impossible
                | or [True | IntoHole <- kinds] -> ReadsHole
                | otherwise -> case fixed of
                    [value] -> Holds [(child, at, value) | (child, at) <- inside] Nothing
                    _
                        | length inside >= 2 -> Holds [] (Just [toPath (child : at) | (child, at) <- inside])
                        | otherwise -> Holds [] Nothing
    classesOf constraint = case equalities constraint of
        EqConstraints classes -> [map unIndexes $ Set.toList $ unPathEClass eclass | eclass <- classes]
        EqContradiction -> [[[], [0]]]

{- | The rows of a trimmed automaton of a child of a site, with the states
tagged by the site and the child, or none when the child has no term.
-}
tagged ::
    (Ord state) =>
    Int ->
    Int ->
    (label -> EditSymbol symbol) ->
    FTA.FTA state label Constraint ->
    [(ConstrainedState, [FTA.Transition ConstrainedState (EditSymbol symbol) Constraint])]
tagged number index relabel automaton
    | null (FTA.transitionsFrom automaton (FTA.initialState automaton)) = []
    | otherwise =
        [ ( Child number index here
          , [ FTA.Transition (relabel label) (map (Child number index) next) constraint
            | FTA.Transition label next constraint <- transitions
            ]
          )
        | (here, transitions) <- Map.toList $ FTA.transitionTable $ renumber automaton
        ]

{- | The template of the pins of a child: each pinned path holds its subterm.
'Nothing' when two pins disagree.
-}
pinTemplate :: (Eq symbol) => [([Int], Term symbol)] -> Maybe (Template symbol)
pinTemplate pins = case [value | ([], value) <- pins] of
    value : others
        | all (== value) others && and [subtermAtMaybe value at == Just inner | (at, inner) <- pins] -> Just $ exact value
        | otherwise -> Nothing
    []
        | null pins -> Just Hole
        | otherwise ->
            AnyPrefix
                <$> mapM
                    (\index -> pinTemplate [(rest, value) | (first : rest, value) <- pins, first == index])
                    [0 .. maximum [index | (index : _, _) <- pins]]

-- | The template that matches exactly the term.
exact :: Term symbol -> Template symbol
exact (Term.Node symbol children) = TemplateNode symbol (map exact children)

-- | The automaton with its states numbered from zero, the initial state first.
renumber :: (Ord state) => FTA.FTA state symbol Constraint -> FTA.FTA Int symbol Constraint
renumber automaton = FTA.mapStates (numbers Map.!) automaton
  where
    initial = FTA.initialState automaton
    numbers = Map.fromList $ zip (initial : filter (/= initial) (FTA.states automaton)) [0 ..]

-- | The subterm at a position, which the term has.
subtermAt :: Term symbol -> [Int] -> Term symbol
subtermAt term at = fromMaybe (error "Data.CFTA.Edit.Constrained: a position of the run is not in the term") $ subtermAtMaybe term at

-- | The subterm at a position.
subtermAtMaybe :: Term symbol -> [Int] -> Maybe (Term symbol)
subtermAtMaybe term [] = Just term
subtermAtMaybe (Term.Node _ children) (index : rest) = case drop index children of
    child : _ -> subtermAtMaybe child rest
    [] -> Nothing

-- | A path from child indexes.
toPath :: [Int] -> Path
toPath = path . map ChildIndex

-- | The child indexes of a path.
unIndexes :: Path -> [Int]
unIndexes = map (\(ChildIndex index) -> index) . unPath
