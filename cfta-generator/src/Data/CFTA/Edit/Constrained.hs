{-# LANGUAGE MultiWayIf #-}

{- | The edits of a term under an automaton with equality constraints or
guards.

The edits are those of "Data.CFTA.Edit": a replacement, a wrap, a context
wrap, or an unwrap at one position, which keeps the state of the position.
With constraints, an edit is valid only when the automaton accepts the edited
term. A constraint of a transition above the position, or of the new root of
a wrap or a context wrap, can name paths that reach the edited part.
'constrainedEditAutomaton' and 'guardedEditAutomaton' move each such
constraint onto the edit. Each path of a constraint is one of these kinds in
the edited term:

* A fixed path stays outside the new material. Its subterm is a fixed
  subterm: of the term, of the old subterm below a wrap, or of the child that
  takes the place of an unwrapped subterm.
* An inside path leads into one child of the edit: the new subterm of a
  replacement, or one other child of the new root of a wrap or a context
  wrap.
* A through path stops on a node whose subterm contains the edit: a node
  above the position, or the new root of a wrap or a context wrap. The symbol
  of the node does not change.
* A path into the child of a context wrap that has the hole. The hole can be
  at any place below that child, so the kind of the path depends on the edit.

For an equality class:

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

An equality atom ('Same') between two different paths at the top of a guard
is an equality class. The other atoms of a guard read the symbols at their
paths, and the symbol at a fixed or a through path does not change:

* An atom without inside paths has one value for the site. The solver
  decides it once, from the observations of the edited term. Yes keeps the
  site, and No gives the site no valid edit.
* An atom with only inside paths moves onto the root transition of the edit,
  with the paths moved into the children. The count decides it on each edit.
* An atom with fixed or through paths and inside paths has a value that
  depends on the edit and on the fixed subterms together. The guard language
  cannot write the fixed values into a guard, so the site is left out.

The negations, conjunctions, and disjunctions of a guard combine the atoms as
the evaluator of "Data.CFTA.Refinement.Evaluate" does. A 'Not' above an atom
is decided with the atom, so a negation holds only when the refinements
refute the formula.

The children of a replacement are the terms of the state other than the old
subterm, as in 'editAutomaton', and the pins restrict them. The other children
of a wrap or a context wrap are the terms of their states, restricted by
their pins. All of them keep the constraints of the automaton. An unwrap has
no child: each of its classes and atoms holds or does not, so the site has
its one edit or none. The symbols are those of "Data.CFTA.Edit", so
'applyEdit' gives the edited term of an edit.

The result lists the sites in 'leftOut' whose edits it cannot give exactly,
with the reason, and leaves their edits out instead of counting them under an
assumption:

* 'Branching': the edits are exact when the transitions above a site are
  those of the run of the term. That is so when the state of each position
  above the site has one transition for the symbol of the term there.
  Otherwise another transition can accept an edited term with other
  constraints, or give the position another state.
* 'ConstrainedHole': a context wrap where a class or an atom reads the child
  with the hole, or where the new term can have a node with a constraint.
  Such a constraint reads the place of the hole, which differs from edit to
  edit. Otherwise the child with the hole is the terms with one hole of
  'holedRows', as in 'editAutomaton'.
* 'MixedGuard': an atom with fixed or through paths and inside paths.
* 'GuardSubstitution': a guard with a substitution.
* 'UndecidedGuard': the solver does not decide an atom without inside paths,
  or whether a state accepts the fixed part of the site: the child of an
  unwrap, the old subterm at the hole of a wrap, or the old subterm of a
  context wrap.

When the automaton is unambiguous, the result is unambiguous too. Each site
has a root symbol of its own, the children come from 'restrictFTA' and
'excludeFTA', which keep an unambiguous automaton unambiguous, and the
constraints on the root transitions only remove edits. 'Data.CFTA.Sized'
counts the edits of an automaton with equality constraints exactly. The
generator import counts an acyclic result. For a cyclic one, it reports
'Data.CFTA.Gen.CannotCountConstrainedEdges', as for every cyclic automaton
with equality constraints; use the depth-bounded import or 'Data.CFTA.Sized'.
With guards, 'Data.CFTA.Sized.sizedUpTo' counts the edits up to a size, over
the symbols of 'plainSymbols'.
-}
module Data.CFTA.Edit.Constrained (
    ConstrainedState (..),
    ConstrainedEdits (..),
    LeftOut (..),
    GuardedEditError (..),
    constrainedEditAutomaton,
    guardedEditAutomaton,
    plainSymbols,
) where

import Control.Monad (forM, zipWithM)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Functor.Identity (runIdentity)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isNothing)
import qualified Data.Set as Set
import Data.String (fromString)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint (..),
    Guard (..),
    conjoin,
    equalitiesHold,
    equalityConstraint,
    noConstraint,
    residual,
 )
import Data.CFTA.Edit (Edit, EditError (..), EditState (Free, Holed), EditSymbol (..), holedRows)
import Data.CFTA.Edit.Internal (sitePath)
import Data.CFTA.Equality.Constraint (EqConstraints (EqConstraints, EqContradiction), mkEqConstraints, unPathEClass)
import Data.CFTA.Index (ChildIndex (..), TransitionIndex (..))
import Data.CFTA.Path (Path, path, unPath)
import Data.CFTA.Refinement.Evaluate (
    Leafness (..),
    Observed (..),
    evaluateConstraint,
    evaluateGuardWithShape,
    leafnessOf,
 )
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))
import Data.CFTA.Symbol (Symbol)
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

{- | Why the result leaves the edits of a site out. When a site has more than
one reason, the result gives the first in this order.
-}
data LeftOut
    = -- | A state above the site has two transitions for the symbol of the term there.
      Branching
    | {- | A context wrap whose hole a constraint reads, or whose new term
      can have a node with a constraint.
      -}
      ConstrainedHole
    | -- | A guard atom reads fixed or through paths and the new material together.
      MixedGuard
    | -- | A guard has a substitution.
      GuardSubstitution
    | -- | The solver does not decide a guard atom on fixed or through paths, or the fixed part of the site.
      UndecidedGuard
    deriving (Eq, Ord, Show)

-- | Why a term has no edit automaton under guards.
data GuardedEditError
    = -- | The automaton does not accept the term ('NotAccepted'), or it has two runs for it that hold ('SeveralRuns').
      EditFailure !EditError
    | -- | The solver does not decide whether the automaton accepts the term.
      UndecidedTerm
    | {- | The automaton accepts the term with one run, and the solver does
      not decide whether another run holds.
      -}
      UndecidedRuns
    deriving (Eq, Show)

-- | What the edited term has at a path of a constraint.
data Kind symbol
    = -- | A fixed subterm.
      Fixed !(Term symbol)
    | -- | A node whose subterm contains the edit, with its symbol.
      Through !symbol
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
      HoldsWhen ![(Int, [Int], Term symbol)] !(Maybe [Path])

-- | What a guard asks of an edit.
data Moved
    = -- | The guard has one value for every edit of the site.
      Decided !Bool
    | -- | The result leaves the site out for this reason.
      Apart !LeftOut
    | -- | The guard on the root transition of the edit.
      MovedGuard !Guard

{- | The valid edits of a term under an automaton with equality constraints.

A guard beyond equality constraints gives 'ConstrainedAutomaton'. The term
must have exactly one run, as for 'editAutomaton'.
-}
constrainedEditAutomaton ::
    (Ord state, Ord symbol) => FTA.PlainFTA state symbol -> Term symbol -> Either EditError (ConstrainedEdits symbol)
constrainedEditAutomaton automaton given
    | any (any (residual . FTA.transitionConstraint)) (FTA.transitionTable automaton) = Left ConstrainedAutomaton
    | otherwise = runIdentity $ editsWith holdsOn (\_ _ -> pure Unknown) runError automaton given
  where
    -- Without a residual guard, the equalities decide a constraint, and no atom is left to decide.
    holdsOn constraint term = pure $ if equalitiesHold constraint term then Yes else No
    -- The equalities decide each run, so the runs are none or more than one.
    runError verdicts = if null verdicts then NotAccepted else SeveralRuns

{- | The valid edits of a term under an automaton with guards, with a solver
that decides them.

The term must have exactly one run, and the solver must decide it. When the
solver refutes every run, the result is 'EditFailure' 'NotAccepted', and when
it decides two runs, 'EditFailure' 'SeveralRuns'. When it decides no run and
does not refute one, the result is 'UndecidedTerm'. When it decides one run
and does not refute another, the result is 'UndecidedRuns': the automaton
accepts the term, but the run of the edits is not known.

The solver decides the guards of the run, the guards on fixed paths of each
site, and for each position, whether each state of the automaton accepts the
subterm there: the states of the hole of a context wrap. That is one check
for each state at each position, also where the position has no context wrap
with a term. Count the result with 'Data.CFTA.Sized.sizedUpTo' over the
symbols of 'plainSymbols'.
-}
guardedEditAutomaton ::
    (Ord state) =>
    Entailment ->
    FTA.PlainFTA state Symbol ->
    Term Symbol ->
    IO (Either GuardedEditError (ConstrainedEdits Symbol))
guardedEditAutomaton entailment =
    editsWith
        (evaluateConstraint entailment)
        (\atom observed -> evaluateGuardWithShape entailment (fmap (uncurry Observed) . observed) atom)
        runError
  where
    runError verdicts = case (length $ filter (== Yes) verdicts, length $ filter (== Unknown) verdicts) of
        (0, 0) -> EditFailure NotAccepted
        (0, _) -> UndecidedTerm
        (1, _) -> UndecidedRuns
        _ -> EditFailure SeveralRuns

{- | The edit automaton with plain symbols, and the decoding of its terms to
edits.

The root symbol of each site and each 'HoleParent' symbol gets a fresh
symbol of its own, which no 'Material' symbol of the automaton is. A
'Material' symbol becomes its symbol. 'Data.CFTA.Sized.sizedUpTo' needs plain
symbols to decide the guards. A guard on a root transition reads only the
children of the root, and a context wrap whose hole a guard reads is left
out, so no guard reads a fresh symbol. The decoding gives the edit of a term
of the automaton, for 'applyEdit'.
-}
plainSymbols ::
    FTA.PlainFTA ConstrainedState (EditSymbol Symbol) -> (FTA.PlainFTA ConstrainedState Symbol, Term Symbol -> Edit Symbol)
plainSymbols automaton = (encoded, decode)
  where
    labels =
        nubOrd
            [FTA.transitionSymbol transition | transitions <- Map.elems $ FTA.transitionTable automaton, transition <- transitions]
    materialOf label = case label of
        Material symbol -> Just symbol
        _ -> Nothing
    material = Set.fromList [symbol | Just symbol <- map materialOf labels]
    others = [label | label <- labels, isNothing (materialOf label)]
    fresh = filter (`Set.notMember` material) [fromString $ "edit-" <> show number | number <- [0 :: Int ..]]
    names = Map.fromList $ zip others fresh
    labelsOf = Map.fromList $ zip fresh others
    encoded = FTA.mapSymbols (\label -> fromMaybe (names Map.! label) (materialOf label)) automaton
    decode (Term.Node symbol children) = Term.Node (Map.findWithDefault (Material symbol) symbol labelsOf) (map decode children)

{- | The edits of a term, with the verdict of a constraint on a whole term,
and the verdict of a guard atom from the observations at its paths. The
edits need exactly one run of the term, with the verdict 'Yes'. Otherwise
the result is the error of the verdicts of the runs that the check does not
refute.
-}
editsWith ::
    (Monad m, Ord state, Ord symbol) =>
    (Constraint -> Term symbol -> m Verdict) ->
    (Guard -> (Path -> Maybe (symbol, Leafness)) -> m Verdict) ->
    ([Verdict] -> failure) ->
    FTA.PlainFTA state symbol ->
    Term symbol ->
    m (Either failure (ConstrainedEdits symbol))
editsWith check decideAtom runError automaton given = do
    found <- runsFrom (FTA.initialState automaton) given
    case found of
        [(Yes, run)] -> Right <$> fromRun run
        _ -> pure $ Left $ runError $ map fst found
  where
    rows = Map.toList $ FTA.transitionTable automaton
    rootedAt state =
        fromRight (error "Data.CFTA.Edit.Constrained: an automaton with another initial state is not valid") $
            FTA.mkFTA state rows

    {- The runs from a state on a term whose constraints the check does not
    refute: the verdict of the run, and the state and the transition at each
    position.
    -}
    runsFrom state term@(Term.Node symbol children) =
        fmap concat $ forM (FTA.transitionsFrom automaton state) $ \transition ->
            if FTA.transitionSymbol transition /= symbol || length (FTA.transitionChildren transition) /= length children
                then pure []
                else do
                    verdict <- check (FTA.transitionConstraint transition) term
                    if verdict == No
                        then pure []
                        else do
                            childRuns <- zipWithM runsFrom (FTA.transitionChildren transition) children
                            pure
                                [ ( if verdict == Yes && all ((== Yes) . fst) picked then Yes else Unknown
                                  , Map.insert [] (state, transition) $
                                        Map.unions [Map.mapKeys (index :) run | (index, (_, run)) <- zip [0 ..] picked]
                                  )
                                | picked <- sequence childRuns
                                ]
    -- Whether a state accepts a term.
    acceptance state term = do
        verdicts <- map fst <$> runsFrom state term
        pure $
            if
                | Yes `elem` verdicts -> Yes
                | Unknown `elem` verdicts -> Unknown
                | otherwise -> No

    -- The states whose terms can have a node with a constraint.
    constrainedBelow = Set.fromList [state | state <- FTA.states automaton, any constrained (reachable state)]
    constrained state = any ((/= noConstraint) . FTA.transitionConstraint) (FTA.transitionsFrom automaton state)
    reachable state = go Set.empty [state]
      where
        go seen [] = Set.toList seen
        go seen (next : pending)
            | Set.member next seen = go seen pending
            | otherwise =
                go (Set.insert next seen) (concatMap FTA.transitionChildren (FTA.transitionsFrom automaton next) <> pending)

    fromRun run = do
        sites <- concat <$> mapM sitesAt [(at, state, subtermAt given at) | (at, (state, _)) <- Map.toList run]
        built <- forM (zip [0 ..] sites) $ \(number, (symbol, children, constraints, known)) -> do
            outcome <- site number symbol children constraints known
            pure (symbol, outcome)
        pure
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
        {- The sites of a position: the symbol, the children, the constraints,
        and whether the state accepts the fixed part of each.
        -}
        sitesAt (at, state, old) = do
            unwraps <- unwrapSites at state old
            wraps <- wrapSites at state old
            contexts <- contextSites at state old
            pure $ replaceSite at state old : unwraps <> wraps <> contexts
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
        -- The constraints of the transitions above the position, with the kind of their paths.
        aboveConstraints at inNew = [(FTA.transitionConstraint transition, kindAbove at prefix inNew) | (prefix, transition) <- above at]

        -- A replacement: one child, the terms of the state other than the old subterm.
        replaceSite at state old = (ReplaceAt (toPath at), [Slot state (Just old)], aboveConstraints at (Inside 0), Yes)
        -- The unwraps of a position: no child; the paths below it lead into the child that takes its place.
        unwrapSites at state (Term.Node _ grandchildren) =
            fmap concat $ forM (zip [0 ..] grandchildren) $ \(index, grandchild) -> do
                known <- acceptance state grandchild
                pure
                    [ ( UnwrapAt (toPath at) (ChildIndex index)
                      , []
                      , aboveConstraints at (maybe Missing Fixed . subtermAtMaybe grandchild)
                      , known
                      )
                    | known /= No
                    ]
        -- The wraps of a position: one for each transition of its state and each child whose state accepts the old subterm.
        wrapSites at state old =
            fmap concat $ forM (zip [0 ..] (FTA.transitionsFrom automaton state)) $ \(index, transition) -> do
                let children = FTA.transitionChildren transition
                fmap concat $ forM (zip [0 ..] children) $ \(hole, child) -> do
                    known <- acceptance child old
                    let inNew relative = case relative of
                            [] -> Through (FTA.transitionSymbol transition)
                            other : rest
                                | other == hole -> maybe Missing Fixed $ subtermAtMaybe old rest
                                | other < length children -> Inside (if other < hole then other else other - 1) rest
                                | otherwise -> Missing
                    pure
                        [ ( WrapAt (toPath at) (FTA.transitionSymbol transition) (TransitionIndex index) (ChildIndex hole)
                          , [Slot sibling Nothing | (other, sibling) <- zip [0 ..] children, other /= hole]
                          , (FTA.transitionConstraint transition, inNew) : aboveConstraints at inNew
                          , known
                          )
                        | known /= No
                        ]
        -- The context wraps of a position: one for each transition of its state and each child that has the hole.
        contextSites at state old = do
            verdicts <- forM (FTA.states automaton) $ \candidate -> do
                verdict <- acceptance candidate old
                pure (candidate, verdict)
            let holeStates = Set.fromList [candidate | (candidate, Yes) <- verdicts]
                known = if any ((== Unknown) . snd) verdicts then Unknown else Yes
            pure
                [ ( ContextAt (toPath at) (FTA.transitionSymbol transition) (TransitionIndex index) (ChildIndex hole)
                  , [if other == hole then HoledSlot holeStates child else Slot child Nothing | (other, child) <- zip [0 ..] children]
                  , (FTA.transitionConstraint transition, inNew) : aboveConstraints at inNew
                  , known
                  )
                | (index, transition) <- zip [0 ..] (FTA.transitionsFrom automaton state)
                , let children = FTA.transitionChildren transition
                , hole <- [0 .. length children - 1]
                , let inNew relative = case relative of
                        [] -> Through (FTA.transitionSymbol transition)
                        other : rest
                            | other == hole -> IntoHole
                            | other < length children -> Inside other rest
                            | otherwise -> Missing
                ]

        {- The root transition and the child rows of a site: 'Left' for a site
        that the result leaves out, and 'Nothing' for a site without a valid
        edit. A constraint that cannot hold decides the site, whatever the
        other constraints are, so such a site is not left out.
        -}
        site number symbol children constraints known
            | branching (unIndexes $ sitePath symbol) = pure $ Left Branching
            | any (null . ($ Hole)) childRows' = pure $ Right Nothing
            | otherwise = do
                analysed <- mapM analyse constraints
                let outcomes = concatMap fst analysed
                    moved = map snd analysed
                    reasons =
                        [ConstrainedHole | any readsHole outcomes || any constrainedHole children]
                            <> [reason | Apart reason <- moved]
                            <> [UndecidedGuard | known == Unknown]
                pure $
                    if
                        | any isImpossible outcomes || or [True | Decided False <- moved] -> Right Nothing
                        | not (null reasons) -> Left (minimum reasons)
                        | otherwise -> Right $ build outcomes moved
          where
            build outcomes moved = do
                templates <-
                    mapM (\child -> pinTemplate [(at, value) | (child', at, value) <- pins, child' == child]) [0 .. length children - 1]
                let pinned = zipWith ($) childRows' templates
                if any null pinned
                    then Nothing
                    else
                        pure (FTA.Transition symbol [Child number child 0 | child <- [0 .. length children - 1]] rootConstraint, concat pinned)
              where
                pins = concat [pins' | HoldsWhen pins' _ <- outcomes]
                classes = [shifted | HoldsWhen _ (Just shifted) <- outcomes]
                rootConstraint =
                    (if null classes then noConstraint else equalityConstraint $ mkEqConstraints classes)
                        { constraintGuard = conjoin [guard | MovedGuard guard <- moved]
                        }
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
            | relative `isPrefixOf` below && relative /= below = Through $ rootSymbol $ subtermAt given (prefix <> relative)
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

    -- The outcomes of the equality classes of a constraint, and the rest of its guard moved onto an edit.
    analyse (constraint, kind) = do
        let (sames, rest) = splitSames (constraintGuard constraint)
            classes = storedClasses (constraintEqualities constraint) <> [[unIndexes left, unIndexes right] | (left, right) <- sames]
        moved <- moveGuard kind True rest
        pure (map (classOutcome kind) classes, moved)

    -- What one class asks of an edit.
    classOutcome kind paths =
        let kinds = map kind paths
            fixed = nubOrd [value | Fixed value <- kinds]
            inside = [(child, at) | Inside child at <- kinds]
         in if
                | or [True | Through _ <- kinds] || or [True | Missing <- kinds] || length fixed > 1 -> Impossible
                | or [True | IntoHole <- kinds] -> ReadsHole
                | otherwise -> case fixed of
                    [value] -> HoldsWhen [(child, at, value) | (child, at) <- inside] Nothing
                    _
                        | length inside >= 2 -> HoldsWhen [] (Just [toPath (child : at) | (child, at) <- inside])
                        | otherwise -> HoldsWhen [] Nothing

    {- A guard with a polarity, moved onto an edit as the evaluator reads it:
    a negation changes the polarity, and an atom is decided or moved with its
    polarity.
    -}
    moveGuard kind positive guard = case guard of
        Top -> pure $ Decided positive
        Bottom -> pure $ Decided (not positive)
        Not inner -> moveGuard kind (not positive) inner
        And guards -> foldr (if positive then andMoved else orMoved) (Decided positive) <$> mapM (moveGuard kind positive) guards
        Or guards -> foldr (if positive then orMoved else andMoved) (Decided (not positive)) <$> mapM (moveGuard kind positive) guards
        Substitute [] inner -> moveGuard kind positive inner
        Substitute _ _ -> pure $ Apart GuardSubstitution
        Same left right -> pure $ case (kindOf left, kindOf right) of
            (Missing, _) -> Decided (not positive)
            (_, Missing) -> Decided (not positive)
            (IntoHole, _) -> Apart ConstrainedHole
            (_, IntoHole) -> Apart ConstrainedHole
            (Inside one oneAt, Inside other otherAt) -> MovedGuard $ polar $ Same (toPath (one : oneAt)) (toPath (other : otherAt))
            _ | left == right -> Decided positive
            (Fixed one, Fixed other) -> Decided (positive == (one == other))
            _ -> Apart MixedGuard
        Satisfies at _ -> atom [at]
        Entails left right -> atom [left, right]
        Holds targets _ -> atom targets
      where
        kindOf = kind . unIndexes
        polar inner = if positive then inner else Not inner
        isInside found = case found of
            Inside _ _ -> True
            _ -> False
        isIntoHole found = case found of
            IntoHole -> True
            _ -> False
        atom paths
            | any isIntoHole kinds = pure $ Apart ConstrainedHole
            | not (any isInside kinds) = verdictMoved <$> decideAtom (polar guard) observed
            | all isInside kinds = pure $ MovedGuard $ polar $ shifted guard
            | otherwise = pure $ Apart MixedGuard
          where
            kinds = map kindOf paths
        verdictMoved verdict = case verdict of
            Yes -> Decided True
            No -> Decided False
            Unknown -> Apart UndecidedGuard
        observed at = case kindOf at of
            Fixed (Term.Node symbol children) -> Just (symbol, leafnessOf children)
            Through symbol -> Just (symbol, Inner)
            _ -> Nothing
        shift at = case kindOf at of
            Inside child rest -> toPath (child : rest)
            _ -> at
        shifted inner = case inner of
            Satisfies at formula -> Satisfies (shift at) formula
            Entails left right -> Entails (shift left) (shift right)
            Holds targets formula -> Holds (map shift targets) formula
            other -> other

-- | The conjunction of two moved guards. One false guard decides it.
andMoved :: Moved -> Moved -> Moved
andMoved left right = case (left, right) of
    (Decided False, _) -> Decided False
    (_, Decided False) -> Decided False
    (Decided True, other) -> other
    (other, Decided True) -> other
    (Apart one, Apart other) -> Apart (min one other)
    (Apart one, _) -> Apart one
    (_, Apart other) -> Apart other
    (MovedGuard one, MovedGuard other) -> MovedGuard (And [one, other])

-- | The disjunction of two moved guards. One true guard decides it.
orMoved :: Moved -> Moved -> Moved
orMoved left right = case (left, right) of
    (Decided True, _) -> Decided True
    (_, Decided True) -> Decided True
    (Decided False, other) -> other
    (other, Decided False) -> other
    (Apart one, Apart other) -> Apart (min one other)
    (Apart one, _) -> Apart one
    (_, Apart other) -> Apart other
    (MovedGuard one, MovedGuard other) -> MovedGuard (Or [one, other])

-- | The equality atoms between two different paths at the top of a guard, and the rest of the guard.
splitSames :: Guard -> ([(Path, Path)], Guard)
splitSames guard = case guard of
    Same left right | left /= right -> ([(left, right)], Top)
    And guards ->
        let parts = map splitSames guards
         in (concatMap fst parts, conjoin [rest | (_, rest) <- parts, rest /= Top])
    _ -> ([], guard)

-- | The classes of equality constraints, as child indexes. A contradiction is a class that cannot hold.
storedClasses :: EqConstraints -> [[[Int]]]
storedClasses constraints = case constraints of
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

-- | The symbol at the root of a term.
rootSymbol :: Term symbol -> symbol
rootSymbol (Term.Node symbol _) = symbol

-- | A path from child indexes.
toPath :: [Int] -> Path
toPath = path . map ChildIndex

-- | The child indexes of a path.
unIndexes :: Path -> [Int]
unIndexes = map (\(ChildIndex index) -> index) . unPath
