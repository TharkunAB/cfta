{- | The edits of a term, as the terms of an automaton.

An edit changes a term of an automaton at one position. The position keeps
the state that the run of the term gives it, so the edited term is a term of
the automaton too. There are two kinds of edit:

* A replacement at a position gives the position a new subterm: a term of the
  state of the position other than the old subterm.
* A wrap at a position puts a new node above the old subterm. The new node
  comes from one transition of the state of the position. The old subterm is
  one child of the new node: a child whose state accepts it. The other
  children are any terms of their states.

'editAutomaton' gives an automaton whose terms are the edits of one term. An
edit site is a position with a kind of edit: a replacement, or a wrap with a
transition and a child index. Each edit site has a root symbol of its own.
The children of the root are the new material of the edit: the new subterm
of a replacement, or the other children of the new node of a wrap. So the
size of an edit is one more than the size of its new material, and the
size-major order gives the edits with the least new material first.
'applyEdit' gives the edited term of an edit.

Two edits can give one edited term. For example, a replacement at the root
can give each term that a deeper edit gives. The automaton counts the edits,
not the edited terms.

When the automaton is unambiguous, the edit automaton is unambiguous too:

* The root transitions have different symbols, one for each edit site, so no
  two of them accept one edit.
* The new subterm of a replacement comes from 'excludeFTA', which keeps an
  unambiguous automaton unambiguous.
* The other children of a wrap come from the states of the automaton, which
  are unambiguous.

So each edit has one run, and the generator import and the count table of
'Data.CFTA.Sized' accept the edit automaton.

The automaton must have no constraints, and the term must have exactly one
run.
-}
module Data.CFTA.Edit (
    EditSymbol (..),
    EditState (..),
    EditError (..),
    Edit,
    editAutomaton,
    applyEdit,
) where

import Control.Monad (guard)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Index (ChildIndex (..), TransitionIndex (..))
import Data.CFTA.Path (Path, getPath, modifyAtPath, path, unPath)
import Data.CFTA.Template (Obligation, Template (..), excludeFTA)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A symbol of an edit: the root symbol of an edit site, or a symbol of the new material.
data EditSymbol symbol
    = -- | Replace the subterm at the path with the one child.
      ReplaceAt !Path
    | {- | Wrap the subterm at the path in a new node with this symbol, from
      this transition of the state at the path. The old subterm is the child
      at the child index, and the children of the edit are the other children
      in order.
      -}
      WrapAt !Path !symbol !TransitionIndex !ChildIndex
    | -- | A symbol of the new material.
      Material !symbol
    deriving (Eq, Ord, Show, Generic)

instance (Hashable symbol) => Hashable (EditSymbol symbol)

-- | A state of an edit automaton.
data EditState state symbol
    = -- | The initial state: one transition for each edit site.
      EditRoot
    | -- | Any term of the state.
      Free !state
    | -- | A state of the new subterm of a replacement: a state of the automaton with what its terms must not match.
      Excluded !(state, Obligation symbol)
    deriving (Eq, Ord, Show)

-- | Why a term has no edit automaton.
data EditError
    = -- | A transition of the automaton has a constraint.
      ConstrainedAutomaton
    | -- | The automaton does not accept the term.
      NotAccepted
    | -- | The automaton has more than one run for the term.
      SeveralRuns
    deriving (Eq, Show)

-- | An edit: a term of an edit automaton.
type Edit symbol = Term (EditSymbol symbol)

{- | The automaton of the edits of a term.

Each position of the term has a replacement site and a wrap site for each
transition of its state and each child index whose state accepts the old
subterm. A site without a term is not in the result.
-}
editAutomaton ::
    (Ord state, Ord symbol) =>
    FTA.PlainFTA state symbol ->
    Term symbol ->
    Either EditError (FTA.PlainFTA (EditState state symbol) (EditSymbol symbol))
editAutomaton automaton given
    | any (any ((/= noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable automaton) = Left ConstrainedAutomaton
    | otherwise = case take 2 $ runsFrom (FTA.initialState automaton) given of
        [] -> Left NotAccepted
        [run] -> Right $ edits [(at, state, old) | (at, state) <- Map.toList run, Just old <- [getPath at given]]
        _ -> Left SeveralRuns
  where
    -- The edit automaton of the positions, with their states and subterms.
    edits positions =
        FTA.trim
            $ fromRight (error "Data.CFTA.Edit: the edit automaton of a ranked automaton is not ranked")
            $ FTA.mkFTA EditRoot
            $ (EditRoot, concat [replaceAt at exclusion : wrapsAt at state old | (at, state, old, exclusion) <- sites])
                : [(Free state, map (onChildren Free) transitions) | (state, transitions) <- Map.toList $ FTA.transitionTable automaton]
                    <> Map.toList (Map.unions [excludedRows exclusion | (_, _, _, exclusion) <- sites])
      where
        sites = [(at, state, old, excludeFTA [template old] (rootedAt state)) | (at, state, old) <- positions]
    -- The replacement site at a position: a term of the state other than the old subterm.
    replaceAt at exclusion = FTA.Transition (ReplaceAt at) [Excluded $ FTA.initialState exclusion] noConstraint
    -- The wrap sites at a position.
    wrapsAt at state old =
        [ FTA.Transition
            (WrapAt at symbol (TransitionIndex index) (ChildIndex hole))
            [Free sibling | (other, sibling) <- zip [0 ..] children, other /= hole]
            noConstraint
        | (index, FTA.Transition symbol children _) <- zip [0 ..] (FTA.transitionsFrom automaton state)
        , (hole, child) <- zip [0 ..] children
        , FTA.accepts (rootedAt child) old
        ]
    excludedRows exclusion =
        Map.fromList
            [ (Excluded pair, map (onChildren Excluded) transitions)
            | (pair, transitions) <- Map.toList $ FTA.transitionTable exclusion
            ]
    rootedAt state =
        fromRight (error "Data.CFTA.Edit: an automaton with another initial state is not valid")
            $ FTA.mkFTA state
            $ Map.toList
            $ FTA.transitionTable automaton
    -- The runs from a state on a term: the state of each position.
    runsFrom state (Term.Node symbol children) =
        [ Map.insert (path []) state $
            Map.unions [Map.mapKeys (path . (ChildIndex index :) . unPath) childRun | (index, childRun) <- zip [0 ..] childRuns]
        | FTA.Transition other childStates _ <- FTA.transitionsFrom automaton state
        , other == symbol
        , length childStates == length children
        , childRuns <- sequence $ zipWith runsFrom childStates children
        ]

{- | The edited term of an edit. 'Nothing' when the edit does not fit the term:
a path that the term does not have, a child index out of range, or a root
symbol inside new material.
-}
applyEdit :: Term symbol -> Edit symbol -> Maybe (Term symbol)
applyEdit given edit = case edit of
    Term.Node (ReplaceAt at) [new] -> do
        _ <- getPath at given
        replacement <- material new
        pure $ modifyAtPath (const replacement) at given
    Term.Node (WrapAt at symbol _ (ChildIndex hole)) others -> do
        old <- getPath at given
        children <- traverse material others
        guard $ hole >= 0 && hole <= length children
        let (before, after) = splitAt hole children
        pure $ modifyAtPath (const $ Term.Node symbol $ before <> (old : after)) at given
    _ -> Nothing
  where
    material (Term.Node (Material symbol) children) = Term.Node symbol <$> traverse material children
    material _ = Nothing

-- | The template that matches exactly the term.
template :: Term symbol -> Template symbol
template (Term.Node symbol children) = TemplateNode symbol (map template children)

-- | A transition with the states and symbols of the new material.
onChildren ::
    (state -> other) -> FTA.Transition state symbol Constraint -> FTA.Transition other (EditSymbol symbol) Constraint
onChildren rename (FTA.Transition symbol children constraint) = FTA.Transition (Material symbol) (map rename children) constraint
