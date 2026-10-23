{- | The edits between two terms: the inverse of 'applyEdit'.

'editsBetween' gives every edit @e@ of 'editAutomaton' of the old term with
@applyEdit old e == Just new@. This is the exact preimage of the new term. It
is not a minimal edit, and it is not the difference of two languages
(the word "diff" names that operation elsewhere).

* If the two terms are equal, the result is empty. A caller asks which change
  was made, and no change was made. The edit automaton still has the
  replacements of a subterm by another term, so the equal pair has no edit.
* Let @p@ be the deepest position that holds every position where the two
  terms differ. An edit at a position @q@ changes only the subterm at @q@, so
  @q@ is @p@ or an ancestor of @p@. For each such @q@ the candidates are:
  the replacement at @q@ by the new subterm, each wrap at @q@ whose new node
  is the new subterm, with the old subterm as one child, each unwrap at @q@ to
  a child of the old subterm that is the new subterm, and each context wrap at
  @q@ whose new term is the new subterm, with the old subterm at the hole, deeper
  than the children of the new root.
* A term that is a wrap of the old subterm is also a replacement: @x@ to @f(x)@
  is a 'ReplaceAt' and, when @f@ is a transition of the state at the position, a
  'WrapAt'. The term @f(g(x))@ for @x@ is a 'ReplaceAt' and, when @f(g)@ is a
  context of the state at the position, a 'ContextAt'. If the old subterm is
  more than once in the new subterm, each place is a context wrap. The
  candidates of all kinds are built, so none is lost.
* Each candidate is checked: 'applyEdit' gives the new term from it, and the
  edit automaton accepts it. The automaton checks the state of the position
  (the category), the vocabulary, and that a replacement differs from the old
  subterm.

'editsBetween' orders the edits by size, and then by the order of the edit, so
the edits with the least new material come first. 'rankedEditsBetween' gives
the rank of each edit in the generator of the edit automaton, and orders them
by rank, which is the size-major order of that generator. It needs the edit
automaton to be unambiguous, as 'Data.CFTA.Edit' says.
-}
module Data.CFTA.Edit.Between (
    BetweenError (..),
    editsBetween,
    rankedEditsBetween,
) where

import Control.Monad (guard)
import Data.Hashable (Hashable)
import Data.List (isPrefixOf, sortOn)
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Edit
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (ChildIndex (..), Rank)
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (Path, getPath, path, unPath)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | Why the edits between two terms are not found.
data BetweenError
    = -- | The old term has no edit automaton.
      BetweenEdit !EditError
    | -- | The edit automaton has no generator, or an edit has no rank.
      BetweenRank !Gen.GenError
    deriving (Eq, Show)

{- | The edits of the old term that give the new term, the smallest first.

The result is empty if the two terms are equal, or if no edit gives the new
term: the new material is outside the vocabulary, or in the wrong category.
-}
editsBetween ::
    (Ord state, Ord symbol) =>
    FTA.PlainFTA state symbol ->
    Term symbol ->
    Term symbol ->
    Either BetweenError [Edit symbol]
editsBetween automaton old new = do
    edits <- either (Left . BetweenEdit) Right $ editAutomaton automaton old
    pure $ sortOn (\edit -> (length edit, edit)) $ filter (accepted edits) $ candidates edits old new
  where
    accepted edits edit = FTA.accepts edits edit && applyEdit old edit == Just new

{- | 'editsBetween' with the rank of each edit in the generator of the edit
automaton ('Data.CFTA.Gen.fromAutomaton'), in rank order.
-}
rankedEditsBetween ::
    (Ord state, Ord symbol, Hashable symbol, Typeable symbol) =>
    FTA.PlainFTA state symbol ->
    Term symbol ->
    Term symbol ->
    Either BetweenError [(Rank, Edit symbol)]
rankedEditsBetween automaton old new = do
    edits <- either (Left . BetweenEdit) Right $ editAutomaton automaton old
    found <- editsBetween automaton old new
    let generator = Gen.fromAutomaton $ Interned.fromRows (FTA.initialState edits) (FTA.transitionTable edits)
    ranked <- traverse (\edit -> either (Left . BetweenRank) (Right . flip (,) edit) $ Gen.rankOfTerm generator edit) found
    pure $ sortOn fst ranked

{- | The edits at the root of the edit automaton that might give the new term:
the sites at the deepest position of the difference and at its ancestors, with
the new material that the new term gives them.
-}
candidates ::
    (Ord state, Ord symbol) =>
    FTA.PlainFTA (EditState state symbol) (EditSymbol symbol) ->
    Term symbol ->
    Term symbol ->
    [Edit symbol]
candidates edits old new = case differenceAt old new of
    Nothing -> []
    Just deepest -> concatMap (candidate deepest) sites
  where
    sites = map FTA.transitionSymbol $ FTA.transitionsFrom edits EditRoot
    candidate deepest site = case site of
        ReplaceAt at -> do
            guard $ ancestorOf at deepest
            replacement <- toList $ getPath at new
            pure $ Term.Node site [fmap Material replacement]
        WrapAt at symbol _ (ChildIndex hole) -> do
            guard $ ancestorOf at deepest
            Term.Node found children <- toList $ getPath at new
            before <- toList $ getPath at old
            guard $ found == symbol && hole >= 0 && hole < length children && children !! hole == before
            pure $ Term.Node site [fmap Material child | (index, child) <- zip [0 ..] children, index /= hole]
        UnwrapAt at (ChildIndex index) -> do
            guard $ ancestorOf at deepest
            Term.Node _ children <- toList $ getPath at old
            now <- toList $ getPath at new
            guard $ index >= 0 && index < length children && children !! index == now
            pure $ Term.Node site []
        ContextAt at symbol _ (ChildIndex hole) -> do
            guard $ ancestorOf at deepest
            Term.Node found children <- toList $ getPath at new
            before <- toList $ getPath at old
            guard $ found == symbol && hole >= 0 && hole < length children
            -- The old subterm may be at more than one place below the child: each place is an edit.
            Term.Node site <$> [fillChildren hole children below | below <- placesBelow before (children !! hole)]
        HoleParent _ _ -> []
        Material _ -> []
    ancestorOf at deepest = unPath at `isPrefixOf` unPath deepest
    toList = maybe [] pure
    -- The child at the hole index becomes a context along the path, the other children are new material.
    fillChildren hole children below =
        [if index == hole then context below child else fmap Material child | (index, child) <- zip [0 ..] children]

-- | The paths in a term, at least one step down, to the subterms that equal the given term.
placesBelow :: (Eq symbol) => Term symbol -> Term symbol -> [[Int]]
placesBelow wanted (Term.Node _ children) =
    concat
        [ [[index] | child == wanted] <> map (index :) (placesBelow wanted child)
        | (index, child) <- zip [0 ..] children
        ]

-- | The new term along a path to its hole: the node over the hole has no child at the hole.
context :: [Int] -> Term symbol -> Edit symbol
context [index] (Term.Node symbol children) =
    Term.Node
        (HoleParent symbol (ChildIndex index))
        [fmap Material child | (other, child) <- zip [0 ..] children, other /= index]
context (index : rest) (Term.Node symbol children) =
    Term.Node
        (Material symbol)
        [if other == index then context rest child else fmap Material child | (other, child) <- zip [0 ..] children]
context [] term' = fmap Material term'

{- | The deepest position that holds every position where two terms differ.
'Nothing' if the terms are equal.
-}
differenceAt :: (Eq symbol) => Term symbol -> Term symbol -> Maybe Path
differenceAt old new
    | old == new = Nothing
    | otherwise = Just $ path $ go old new
  where
    go (Term.Node symbol children) (Term.Node other others)
        | symbol == other
        , length children == length others
        , [(index, (left, right))] <- [(index, pair) | (index, pair) <- zip [0 ..] (zip children others), fst pair /= snd pair] =
            ChildIndex index : go left right
    go _ _ = []
