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

__Edit sets.__ 'editSetsBetween' gives every edit set of 'editSetAutomaton'
of the old term with 'applyEditSet' that gives the new term: the exact
preimage for edits at one to k incomparable positions. A set of one edit is
an edit of 'editsBetween', so the one-edit sets of the result are the edits of
'editsBetween' for every k of at least 1. The candidates:

* A mismatch is a position where the two terms differ and the symbols or the
  numbers of children differ. An edit changes the subterm at its position, and
  only that subterm, so each mismatch is at or below exactly one position of a
  set, and each position of a set is at or above a mismatch.
* The positions at or above a mismatch are the difference. The position sets
  of the candidates are its cuts: the sets of at most k positions, with each
  mismatch at or below exactly one of them.
* Each position of a cut takes the candidates of 'editsBetween' at that
  position: the replacement, the wraps, the unwraps, and the context wraps
  that change its old subterm into its new subterm.
* Each candidate set is checked: the automaton of edit sets accepts it, and
  'applyEditSet' gives the new term from it.

With @d@ positions in the difference and at most @w@ candidates at one
position, there are at most @sum [choose d j * w ^ j | j <- [1 .. k]]@
candidate sets. 'editSetsBetween' counts them exactly before it builds them,
and gives 'TooManyCandidates' when the count is above 'candidateLimit'.

An edit tree ("Data.CFTA.Edit.Trees") can have an edit inside a wrap. Then the
new term has a node above the changed old subterm, and the positions of the
two terms do not align below it. The preimage of edit trees needs, for each
wrap and context wrap at a position, the alignment of the child with the hole
in the new subterm with the old subterm, and the edit sets between that pair,
when the wrap is treeable. 'editSetsBetween' does not give edit trees.
-}
module Data.CFTA.Edit.Between (
    BetweenError (..),
    editsBetween,
    rankedEditsBetween,
    editSetsBetween,
    rankedEditSetsBetween,
    candidateLimit,
) where

import Control.Monad (guard)
import Data.Hashable (Hashable)
import Data.List (isPrefixOf, sortOn)
import qualified Data.Map.Strict as Map
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Edit
import Data.CFTA.Edit.Internal (bug, sitePath)
import Data.CFTA.Edit.Sets (SetSymbol (..), applyEditSet, editSetAutomaton)
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
    | -- | The number of candidate edit sets, which is above 'candidateLimit'.
      TooManyCandidates !Integer
    deriving (Eq, Show)

-- | The largest number of candidate edit sets that 'editSetsBetween' checks.
candidateLimit :: Integer
candidateLimit = 100000

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
    Just deepest ->
        concat
            [ siteCandidates old new site
            | site <- map FTA.transitionSymbol $ FTA.transitionsFrom edits EditRoot
            , unPath (sitePath site) `isPrefixOf` unPath deepest
            ]

{- | The edits at one site that might change the old subterm at its position
into the new subterm there, with the new material that the new term gives them.
-}
siteCandidates :: (Eq symbol) => Term symbol -> Term symbol -> EditSymbol symbol -> [Edit symbol]
siteCandidates old new site = case site of
    ReplaceAt at -> do
        replacement <- toList $ getPath at new
        pure $ Term.Node site [fmap Material replacement]
    WrapAt at symbol _ (ChildIndex hole) -> do
        Term.Node found children <- toList $ getPath at new
        before <- toList $ getPath at old
        guard $ found == symbol && hole >= 0 && hole < length children && children !! hole == before
        pure $ Term.Node site [fmap Material child | (index, child) <- zip [0 ..] children, index /= hole]
    UnwrapAt at (ChildIndex index) -> do
        Term.Node _ children <- toList $ getPath at old
        now <- toList $ getPath at new
        guard $ index >= 0 && index < length children && children !! index == now
        pure $ Term.Node site []
    ContextAt at symbol _ (ChildIndex hole) -> do
        Term.Node found children <- toList $ getPath at new
        before <- toList $ getPath at old
        guard $ found == symbol && hole >= 0 && hole < length children
        -- The old subterm may be at more than one place below the child: each place is an edit.
        Term.Node site <$> [fillChildren hole children below | below <- placesBelow before (children !! hole)]
    HoleParent _ _ -> []
    Material _ -> []
  where
    toList = maybe [] pure
    -- The child at the hole index becomes a context along the path, the other children are new material.
    fillChildren hole children below =
        [if index == hole then context below child else fmap Material child | (index, child) <- zip [0 ..] children]

{- | The edit sets of the old term that give the new term, of one to k edits,
the smallest first.

The result is empty if the two terms are equal, or if no edit set gives the
new term. It is 'TooManyCandidates' when there are more candidate sets than
'candidateLimit'.
-}
editSetsBetween ::
    (Ord state, Ord symbol) =>
    Int ->
    FTA.PlainFTA state symbol ->
    Term symbol ->
    Term symbol ->
    Either BetweenError [Term (SetSymbol symbol)]
editSetsBetween bound automaton old new = do
    edits <- either (Left . BetweenEdit) Right $ editAutomaton automaton old
    case differenceOf old new of
        Nothing -> pure []
        Just difference -> do
            let sitesAt =
                    Map.fromListWith
                        (flip (<>))
                        [ (unPath (sitePath site), [site])
                        | site <- map FTA.transitionSymbol $ FTA.transitionsFrom edits EditRoot
                        ]
                candidatesAt at = concatMap (siteCandidates old new) (Map.findWithDefault [] (map ChildIndex at) sitesAt)
                count = sum $ drop 1 $ cutCounts bound (fromIntegral . length . candidatesAt) [] difference
            if count > candidateLimit
                then Left $ TooManyCandidates count
                else do
                    sets <- either (Left . BetweenEdit) Right $ editSetAutomaton bound automaton old
                    let accepted set = FTA.accepts sets set && applyEditSet old set == Just new
                    pure
                        $ sortOn (\set -> (length set, set))
                        $ filter accepted [setTerm chosen | chosen <- cuts bound candidatesAt [] difference]

{- | 'editSetsBetween' with the rank of each edit set in the generator of the
automaton of edit sets ('Data.CFTA.Gen.fromAutomaton'), in rank order.
-}
rankedEditSetsBetween ::
    (Ord state, Ord symbol, Hashable symbol, Typeable symbol) =>
    Int ->
    FTA.PlainFTA state symbol ->
    Term symbol ->
    Term symbol ->
    Either BetweenError [(Rank, Term (SetSymbol symbol))]
rankedEditSetsBetween bound automaton old new = do
    found <- editSetsBetween bound automaton old new
    sets <- either (Left . BetweenEdit) Right $ editSetAutomaton bound automaton old
    let generator = Gen.fromAutomaton $ Interned.fromRows (FTA.initialState sets) (FTA.transitionTable sets)
    ranked <- traverse (\set -> either (Left . BetweenRank) (Right . flip (,) set) $ Gen.rankOfTerm generator set) found
    pure $ sortOn fst ranked

-- | Where two terms differ, below a position where they agree on the symbol and the number of children.
data Difference
    = -- | The symbols or the numbers of children differ.
      Mismatch
    | -- | The children that differ, by child index.
      Below ![(Int, Difference)]

-- | Where two terms differ. 'Nothing' if they are equal.
differenceOf :: (Eq symbol) => Term symbol -> Term symbol -> Maybe Difference
differenceOf old@(Term.Node symbol children) new@(Term.Node other others)
    | old == new = Nothing
    | symbol == other && length children == length others =
        Just $
            Below
                [(index, found) | (index, (left, right)) <- zip [0 ..] (zip children others), Just found <- [differenceOf left right]]
    | otherwise = Just Mismatch

{- | The number of candidate sets of the cuts of a difference, by the number of
positions, from zero to the bound: a cut takes one candidate at each of its
positions.
-}
cutCounts :: Int -> ([Int] -> Integer) -> [Int] -> Difference -> [Integer]
cutCounts bound weight at difference = zipWith (+) chosen below
  where
    chosen = take (bound + 1) $ 0 : weight at : repeat 0
    below = case difference of
        Mismatch -> replicate (bound + 1) 0
        Below children -> foldr (product' . \(index, child) -> cutCounts bound weight (at <> [index]) child) one children
    one = take (bound + 1) $ 1 : repeat 0
    -- The counts of two independent parts, by the total number of positions.
    product' left right = [sum [left !! i * right !! (j - i) | i <- [0 .. j]] | j <- [0 .. bound]]

-- | The candidate edits of the cuts of a difference with at most the bound of positions, in preorder.
cuts :: Int -> ([Int] -> [Edit symbol]) -> [Int] -> Difference -> [[Edit symbol]]
cuts bound candidatesAt at difference
    | bound < 1 = []
    | otherwise = [[edit] | edit <- candidatesAt at] <> below
  where
    below = case difference of
        Mismatch -> []
        Below children -> combine bound children
    combine _ [] = [[]]
    combine left ((index, child) : rest) =
        [first <> others | first <- cuts left candidatesAt (at <> [index]) child, others <- combine (left - length first) rest]

{- | The term of an edit set from its edits in preorder: a chain of sites, as in
"Data.CFTA.Edit.Sets".
-}
setTerm :: [Edit symbol] -> Term (SetSymbol symbol)
setTerm chosen = case chosen of
    [Term.Node site material] -> Term.Node (Last site) (map (fmap Inside) material)
    Term.Node site material : rest -> Term.Node (Link site) (map (fmap Inside) material <> [setTerm rest])
    [] -> bug "an edit set without an edit"

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
