{- | Learn exclusions from terms that a checker rejected and terms that it accepted.

'generalize' gives the least general generalization of terms as a
'Template': the anti-unification of Plotkin and of Reynolds (Machine
Intelligence 5, 1970), with anonymous holes. 'learnExclusions' puts the
rejected terms into clusters. The generalization of each cluster matches no
accepted term, so each cluster gives one exclusion. 'exclusionPrice' counts
the terms of a language that exclusions remove within a size bound, so a
caller can see what each template costs.

The clusters come from agglomerative clustering, as in Getafix (Bader,
Scott, Pradel, and Chandra, OOPSLA 2019). Each rejected term starts as one
cluster. Each step merges the two clusters whose generalization keeps the
most symbols and arities and matches no accepted term. The steps stop when no
merge is possible. The result is a heuristic: it does not have the least
number of templates in every case.
-}
module Data.CFTA.Template.Learn (
    Placement (..),
    generalize,
    Exclusion (..),
    Conflict (..),
    Learned (..),
    learnExclusions,
    Price (..),
    priceExtra,
    exclusionPrice,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (find, sortOn, tails)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe (isJust, isNothing)
import Data.Ord (Down (..))

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Index (Cardinality (..), Size (..))
import Data.CFTA.Sized (Sized, SizedError, countOfSize, rankOfSize, sized)
import Data.CFTA.Template (Template (..), excludeAnywhereFTA, excludeFTA, matchesNowhere, matchesTemplate)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

{- | Where an exclusion applies: at the root of a term, as 'excludeFTA' does,
or at each subterm, as 'excludeAnywhereFTA' does.
-}
data Placement = AtRoot | Anywhere
    deriving (Eq, Show)

-- | Whether a template removes a term with a placement.
removes :: (Eq symbol) => Placement -> Template symbol -> Term symbol -> Bool
removes AtRoot template term = matchesTemplate template term
removes Anywhere template term = not (matchesNowhere [template] term)

{- | The least general generalization of terms, with anonymous holes.

Terms with one root symbol and one arity give that symbol with the
generalizations of their children. Terms with one arity and different root
symbols give 'AnyNode' with the generalizations of their children; for
leaves, this is @AnyNode []@, which matches each leaf. Terms with different
arities give 'Hole'. Each of the terms matches the result.

The holes have no names. Thus the result cannot state that two positions
hold the same subterm. With named variables, @x - x@ and @1 - 1@ generalize
to @v - v@. Here they generalize to @_ - _@, which also matches @x - 1@.
-}
generalize :: (Eq symbol) => NonEmpty (Term symbol) -> Template symbol
generalize terms@(first :| _)
    | any ((/= arity) . Term.arity) terms = Hole
    | all ((== symbol) . Term.rootLabel) terms = TemplateNode symbol parts
    | otherwise = AnyNode parts
  where
    symbol = Term.rootLabel first
    arity = Term.arity first
    parts = [generalize (Term.childAt index <$> terms) | index <- [0 .. arity - 1]]

-- | A learned exclusion: a template, and the rejected terms that it generalizes.
data Exclusion symbol = Exclusion
    { exclusionTemplate :: !(Template symbol)
    , exclusionSources :: ![Term symbol]
    }
    deriving (Eq, Show)

{- | A rejected term that no template can remove without an accepted term.
'AtRoot' gives a conflict when the accepted term is equal to the rejected
term. 'Anywhere' gives one also when the accepted term contains it.
-}
data Conflict symbol = Conflict
    { conflictRejected :: !(Term symbol)
    , conflictAccepted :: !(Term symbol)
    }
    deriving (Eq, Show)

-- | The exclusions, in template order, and the conflicts, in the order of the rejected terms.
data Learned symbol = Learned
    { learnedExclusions :: ![Exclusion symbol]
    , learnedConflicts :: ![Conflict symbol]
    }
    deriving (Eq, Show)

{- | Learn exclusions that remove each rejected term and no accepted term.

The first list holds the rejected terms, and the second the accepted terms.
Each template of the result removes no accepted term with the placement.
Each rejected term without a conflict is a source of one template, and that
template removes it. A cluster with the generalization 'Hole' does not merge,
because that template removes each term.

A template that removes no accepted term stays safe when it gets more
specific. So when one template that removes no accepted term generalizes all
the rejected terms, each merge is safe, and the result has one template.
-}
learnExclusions :: (Ord symbol) => Placement -> [Term symbol] -> [Term symbol] -> Learned symbol
learnExclusions placement rejected accepted =
    Learned
        (sortOn exclusionTemplate [Exclusion template sources | (template, sources) <- merge initial])
        [Conflict term blocking | term <- unique, Just blocking <- [blocker (single term)]]
  where
    unique = nubOrd rejected
    single term = generalize (term :| [])
    blocker template = find (removes placement template) accepted
    initial = [(single term, [term]) | term <- unique, isNothing (blocker (single term))]

    -- Merge the best safe pair until no pair is safe.
    merge clusters = case sortOn rank candidates of
        [] -> clusters
        (_, merged) : _ -> merge merged
      where
        numbered = zip [0 :: Int ..] clusters
        candidates =
            [ (template, merged : [cluster | (index, cluster) <- numbered, index /= left, index /= right])
            | (left, (_, leftSources)) : rest <- tails numbered
            , (right, (_, rightSources)) <- rest
            , let sources = leftSources <> rightSources
                  template = generalize (NonEmpty.fromList sources)
                  merged = (template, sources)
            , template /= Hole
            , isNothing (blocker template)
            ]
        rank (template, _) = (Down (specificity template), template)

{- | The symbols and arities that a template fixes: two for a 'TemplateNode'
(its symbol and its arity), and one for an 'AnyNode' (its arity).
-}
specificity :: Template symbol -> Int
specificity template = case template of
    Hole -> 0
    AnyNode parts -> 1 + sum (map specificity parts)
    TemplateNode _ parts -> 2 + sum (map specificity parts)
    AnyPrefix parts -> sum (map specificity parts)
    TemplatePrefix _ parts -> 1 + sum (map specificity parts)
    NamedHole _ -> 0

{- | The terms of a language with at most a bound of nodes, before and after
an exclusion.
-}
data Price = Price
    { priceBefore :: !Integer
    -- ^ The terms of the language.
    , priceAfter :: !Integer
    -- ^ The terms that the exclusion keeps.
    , priceRejected :: !Integer
    -- ^ The rejected terms of the language that the exclusion removes.
    }
    deriving (Eq, Show)

-- | The removed terms that are not rejected terms: the cost of the generalization.
priceExtra :: Price -> Integer
priceExtra price = priceBefore price - priceAfter price - priceRejected price

{- | Count the terms that templates remove from a language, within a size
bound. The list holds the rejected terms.

'Data.CFTA.Sized' counts the language before and after the exclusion. Give
one template for the price of that template. The prices of templates that
remove the same terms do not add up to the price of all of them.
-}
exclusionPrice ::
    (Ord state, Ord symbol) =>
    Placement ->
    Size ->
    [Term symbol] ->
    [Template symbol] ->
    FTA.FTA state symbol Constraint ->
    Either SizedError Price
exclusionPrice placement bound@(Size limit) rejected templates automaton = do
    before <- sized automaton
    after <- case placement of
        AtRoot -> sized (excludeFTA templates automaton)
        Anywhere -> sized (excludeAnywhereFTA templates automaton)
    let removed =
            [ term
            | term <- nubOrd rejected
            , toInteger (length term) <= limit
            , isJust (rankOfSize before term)
            , any (\template -> removes placement template term) templates
            ]
    pure (Price (total before) (total after) (toInteger (length removed)))
  where
    total :: Sized symbol -> Integer
    total classes = sum [count | size <- [1 .. bound], let Cardinality count = countOfSize classes size]
