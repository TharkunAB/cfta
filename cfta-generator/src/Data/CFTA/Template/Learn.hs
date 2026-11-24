{- | Learn exclusions from terms that a checker rejected and terms that it accepted.

'generalize' gives a least general generalization of terms as a
'Template': the anti-unification of Plotkin and of Reynolds (Machine
Intelligence 5, 1970). A difference that occurs at two positions gets one
named hole, so the template keeps the equality. 'learnExclusions' puts the
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
    exclusionPriceUpTo,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (find, sortOn, tails)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import Data.Ord (Down (..))
import Data.Text (Text)
import qualified Data.Text as Text

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Index (Cardinality (..), Size (..))
import Data.CFTA.Refinement.Verdict (Entailment (Entailment))
import Data.CFTA.Sized (Sized, SizedError, countOfSize, rankOfSize, sized, sizedUpTo)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (
    Template (..),
    excludeAnywhereFTA,
    excludeFTA,
    matchesNowhere,
    matchesTemplate,
    repeatedNames,
 )
import Data.CFTA.Template.Named (excludeNamedAnywhereFTA, excludeNamedFTA)
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

{- | A least general generalization of terms.

Terms with one root symbol and one arity give that symbol with the
generalizations of their children. At a position where the root symbols
differ, the terms at that position are a difference. A difference that
occurs at two or more positions gives a named hole there, as in the
anti-unification of Plotkin: @x - x@ and @1 - 1@ give @v0 - v0@. Another
difference of terms with one arity gives 'AnyNode' with the generalizations
of their children; for leaves, this is @AnyNode []@, which matches each
leaf. Another difference gives 'Hole'. Each of the terms matches the result.

A named hole and @AnyNode []@ are not comparable: the first keeps an
equality, and the second keeps a shape. So there is no unique least general
generalization. This function prefers the equality. The names are @v0@,
@v1@, and so on, in preorder.
-}
generalize :: (Ord symbol) => NonEmpty (Term symbol) -> Template symbol
generalize terms = rename (unshare (build terms))
  where
    -- The differences that occur at two or more positions, and a temporary name for each.
    repeated = Map.filter (> 1) (Map.fromListWith (+) [(difference, 1 :: Int) | difference <- differences terms])
    names = Map.fromList (zip (Map.keys repeated) [Text.pack (show index) | index <- [0 :: Int ..]])
    columnsByName = Map.fromList [(name, column) | (column, name) <- Map.toList names]
    differences column
        | sameSymbol column = concatMap differences (columns column)
        | sameArity column = column : concatMap differences (columns column)
        | otherwise = [column]
    build column
        | sameSymbol column = TemplateNode (Term.rootLabel (NonEmpty.head column)) (map build (columns column))
        | Just name <- Map.lookup column names = NamedHole name
        | sameArity column = AnyNode (map build (columns column))
        | otherwise = Hole
    -- A name that the result has only once states no equality.
    unshare template = replaceNames once template
      where
        once name
            | length (filter (== name) (holeNames template)) == 1 =
                maybe Hole anonymous (Map.lookup name columnsByName)
            | otherwise = NamedHole name
    rename template = replaceNames (\name -> NamedHole (Map.findWithDefault name name fresh)) template
      where
        fresh = Map.fromList (zip (nubOrd (holeNames template)) [Text.pack ("v" <> show index) | index <- [0 :: Int ..]])

-- | Whether the terms have one root symbol and one arity.
sameSymbol :: (Eq symbol) => NonEmpty (Term symbol) -> Bool
sameSymbol column@(first :| _) = sameArity column && all ((== Term.rootLabel first) . Term.rootLabel) column

-- | Whether the terms have one arity.
sameArity :: NonEmpty (Term symbol) -> Bool
sameArity column@(first :| _) = all ((== Term.arity first) . Term.arity) column

-- | The terms at each child index, for terms of one arity.
columns :: NonEmpty (Term symbol) -> [NonEmpty (Term symbol)]
columns column@(first :| _) = [Term.childAt index <$> column | index <- [0 .. Term.arity first - 1]]

-- | The generalization without named holes.
anonymous :: (Eq symbol) => NonEmpty (Term symbol) -> Template symbol
anonymous column
    | sameSymbol column = TemplateNode (Term.rootLabel (NonEmpty.head column)) (map anonymous (columns column))
    | sameArity column = AnyNode (map anonymous (columns column))
    | otherwise = Hole

-- | The names of the named holes of a template, in preorder, with repetitions.
holeNames :: Template symbol -> [Text]
holeNames template = case template of
    NamedHole name -> [name]
    Hole -> []
    AnyNode parts -> concatMap holeNames parts
    TemplateNode _ parts -> concatMap holeNames parts
    AnyPrefix parts -> concatMap holeNames parts
    TemplatePrefix _ parts -> concatMap holeNames parts

-- | Replace each named hole.
replaceNames :: (Text -> Template symbol) -> Template symbol -> Template symbol
replaceNames replace template = case template of
    NamedHole name -> replace name
    Hole -> Hole
    AnyNode parts -> AnyNode (map (replaceNames replace) parts)
    TemplateNode symbol parts -> TemplateNode symbol (map (replaceNames replace) parts)
    AnyPrefix parts -> AnyPrefix (map (replaceNames replace) parts)
    TemplatePrefix symbol parts -> TemplatePrefix symbol (map (replaceNames replace) parts)

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
    single term = anonymous (term :| [])
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

{- | The symbols, arities, and equalities that a template fixes: two for a
'TemplateNode' (its symbol and its arity), one for an 'AnyNode' (its arity),
and one for each repetition of a name.
-}
specificity :: Template symbol -> Int
specificity template = shape template + sum [length paths - 1 | (_, paths) <- repeatedNames template]
  where
    shape part = case part of
        Hole -> 0
        NamedHole _ -> 0
        AnyNode parts -> 1 + sum (map shape parts)
        TemplateNode _ parts -> 2 + sum (map shape parts)
        AnyPrefix parts -> sum (map shape parts)
        TemplatePrefix _ parts -> 1 + sum (map shape parts)

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

A template that repeats a name gives a guard ("Data.CFTA.Template.Named"),
and 'sized' rejects the guard with 'Data.CFTA.Sized.ResidualGuard'. Use
'exclusionPriceUpTo' for such a template.
-}
exclusionPrice ::
    (Ord state, Ord symbol) =>
    Placement ->
    Size ->
    [Term symbol] ->
    [Template symbol] ->
    FTA.FTA state symbol Constraint ->
    Either SizedError Price
exclusionPrice placement bound rejected templates automaton = do
    before <- sized automaton
    after <- case (placement, all (null . repeatedNames) templates) of
        (AtRoot, True) -> sized (excludeFTA templates automaton)
        (Anywhere, True) -> sized (excludeAnywhereFTA templates automaton)
        (AtRoot, False) -> sized (excludeNamedFTA templates automaton)
        (Anywhere, False) -> sized (excludeNamedAnywhereFTA templates automaton)
    pure (priceOf placement bound rejected templates before after)

{- | 'exclusionPrice' for any templates, also with repeated names, on an
automaton of 'Symbol's. 'Data.CFTA.Sized.sizedUpTo' decides the guards of the
named exclusion on each term that it builds, so the counts are exact. It
lists each term up to the bound, so its cost grows with the language.
-}
exclusionPriceUpTo ::
    (Ord state) =>
    Placement ->
    Size ->
    [Term Symbol] ->
    [Template Symbol] ->
    FTA.FTA state Symbol Constraint ->
    IO (Either SizedError Price)
exclusionPriceUpTo placement bound rejected templates automaton = do
    before <- sizedUpTo syntactic bound automaton
    after <- sizedUpTo syntactic bound $ case placement of
        AtRoot -> excludeNamedFTA templates automaton
        Anywhere -> excludeNamedAnywhereFTA templates automaton
    pure (priceOf placement bound rejected templates <$> before <*> after)
  where
    -- The guards compare subterms only, so they need no solver.
    syntactic = Entailment $ \_ _ -> fail "exclusionPriceUpTo: a template guard asked a solver"

-- | The price from the size classes before and after an exclusion.
priceOf ::
    (Ord symbol) => Placement -> Size -> [Term symbol] -> [Template symbol] -> Sized symbol -> Sized symbol -> Price
priceOf placement bound@(Size limit) rejected templates before after =
    Price (total before) (total after) (toInteger (length removed))
  where
    removed =
        [ term
        | term <- nubOrd rejected
        , toInteger (length term) <= limit
        , isJust (rankOfSize before term)
        , any (\template -> removes placement template term) templates
        ]
    total classes = sum [count | size <- [1 .. bound], let Cardinality count = countOfSize classes size]
