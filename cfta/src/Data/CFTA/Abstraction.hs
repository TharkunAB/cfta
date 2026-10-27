{- | Checks that a later automaton is an abstraction extension of an earlier
automaton, with a solver.

In an abstraction extension, the later automaton splits a production of the
earlier automaton into refined variants, for example one for each cube of new
predicates: a leaf @lit@ with the refinement @0 <= v <= 9@ becomes
@lit [0 <= v <= 9 && v > 4]@ and @lit [0 <= v <= 9 && v <= 4]@. A variant has
the text of the symbol, the child states, and the constraint of its
production, and another refinement. The two automata share their states.

For each production of the earlier automaton, the variants are the
productions of the later automaton at the same state with the same symbol
text, the same child states, and the same constraint. When the earlier
automaton has more than one production with that key, the variants belong to
all of them. 'checkAbstraction' asks the solver:

* Cover: the refinement of each production entails the disjunction of the
  refinements of its variants. Otherwise a value of the earlier automaton can
  be in no variant ('Uncovered'). A production without variants is lost.
* Soundness: the refinement of each variant entails the disjunction of the
  refinements of its productions. Otherwise a variant has a new value
  ('Unsound'). A production of the later automaton without a production of
  the earlier automaton with its key is a variant without productions.

'checkOverlaps' asks whether the refinements of two variants exclude each
other. Two variants with a common value make the later automaton ambiguous,
so their ranks count that value twice. An overlap is a warning, not a failure
of the extension.

Each report holds the verdict of the solver: 'No', or 'Unknown' when the
solver does not decide the question. 'Unknown' is never read as 'Yes'. A query
that reaches the time limit of the Z3 solver ('TimeLimitReached') is
'Unknown'. The solver gives no model, so a report names the productions, not a
value.
-}
module Data.CFTA.Abstraction (
    Production,
    AbstractionError (..),
    Overlap (..),
    checkAbstraction,
    checkOverlaps,
) where

import Control.Exception (handle)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Text (Text)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Formula (Formula (Bottom), conjunction, disjunction)
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..))
import Data.CFTA.Refinement.Verdict (Entailment (entails), Verdict (..))
import Data.CFTA.Symbol (Symbol, symbolRefinement, symbolText)

-- | A production of an automaton: a symbol, its child states, and its constraint.
type Production state = FTA.Transition state Symbol Constraint

-- | A reason why the later automaton is not an abstraction extension of the earlier automaton.
data AbstractionError state
    = -- | The initial state of the earlier automaton and the other initial state of the later automaton.
      ChangedStart !state !state
    | {- | A production of the earlier automaton whose refinement does not
      entail the disjunction of the refinements of its variants, the variants,
      and the verdict of the solver: 'No' or 'Unknown'.
      -}
      Uncovered !state !(Production state) ![Production state] !Verdict
    | {- | A variant whose refinement does not entail the disjunction of the
      refinements of its productions in the earlier automaton, the productions,
      and the verdict of the solver: 'No' or 'Unknown'.
      -}
      Unsound !state !(Production state) ![Production state] !Verdict
    deriving (Eq, Show)

{- | Two variants of a production whose refinements can both hold, and the
verdict of the solver on their exclusion: 'No' or 'Unknown'.
-}
data Overlap state = Overlap !state !(Production state) !(Production state) !Verdict
    deriving (Eq, Show)

{- | The reasons why the later automaton is not an abstraction extension of
the earlier automaton: another initial state, then the productions of the
earlier automaton that their variants do not cover, then the unsound
variants, each in state order. An empty list when it is an abstraction
extension.
-}
checkAbstraction ::
    (Ord state) => Entailment -> FTA.PlainFTA state Symbol -> FTA.PlainFTA state Symbol -> IO [AbstractionError state]
checkAbstraction entailment earlier later = do
    uncovered <- failures (pairs earlier later) entailed $ \(state, production, variants) -> Uncovered state production variants
    unsound <- failures (pairs later earlier) entailed $ \(state, variant, productions) -> Unsound state variant productions
    pure $ start <> uncovered <> unsound
  where
    -- The refinement of the production entails the disjunction of the refinements of the others.
    entailed (_, production, others) = decide entailment (refinement production) (disjunction $ map refinement others)
    start =
        [ChangedStart (FTA.initialState earlier) (FTA.initialState later) | FTA.initialState earlier /= FTA.initialState later]

{- | The pairs of variants of the later automaton whose refinements can both
hold, in state order. Two variants are a pair when they have the same key.
-}
checkOverlaps :: (Ord state) => Entailment -> FTA.PlainFTA state Symbol -> IO [Overlap state]
checkOverlaps entailment later =
    failures
        [ (state, left, right)
        | (state, productions) <- Map.toList $ FTA.transitionTable later
        , (index, left) <- zip [0 :: Int ..] productions
        , right <- drop (index + 1) productions
        , key left == key right
        ]
        (\(_, left, right) -> decide entailment (conjunction [refinement left, refinement right]) Bottom)
        (\(state, left, right) -> Overlap state left right)

{- | Each production of the first automaton with the productions of the second
automaton at the same state with the same key.
-}
pairs ::
    (Ord state) => FTA.PlainFTA state Symbol -> FTA.PlainFTA state Symbol -> [(state, Production state, [Production state])]
pairs first second =
    [ (state, production, filter ((== key production) . key) $ Map.findWithDefault [] state rows)
    | (state, productions) <- Map.toList $ FTA.transitionTable first
    , production <- productions
    ]
  where
    rows = FTA.transitionTable second

-- | Ask each question, and keep the report of each verdict that is not 'Yes', in order.
failures :: [question] -> (question -> IO Verdict) -> (question -> Verdict -> report) -> IO [report]
failures questions ask report = catMaybes <$> traverse one questions
  where
    one question = do
        verdict <- ask question
        pure $ if verdict == Yes then Nothing else Just $ report question verdict

-- | Ask the solver whether the first formula entails the second. A time limit gives 'Unknown'.
decide :: Entailment -> Formula -> Formula -> IO Verdict
decide entailment antecedent consequent = handle (\(TimeLimitReached _) -> pure Unknown) $ entails entailment antecedent consequent

-- | The symbol text, the child states, and the constraint of a production: what its variants keep.
key :: Production state -> (Text, [state], Constraint)
key production =
    (symbolText $ FTA.transitionSymbol production, FTA.transitionChildren production, FTA.transitionConstraint production)

-- | The refinement of the symbol of a production.
refinement :: Production state -> Formula
refinement = symbolRefinement . FTA.transitionSymbol
