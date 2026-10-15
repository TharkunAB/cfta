{- | A portfolio of proposers that share one host: each runs for its budget
under one deadline, the fits are reported once across the runs, and the
outcome of a run decides whether the next one runs.

A proposer makes candidate programs and checks them with the host, under
'Limits', as the walk of "Data.CFTA.Gen.Synthesis.Walk" does for Hectare's
programs ('hectare'), and the search of "Data.CFTA.Gen.Synthesis.States"
for the programs of the host's own goals ('states'). The portfolio runs the proposers in order: the first
for its budget, and each later one when the one before ended without
'Solved' ('Exhausted': it looked at every program up to its limits;
'OutOfTime': it reached its budget), for its budget or the rest of the time.
It keeps the fits so far, so that a program that a later run finds again is
not a new fit, and it gives the figures of each run.

'flaggedLast' orders fits with a host's flag (as a fit that ignores a part
of itself) after the others, in a stable order: the ranking does not depend
on the host, the flag does.
-}
module Data.CFTA.Gen.Synthesis.Portfolio (
    -- * Proposers
    Proposer (..),
    hectare,
    states,
    statesWith,

    -- * Portfolios
    Run (..),
    portfolio,
    combined,

    -- * Ranking
    flaggedLast,
) where

import Control.Applicative ((<|>))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.IORef (atomicModifyIORef', newIORef)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)

import Data.CFTA.Gen.Synthesis (Program, Type)
import Data.CFTA.Gen.Synthesis.States (Figures, Goals, Walking (..), searchStatesWith)
import Data.CFTA.Gen.Synthesis.Walk

-- Proposers

{- | A proposer: its name, its budget in seconds ('Nothing': the rest of the
time), and its run. A run takes the limits (with the deadline of the run),
the function that says whether a fit's program is new, and the caller's
function on fits, and it gives its figures with its outcome.
-}
data Proposer m = Proposer
    { proposerName :: Text
    , proposerBudget :: Maybe Double
    , proposerRun :: Limits -> ([Token] -> m Bool) -> (Fit -> m Bool) -> m Progress
    }

{- | Hectare's programs over erased leaves, checked by the walk with the
host's checker (mode (a)): a proposer with a name, a budget, the hooks for
the sizes and the programs, the leaves, Hectare's pruning rules, and the
erased goal.
-}
hectare ::
    (MonadIO m) =>
    Text ->
    Maybe Double ->
    Checker m ->
    (Int -> Progress -> m ()) ->
    (Int -> Program -> m ()) ->
    [Erased] ->
    [([Text], Maybe [Text])] ->
    Type ->
    Proposer m
hectare name budget checker onSize onProgram leaves avoid goal =
    Proposer name budget $ \limits new accept ->
        walk limits checker (Hooks onSize onProgram new) leaves avoid goal accept

{- | The programs of the host's own goals over states, checked with the
host's checker (mode (b)): a proposer with a name, a budget, the hooks for
the sizes and the programs, a function on the figures of the states at the
end of the run, the host's goals, and Hectare's pruning rules.
-}
states ::
    (MonadIO m, Ord key) =>
    Text ->
    Maybe Double ->
    Checker m ->
    (Int -> Progress -> m ()) ->
    (Int -> Program -> m ()) ->
    (Figures -> m ()) ->
    Goals m key ->
    [([Text], Maybe [Text])] ->
    Proposer m
states = statesWith Preorder

-- | 'states' with a way to walk the table of each size.
statesWith ::
    (MonadIO m, Ord key) =>
    Walking ->
    Text ->
    Maybe Double ->
    Checker m ->
    (Int -> Progress -> m ()) ->
    (Int -> Program -> m ()) ->
    (Figures -> m ()) ->
    Goals m key ->
    [([Text], Maybe [Text])] ->
    Proposer m
statesWith walking name budget checker onSize onProgram onFigures goals avoid =
    Proposer name budget $ \limits new accept -> do
        (progress, figures) <- searchStatesWith walking limits checker (Hooks onSize onProgram new) goals avoid accept
        progress <$ onFigures figures

-- Portfolios

-- | A run of a proposer: its name, its figures with its outcome, and its time.
data Run = Run
    { runName :: Text
    , runProgress :: Progress
    , runNanos :: !Word64
    -- ^ The time of the run on the monotonic clock, in nanoseconds.
    }
    deriving (Eq, Show)

{- | Run the proposers in order under the limits, each for its budget: a run
that is 'Solved' ends the portfolio, and after another outcome the next
proposer runs, while there is time. The fits are new once across the runs.
The result has the runs that took place.
-}
portfolio :: (MonadIO m) => Limits -> [Proposer m] -> (Fit -> m Bool) -> m [Run]
portfolio limits proposers accept = do
    reported <- liftIO (newIORef Set.empty)
    let new tokens = liftIO $ atomicModifyIORef' reported $ \seen ->
            if tokens `Set.member` seen then (seen, False) else (Set.insert tokens seen, True)
        go remaining runs = case remaining of
            [] -> pure (reverse runs)
            proposer : rest -> do
                now <- liftIO getMonotonicTimeNSec
                if maybe False (now >=) (limitDeadline limits) && not (null runs)
                    then pure (reverse runs)
                    else do
                        let deadline = earlier (limitDeadline limits) (budgetEnd now <$> proposerBudget proposer)
                        progress <- proposerRun proposer limits{limitDeadline = deadline} new accept
                        end <- liftIO getMonotonicTimeNSec
                        let runs' = Run (proposerName proposer) progress (end - now) : runs
                        if progressOutcome progress == Solved then pure (reverse runs') else go rest runs'
    go proposers []
  where
    budgetEnd :: Word64 -> Double -> Word64
    budgetEnd now seconds = now + round (seconds * 1e9)
    earlier (Just a) (Just b) = Just (min a b)
    earlier a b = a <|> b

{- | The figures of runs together: the sums of the counts and of the times,
and the size, the deadline, and the outcome of the last run.
-}
combined :: [Run] -> Progress
combined = foldl add emptyProgress . map runProgress
  where
    add total progress =
        progress
            { progressPrograms = progressPrograms total + progressPrograms progress
            , progressSkipped = progressSkipped total + progressSkipped progress
            , progressFits = progressFits total + progressFits progress
            , progressBuildNanos = progressBuildNanos total + progressBuildNanos progress
            , progressReduceNanos = progressReduceNanos total + progressReduceNanos progress
            , progressListNanos = progressListNanos total + progressListNanos progress
            , progressCheckNanos = progressCheckNanos total + progressCheckNanos progress
            }

-- Ranking

-- | The items without the flag, then the items with it, each in their order.
flaggedLast :: (a -> Bool) -> [a] -> [a]
flaggedLast flagged items = filter (not . flagged) items <> filter flagged items
