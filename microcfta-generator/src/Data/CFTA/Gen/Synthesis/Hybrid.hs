{- | Refinement-typed component synthesis with Hectare's program spaces and
Hegel's checks.

"Data.CFTA.Gen.Synthesis" (Hectare) lists the programs of a goal type size
by size, and the programs of its spaces use every argument of the query.
"Data.CFTA.Gen.Synthesis.Liquid" (Hegel) checks refinement types. The hybrid
gives Hectare the base types of the components and the query, and Hectare's
saturated space ('Data.CFTA.Gen.Synthesis.rawSaturatedSearchSpace') has only
Hegel's terms: each head is applied to all its parameters, and each leaf is
an argument of the query or a component that Hegel uses as a value. The
hybrid lists the programs of each size of this space in Hectare's order,
replaces each group representative by each member of its group
('Data.CFTA.Gen.Synthesis.expand'), and checks each program with
'Data.CFTA.Gen.Synthesis.Liquid.checker' or
'Data.CFTA.Gen.Synthesis.Liquid.preciseChecker'. It stops at the first
program that passes.

The search is goal-directed: the solver sees only the subprograms of
programs of the goal type, and the search stops within a size. A size counts
the components and arguments of a program, as in Hectare. The hybrid does
not make conditionals, and it does not find a program that leaves out an
argument of the query. Up to the largest size, each other term of Hegel is a
program of the saturated space. The other programs of Hectare's spaces, such
as a partial application as an argument, fail the check, so the saturated
space loses no solution.

Hectare's construction grows fast with the size and the number of
arguments, and some goal types have millions of programs, so the hybrid can
be slower than Hegel. With 'hybridFallback', the hybrid has a time budget.
When it has no program at the end of the budget, or after its largest size,
Hegel's 'synthesize' runs on the query.
-}
module Data.CFTA.Gen.Synthesis.Hybrid (
    HybridOptions (..),
    defaultHybridOptions,
    HybridStatistics (..),
    HybridOutcome (..),
    synthesizeHybrid,
) where

import Control.Monad (join)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import System.Timeout (timeout)

import Data.CFTA.Gen.Synthesis (
    Library (..),
    Program,
    Query (..),
    Saturation (..),
    distinctSaturatedSolutionsOfSize,
    expand,
 )
import Data.CFTA.Gen.Synthesis.Liquid (
    Checker (..),
    Component,
    LiquidQuery (..),
    Options,
    Outcome,
    baseOf,
    checker,
    componentRoles,
    defaultOptions,
    preciseChecker,
    synthesize,
 )
import Data.CFTA.Refinement (Entailment)

-- | The options of a hybrid search.
data HybridOptions = HybridOptions
    { hybridPrecise :: Bool
    -- ^ Check with 'preciseChecker' instead of 'checker'.
    , hybridMaximumSize :: Int
    -- ^ The largest size of a program: its components and arguments.
    , hybridFallback :: Maybe (Int, Options)
    {- ^ The seconds of the hybrid, and the options of Hegel's 'synthesize',
    which runs when the hybrid has no program at the end of them. With
    'Nothing', the hybrid runs alone and has no time budget.
    -}
    }
    deriving (Show)

{- | The precise checker, programs of at most 20 components and arguments,
and Hegel with 'defaultOptions' after 30 seconds.
-}
defaultHybridOptions :: HybridOptions
defaultHybridOptions = HybridOptions True 20 (Just (30, defaultOptions))

-- | What a hybrid search did.
data HybridStatistics = HybridStatistics
    { hybridSize :: Int
    -- ^ The size of the solution, or the last size that the hybrid reached.
    , hybridChecked :: Int
    -- ^ The programs that the search checked.
    , hybridQueries :: Int
    -- ^ The entailment queries.
    , hybridUndecided :: Int
    -- ^ The entailment queries that the solver could not decide.
    }
    deriving (Eq, Show)

{- | The first program that passes, or none, the statistics of the hybrid,
and Hegel's result when the fallback ran.
-}
data HybridOutcome = HybridOutcome
    { hybridSolution :: Maybe Program
    , hybridStatistics :: HybridStatistics
    , hybridFallbackOutcome :: Maybe (Either String Outcome)
    }
    deriving (Show)

{- | List the saturated programs of the goal's base type size by size, and
stop at the first one that passes the check. Each program is checked once: two
programs of representatives expand to different programs. Without a
program, run the fallback of the options.
-}
synthesizeHybrid :: Entailment -> HybridOptions -> [Component] -> LiquidQuery -> IO HybridOutcome
synthesizeHybrid entailment options components query = do
    check <- (if hybridPrecise options then preciseChecker else checker) entailment components query
    checked <- newIORef (0 :: Int)
    reached <- newIORef (0 :: Int)
    let search size
            | size > hybridMaximumSize options = pure Nothing
            | otherwise = do
                writeIORef reached size
                found <- firstPassing (concatMap (expand lib) (distinctSaturatedSolutionsOfSize saturation lib goal size))
                maybe (search (size + 1)) (pure . Just . (size,)) found
        firstPassing [] = pure Nothing
        firstPassing (program : rest) = do
            modifyIORef' checked (+ 1)
            passes <- checkProgram check program
            if passes then pure (Just program) else firstPassing rest
    -- The solver replaces its process when a time limit stops a query, so
    -- Hegel can use the solver after the budget.
    found <- case hybridFallback options of
        Nothing -> search 1
        Just (seconds, _) -> join <$> timeout (seconds * 1000000) (search 1)
    count <- readIORef checked
    size <- readIORef reached
    (queries, undecided) <- checkerQueries check
    fallback <- case (found, hybridFallback options) of
        (Nothing, Just (_, hegel)) -> Just <$> synthesize entailment hegel components query
        _ -> pure Nothing
    pure $
        HybridOutcome
            (snd <$> found)
            (HybridStatistics (maybe size fst found) count queries undecided)
            fallback
  where
    goal = Query [(name, baseOf typ) | (name, typ) <- liquidArguments query] (baseOf (liquidGoal query))
    -- The components of a group share their base type, their number of
    -- parameters, and whether they are values.
    roles = Map.fromList [(name, (parameters, value)) | (name, parameters, value) <- componentRoles components query]
    groups = foldl addMember [] [(name, (baseOf typ, Map.findWithDefault (0, False) name roles)) | (name, typ) <- components]
    addMember found (name, key) = case break ((== key) . fst) found of
        (before, (_, members) : after) -> before <> ((key, members <> [name]) : after)
        (before, []) -> before <> [(key, [name])]
    representativeName index = Text.pack ("f" <> show (index :: Int))
    lib =
        Library
            { libraryGroups = [(representativeName index, typ, members) | (index, ((typ, _), members)) <- zip [0 ..] groups]
            , libraryArgumentOnly = []
            , libraryAvoid = []
            }
    saturation =
        Saturation
            { saturationArities =
                Map.fromList
                    [ (representativeName index, parameters)
                    | (index, ((_, (parameters, _)), _)) <- zip [0 ..] groups
                    , parameters > 0
                    ]
            , saturationValues = [representativeName index | (index, ((_, (_, True)), _)) <- zip [0 ..] groups]
            }
