{- | Refinement-typed component synthesis with Hectare's program spaces and
Hegel's checks.

"Data.CFTA.Gen.Synthesis" (Hectare) lists the programs of a goal type size
by size, and the programs of its spaces use every argument of the query.
"Data.CFTA.Gen.Synthesis.Liquid" (Hegel) checks refinement types. The hybrid
gives Hectare the base types of the components and the query, lists the
programs of each size in Hectare's order, replaces each group
representative by each member of its group ('Data.CFTA.Gen.Synthesis.expand'),
and checks each program with 'Data.CFTA.Gen.Synthesis.Liquid.checker' or
'Data.CFTA.Gen.Synthesis.Liquid.preciseChecker'. It stops at the first
program that passes.

The search is goal-directed: the solver sees only the subprograms of
programs of the goal type, and the search stops within a size. A size counts
the components and arguments of a program, as in Hectare. The hybrid does
not make conditionals, and it does not find a program that leaves out an
argument of the query. Up to the largest size, each other term of Hegel is a
program of Hectare's spaces. A program of Hectare's spaces that Hegel cannot
type, such as a partial application as an argument, fails the check.
-}
module Data.CFTA.Gen.Synthesis.Hybrid (
    HybridOptions (..),
    defaultHybridOptions,
    HybridStatistics (..),
    HybridOutcome (..),
    synthesizeHybrid,
) where

import Data.Containers.ListUtils (nubOrd)
import Data.IORef (modifyIORef', newIORef, readIORef)

import Data.CFTA.Gen.Synthesis (Program, Query (..), expand, library, solutionsOfSize)
import Data.CFTA.Gen.Synthesis.Liquid (
    Checker (..),
    Component,
    LiquidQuery (..),
    baseOf,
    checker,
    preciseChecker,
 )
import Data.CFTA.Refinement (Entailment)

-- | The options of a hybrid search.
data HybridOptions = HybridOptions
    { hybridPrecise :: Bool
    -- ^ Check with 'preciseChecker' instead of 'checker'.
    , hybridMaximumSize :: Int
    -- ^ The largest size of a program: its components and arguments.
    }
    deriving (Eq, Show)

-- | The precise checker, and programs of at most 20 components and arguments.
defaultHybridOptions :: HybridOptions
defaultHybridOptions = HybridOptions True 20

-- | What a hybrid search did.
data HybridStatistics = HybridStatistics
    { hybridSize :: Int
    -- ^ The size of the solution, or the largest size.
    , hybridChecked :: Int
    -- ^ The programs that the search checked.
    , hybridQueries :: Int
    -- ^ The entailment queries.
    , hybridUndecided :: Int
    -- ^ The entailment queries that the solver could not decide.
    }
    deriving (Eq, Show)

-- | The first program that passes, or none, and the statistics of the search.
data HybridOutcome = HybridOutcome
    { hybridSolution :: Maybe Program
    , hybridStatistics :: HybridStatistics
    }
    deriving (Eq, Show)

{- | List the programs of the goal's base type size by size, and stop at the
first one that passes the check. Each program is checked once: two
programs of representatives expand to different programs.
-}
synthesizeHybrid :: Entailment -> HybridOptions -> [Component] -> LiquidQuery -> IO HybridOutcome
synthesizeHybrid entailment options components query = do
    check <- (if hybridPrecise options then preciseChecker else checker) entailment components query
    checked <- newIORef (0 :: Int)
    let search size
            | size > hybridMaximumSize options = pure Nothing
            | otherwise = do
                found <- firstPassing (concatMap (expand lib) (nubOrd (solutionsOfSize lib goal size)))
                maybe (search (size + 1)) (pure . Just . (size,)) found
        firstPassing [] = pure Nothing
        firstPassing (program : rest) = do
            modifyIORef' checked (+ 1)
            passes <- checkProgram check program
            if passes then pure (Just program) else firstPassing rest
    found <- search 1
    count <- readIORef checked
    (queries, undecided) <- checkerQueries check
    pure $
        HybridOutcome
            (snd <$> found)
            (HybridStatistics (maybe (hybridMaximumSize options) fst found) count queries undecided)
  where
    lib = library [(name, baseOf typ) | (name, typ) <- components] [] []
    goal = Query [(name, baseOf typ) | (name, typ) <- liquidArguments query] (baseOf (liquidGoal query))
