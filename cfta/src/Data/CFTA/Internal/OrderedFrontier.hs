{- | Ordered enumeration scheduler. The Enumeration adapter owns equality state.
The caller supplies opaque branch snapshots from the existing enumerator.
Bounds and monotone refresh are contracts. They are not proved by this module.
-}
module Data.CFTA.Internal.OrderedFrontier where

import qualified Data.Map.Strict as Map

-- | A lower bound. Unknown compares below every known key.
data Estimate key = Unknown | Bound !key
    deriving (Eq, Ord, Show)

{- | A lazy source of siblings. The bound covers every remaining sibling.
The suspended function returns one sibling. It must not collect the source.
-}
data Siblings key branch
    = End
    | More !(Estimate key) (branch -> (branch, Siblings key branch))

-- | One existing-enumerator step, or a complete result from that branch.
data Step key branch value
    = Dead
    | Finished value
    | Children (Siblings key branch)

{- | Callbacks for a fixed raw search tree and a changing monotone filter.
Refresh must inspect the current global filter. It may reject a branch.
It must not add completions or change the raw sibling source.
-}
data Policy key rules branch value = Policy
    { refresh :: rules -> branch -> Maybe branch
    , lowerBound :: branch -> Estimate key
    , advance :: branch -> Step key branch value
    , exactKey :: value -> key
    }

-- | Pending work. Finished results retain their branch for a fresh filter check.
data Job key branch value
    = Prefix branch
    | Rest branch (Siblings key branch)
    | Result branch value

-- | Small counters. They do not estimate the size of captured closures.
data Counts = Counts
    { poppedJobs :: !Integer
    , rejectedJobs :: !Integer
    , pulledSiblings :: !Integer
    , maximumQueueEntries :: !Int
    }
    deriving (Eq, Show)

-- | Persistent frontier with deterministic serial numbers for equal priorities.
data Cursor key rules branch value = Cursor
    { globalRules :: rules
    , queue :: !(Map.Map (Estimate key, Int, Integer) (Job key branch value))
    , nextSerial :: !Integer
    , counts :: !Counts
    }

-- | The work limit or the frontier capacity stopped this call.
data PauseReason = FuelLimit | FrontierLimit
    deriving (Eq, Show)

-- | A result, normal exhaustion, a resumable limit, or an invalid bound.
data Next key rules branch value
    = Yield value (Cursor key rules branch value)
    | Exhausted Counts
    | Paused PauseReason (Cursor key rules branch value)
    | InvalidBound key (Estimate key) (Cursor key rules branch value)

-- | Start from one opaque branch. No branch expansion occurs here.
start :: Policy key rules branch value -> rules -> branch -> Cursor key rules branch value
start policy rules branch =
    Cursor rules (Map.singleton (lowerBound policy branch, 1, 0) (Prefix branch)) 1 (Counts 0 0 0 1)

-- | Replace the global filter with a stronger one. Recheck jobs when activated.
strengthen :: rules -> Cursor key rules branch value -> Cursor key rules branch value
strengthen rules cursor = cursor{globalRules = rules}

-- | Preserve the strongest inherited lower bound.
stronger :: (Ord key) => Estimate key -> Estimate key -> Estimate key
stronger = max

-- | Add at most two jobs. Equal-key complete results precede unfinished work.
insertJobs ::
    (Ord key) => [(Estimate key, Job key branch value)] -> Cursor key rules branch value -> Cursor key rules branch value
insertJobs jobs cursor = foldl add cursor jobs
  where
    add current (bound, job) =
        let kind = case job of Result _ _ -> 0; _ -> 1
            serial = nextSerial current
            newQueue = Map.insert (bound, kind, serial) job (queue current)
            oldCounts = counts current
         in current
                { queue = newQueue
                , nextSerial = serial + 1
                , counts = oldCounts{maximumQueueEntries = max (maximumQueueEntries oldCounts) (Map.size newQueue)}
                }

{- | Produce the smallest certified result within a work and frontier limit.
Unknown bounds remain work; they never justify discarding a branch.
A limit returns the intact current frontier. Increase the limit to resume.
-}
next ::
    (Ord key) => Policy key rules branch value -> Int -> Int -> Cursor key rules branch value -> Next key rules branch value
next policy fuel limit cursor
    | fuel <= 0 = Paused FuelLimit cursor
    | Map.size (queue cursor) > limit = Paused FrontierLimit cursor
    | otherwise = case Map.minViewWithKey (queue cursor) of
        Nothing -> Exhausted (counts cursor)
        Just (((bound, _, _), job), rest) ->
            let oldCounts = counts cursor
                popped = cursor{queue = rest, counts = oldCounts{poppedJobs = poppedJobs oldCounts + 1}}
                reject =
                    next
                        policy
                        (fuel - 1)
                        limit
                        popped{counts = (counts popped){rejectedJobs = rejectedJobs oldCounts + 1}}
                continueFrom current jobs =
                    if Map.size rest + length jobs > limit
                        then Paused FrontierLimit cursor
                        else next policy (fuel - 1) limit (insertJobs jobs current)
                continue = continueFrom popped
                recheck branch = refresh policy (globalRules cursor) branch
                siblings parent stream = case stream of
                    End -> []
                    More tailBound _ -> [(stronger bound tailBound, Rest parent stream)]
             in case job of
                    Prefix branch -> case recheck branch of
                        Nothing -> reject
                        Just current -> case advance policy current of
                            Dead -> continue []
                            Finished value ->
                                let key = exactKey policy value
                                 in if Bound key < bound
                                        then InvalidBound key bound cursor
                                        else continue [(Bound key, Result current value)]
                            Children stream -> continue (siblings current stream)
                    Rest parent stream -> case recheck parent of
                        Nothing -> reject
                        Just current -> case stream of
                            End -> continue []
                            More _ pull ->
                                let (child, remaining) = pull current
                                    jobs = (stronger bound (lowerBound policy child), Prefix child) : siblings current remaining
                                    currentCounts = counts popped
                                    pulled = popped{counts = currentCounts{pulledSiblings = pulledSiblings currentCounts + 1}}
                                 in continueFrom pulled jobs
                    Result branch value -> case recheck branch of
                        Nothing -> reject
                        Just _ -> Yield value popped
