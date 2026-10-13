-- | Replay the staged open-cache rank fixture with the actual constructors.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Enumeration (unconstrained)
import Data.CFTA.Interned.Operations (unfoldOuterRec)
import Data.CFTA.Interned.Type
import qualified Data.Set as Set

-- | Capture the exact depth sentinel used by the Lean fixture.
depthCapture :: Node Int
depthCapture = Rec RecDepth

-- | Capture the exact level-two ordinary sentinel.
ordinaryCapture :: Node Int
ordinaryCapture = Rec (RecUnint 2)

-- | Retain the inner raw binder and both fixed sentinel captures.
originalBody :: Node Int -> Node Int
originalBody outer = createMuDontCleanup $ \inner ->
    Node
        [ Edge 0 [depthCapture]
        , Edge 0 [ordinaryCapture]
        , Edge 1 [inner]
        , Edge 2 [outer]
        ]

-- | Build the original outer raw binder before the cache preloads.
original :: Node Int
original = createMuDontCleanup originalBody

-- | Install the depth-side probe through an unused smart binder.
preloadFirst :: Node Int -> Node Int
preloadFirst node = createMu $ \_ ->
    Node
        [ Edge 0 [depthCapture]
        , Edge 0 [ordinaryCapture]
        , Edge 1 [depthCapture]
        , Edge 2 [node]
        ]

-- | Install the ordinary-side probe through an unused smart binder.
preloadSecond :: Node Int -> Node Int
preloadSecond node = createMu $ \_ ->
    Node
        [ Edge 0 [depthCapture]
        , Edge 0 [ordinaryCapture]
        , Edge 1 [ordinaryCapture]
        , Edge 2 [node]
        ]

-- | Install the later raw representative with its used smart inner binder.
representative :: Node Int -> Node Int
representative node = createMuDontCleanup $ \outer -> createMu $ \inner ->
    Node
        [ Edge 0 [inner]
        , Edge 0 [depthCapture]
        , Edge 0 [ordinaryCapture]
        , Edge 1 [outer]
        , Edge 2 [node]
        ]

-- | Count consecutive stored Mu bodies at the root.
headRank :: Node symbol -> Int
headRank (InternedMu payload) = 1 + headRank (internedMuBody payload)
headRank _ = 0

-- | Count Mu records on each path to a free reference occurrence.
costs :: Node symbol -> [(RecNodeId, Int)]
costs EmptyNode = []
costs (Rec name) = [(name, 0)]
costs (InternedNode payload) = concatMap (concatMap costs . edgeChildren) (internedNodeEdges payload)
costs (InternedUnion payload) = concatMap costs (internedUnionMembers payload)
costs (InternedMu payload) =
    [(name, cost + 1) | (name, cost) <- costs (internedMuBody payload), name /= RecInt (internedMuId payload)]

-- | Select the least free-reference cost, or zero for a closed record.
freeRank :: Node symbol -> Int
freeRank node = case map snd (costs node) of
    [] -> 0
    values -> minimum values

-- | Force each stage before the next stage can populate the global caches.
forceNode :: Node Int -> IO (Node Int)
forceNode node = evaluate (headRank node + freeRank node + length (costs node)) >> evaluate node

-- | Check the source trace and the scope of its callback renaming evidence.
main :: IO ()
main = do
    node <- forceNode original
    _ <- forceNode (preloadFirst node)
    _ <- forceNode (preloadSecond node)
    later <- forceNode (representative node)
    unfolded <- forceNode (unfoldOuterRec node)
    next <- forceNode (unfoldOuterRec unfolded)
    lastNode <- forceNode (unfoldOuterRec next)
    let values = [node, unfolded, next, lastNode]
    print ("head-ranks", map headRank values)
    print ("free-ranks", map freeRank values)
    print ("cached-depths", map numNestedMu values)
    print ("representative-hit", unfolded == later)
    print ("open", map (not . Set.null . freeVars) values)
    print ("unconstrained", map unconstrained values)
    print ("ids", map nodeIdentity values, nodeIdentity later)
    print ("free-vars", map freeVars values)
    unless
        ( map headRank values == [2, 2, 1, 0]
            && map freeRank values == [2, 2, 1, 0]
            && map numNestedMu values == [2, 4, 5, 5]
            && unfolded == later
            && all (not . Set.null . freeVars) values
            && all unconstrained values
            && all ((== Set.fromList [RecDepth, RecUnint 2]) . freeVars) values
        )
        $ fail "The staged source replay differs from the Lean fixture."
    let aliasLeft = substFree RecDepth (Rec (RecUnint 999)) (originalBody depthCapture)
        aliasRight = originalBody (Rec (RecUnint 999))
        aliasLaw = aliasLeft == aliasRight
    print ("captured-depth-renaming-law", aliasLaw)
    print ("captured-depth-renaming-free", freeVars aliasLeft, freeVars aliasRight)
    unless (not aliasLaw && RecDepth `Set.notMember` freeVars aliasLeft && RecDepth `Set.member` freeVars aliasRight) $
        fail "The captured-name renaming witness changed."
    case node of
        InternedMu payload -> do
            let own = RecInt (internedMuId payload)
                body = internedMuBody payload
                ownDepth = substFree own depthCapture body == internedMuDepthShape payload
                ownOrdinary = substFree own (Rec (RecUnint (numNestedMu body))) body == internedMuShape payload
            print ("own-to-depth", ownDepth)
            print ("own-to-ordinary", ownOrdinary)
            unless (ownDepth && ownOrdinary) $ fail "An actual original probe substitution changed."
        _ -> fail "The original raw binder was not retained."
