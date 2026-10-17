{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (Exception, SomeException, evaluate, throwIO, try)
import Control.Monad (forM, forM_, unless, when)
import Data.CFTA.Equality
import Data.IORef
import Data.List (find)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import System.Environment (getArgs)
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdout)
import System.Timeout (timeout)

type Key = (EqConstraints, Node String)

data Cell = Active | Returned (Node String)

data Stats = Stats {calls :: Int, hits :: Int, maximumActive :: Int}
    deriving (Show)

data SearchFault = Busy Key [Key] | Limit [Key]
    deriving (Show, Typeable)

instance Exception SearchFault

-- The association list uses Eq, hence the actual interned equality identity.
-- It does not identify keys by class denotation or by an occurrence label.
instrumented :: Int -> Node String -> IO (Node String, Stats)
instrumented limit root = do
    table <- newIORef []
    stats <- newIORef (Stats 0 0 0)
    let go stack inherited value = do
            let key = (inherited, value)
            modifyIORef' stats (\s -> s {calls = calls s + 1})
            s <- readIORef stats
            when (calls s > limit) (throwIO (Limit stack))
            known <- readIORef table
            case lookup key known of
                Just Active -> throwIO (Busy key stack)
                Just (Returned result) -> do
                    modifyIORef' stats (\t -> t {hits = hits t + 1})
                    pure result
                Nothing -> do
                    modifyIORef' table ((key, Active) :)
                    let entered = key : stack
                    modifyIORef' stats (\t -> t {maximumActive = max (maximumActive t) (length entered)})
                    result <- case value of
                        EmptyNode -> pure EmptyNode
                        Mu _ -> pure value
                        InternedUnion _ -> pure value
                        Rec _ -> fail "source-built search reached an open reference"
                        Node edges -> do
                            narrowed <- forM edges $ \edge -> do
                                current <- evaluate (reduceEdgeIntersection inherited edge)
                                let combined = combineEqConstraints inherited (equalities (edgeConstraint current))
                                children <- case combined of
                                    EqContradiction -> pure (map (const EmptyNode) (edgeChildren current))
                                    _ -> forM (zip [0 ..] (edgeChildren current)) $ \(index, child) ->
                                        go entered (eqConstraintsDescend combined index) child
                                evaluate (setChildren current children)
                            evaluate (modifyNode value (const narrowed))
                    modifyIORef' table (map (\entry@(old, _) -> if old == key then (old, Returned result) else entry))
                    pure result
    result <- go [] EmptyConstraints root
    final <- readIORef stats
    pure (result, final)

leaf :: Node String
leaf = Node [Edge "a" []]

tau :: Node String
tau = Mu (\self -> Node [Edge "a" [], Edge "p" [self, self]])

tauStep :: Node String
tauStep = Mu (\self -> Node [Edge "a" [], Edge "p" [Node [Edge "p" [self, self]], self]])

classes :: [EqConstraints]
classes = map (mkEqConstraints . map (map (path . map ChildIndex)))
    [ [[ [0], [1] ]]
    , [[ [0], [1, 0] ]]
    , [[ [0, 0], [1] ]]
    , [[ [0, 0], [1, 0] ]]
    , [[ [0], [1, 0, 0] ]]
    , [[ [0, 0, 0], [1] ]]
    , [[ [0], [1, 0], [1, 1] ]]
    , [[ [0, 0], [1, 0] ], [[0, 1], [1, 1]]]
    , [[ [0], [1, 0, 0] ], [[0, 1], [1, 0, 1]]]
    , [[ [0, 0], [1, 1, 0] ], [[0, 1], [1, 0, 1]]]
    ]

same :: EqConstraints
same = mkEqConstraints [[path [0], path [1]]]

nest :: Int -> EqConstraints -> Node String
nest 0 _ = leaf
nest depth own = let child = nest (depth - 1) own in pair own child child

pair :: EqConstraints -> Node String -> Node String -> Node String
pair own left right = Node [mkEdge "p" [left, right] (equalityConstraint own)]

-- The first two levels repeat raw guards at distinct source positions.
-- The staggered pair places a guard above and below distinct plain wrappers.
family :: [(String, Node String)]
family =
    [("historical-fixed-cycle", repairedCycle)]
        ++ [("base-" ++ show i ++ "-" ++ show j, pair outer left right)
           | (i, outer) <- zip [0 :: Int ..] classes
           , let b = pair same leaf leaf
           , (j, (left, right)) <- zip [0 :: Int ..] [(b, tau), (tau, b), (b, tauStep), (tauStep, b), (b, b)]
           ]
        ++ [("nested-" ++ show ownIndex ++ "-" ++ show depth ++ "-" ++ show outerIndex ++ "-" ++ show orientation,
                pair outer left right)
           | (ownIndex, own) <- zip [0 :: Int ..] classes
           , depth <- [1 .. 4 :: Int]
           , let base = nest depth own
           , (outerIndex, outer) <- zip [0 :: Int ..] classes
           , (orientation, (left, right)) <- zip [0 :: Int ..] [(base, tau), (tau, base), (base, tauStep), (tauStep, base)]
           ]
        ++ [("staggered-" ++ show i ++ "-" ++ show j ++ "-" ++ show k,
                pair outer (pair first good good) (pair EmptyConstraints bad bad))
           | (i, first) <- zip [0 :: Int ..] classes
           , (j, second) <- zip [0 :: Int ..] classes
           , (k, outer) <- zip [0 :: Int ..] classes
           , let good = pair EmptyConstraints tau tau
           , let bad = pair second tau tau
           ]
        ++ [("cross-copy-" ++ show i ++ "-" ++ show j ++ "-" ++ show k,
                pair outer (pair first leaf tau) (pair second tau leaf))
           | (i, first) <- zip [0 :: Int ..] classes
           , (j, second) <- zip [0 :: Int ..] classes
           , (k, outer) <- zip [0 :: Int ..] classes
           ]
  where
    repairedCycle =
        let wrap value = Node [Edge "w" [value]]
            plain = Mu (\self -> Node [Edge "a" [], Edge "p" [wrap self, wrap self]])
            next = Node [Edge "p" [wrap plain, wrap plain]]
            constrained = Mu (\self -> Node [Edge "a" [], mkEdge "p" [wrap self, wrap next] (equalityConstraint same)])
         in Node [mkEdge "p" [wrap constrained, wrap next] (equalityConstraint same)]

checkOne :: (String, Node String) -> IO Stats
checkOne (label, root) = do
    unless (Set.null (freeVars root)) (fail (label ++ ": open initial source"))
    observed <- timeout 1500000 (try (instrumented 10000 root))
    case observed of
        Nothing -> fail (label ++ ": local-operation timeout")
        Just (Left fault) -> do
            putStrLn ("CANDIDATE " ++ label ++ " " ++ show (fault :: SomeException))
            print root
            host <- timeout 1500000 (evaluate (nodeIdentity (reducePartially root)))
            putStrLn ("ACTUAL " ++ show host)
            fail (label ++ ": inspect candidate")
        Just (Right (result, stats)) -> do
            host <- timeout 1500000 (evaluate (nodeIdentity (reducePartially root)))
            unless (host == Just (nodeIdentity result)) $
                fail (label ++ ": actual host identity mismatch or timeout: " ++ show host)
            pure stats

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    arguments <- getArgs
    let selected = case arguments of
            [label] -> maybe [] pure (find ((== label) . fst) family)
            [] -> family
            _ -> []
    unless (not (null selected)) (fail "no selected cases")
    totals <- newIORef (0, Stats 0 0 0)
    forM_ selected $ \candidate -> do
        stats <- checkOne candidate
        modifyIORef' totals $ \(count, total) ->
            ( count + 1
            , Stats (calls total + calls stats) (hits total + hits stats) (max (maximumActive total) (maximumActive stats))
            )
        (count, _) <- readIORef totals
        when (count `mod` 100 == 0) (putStrLn ("checked " ++ show count))
    readIORef totals >>= print
