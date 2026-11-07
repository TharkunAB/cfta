{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Probe retained Mu identities in actual synthesis type annotations.

Run one case per process with @--case NAME@ after a timeout. Each case has
a three-second limit. Reports are observations, not a closure theorem or
a test-suite exit status. Stored graph counts exclude transient allocations.
-}
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Data.CFTA.Equality
import Data.CFTA.Gen.Synthesis
import qualified Data.CFTA.Interned.Type as Physical
import Data.CFTA.Symbol (Symbol (Symbol))
import qualified Data.Set as Set
import Data.Text (Text)
import System.Environment (getArgs)
import System.Timeout (timeout)

-- | Source types and the annotation selected for one independent probe.
data ProbeCase = ProbeCase
    { caseName :: String
    , leftType :: Type
    , rightType :: Type
    , goalType :: Type
    , selectGoal :: Bool
    }
    deriving (Show)

-- | Reachable stored graph counts and the checked identity observations.
data Observation = Observation
    { operation :: String
    , ordinaryNodes :: Int
    , muNodes :: Int
    , unionNodes :: Int
    , storedEdges :: Int
    , retainedMuIds :: [Int]
    , closed :: Bool
    , empty :: Bool
    , muSubsetOfActualU :: Bool
    }
    deriving (Show)

-- | Standard and deliberate catalog-boundary inputs. There is no case matrix.
cases :: [ProbeCase]
cases =
    [ ProbeCase "int" int int int False
    , ProbeCase "list" (list a) (list int) int False
    , ProbeCase "pair-function" (pair a (TFun a (list b))) (pair int (TFun int (list int))) int False
    , ProbeCase "unequal-depth" (pair a (list a)) (pair b (list b)) int False
    , ProbeCase "arrow-catalog" (TCons "->" [a, b, TVar "c"]) (TCons "(->)" []) int False
    , ProbeCase "missing-rigid-var-e" int int (TVar "e") True
    , ProbeCase "fun-unary" (TCons "Fun" [a]) int int False
    ]
  where
    a = TVar "a"
    b = TVar "b"
    int = TCons "Int" []
    list value = TCons "List" [value]
    pair first second = TCons "Pair" [first, second]

{- | Read public annotations from one actual size-one raw search space.
The explicit representatives keep the poly component separate from aliases.
Read stored children to preserve their physical Mu identity.
-}
annotations :: ProbeCase -> Either String (Node Symbol, Node Symbol, Node Symbol, Node Symbol)
annotations spec = do
    let lib =
            Library
                { libraryGroups =
                    [ ("poly", TVar "a", ["poly"])
                    , ("left", leftType spec, ["left"])
                    , ("right", rightType spec, ["right"])
                    ]
                , libraryArgumentOnly = []
                , libraryAvoid = []
                , libraryEncoding = FirstOrder
                }
        raw = rawSearchSpace lib (Query [] (goalType spec)) 1
    case raw of
        Physical.InternedNode stored
            | [outer] <- Physical.internedNodeEdges stored
            , edgeSymbol outer == Symbol "filter"
            , [goal, programs] <- edgeChildren outer -> do
                universe <- annotation "poly" programs
                left <- annotation "left" programs
                right <- annotation "right" programs
                let selected = if selectGoal spec then goal else left
                pure (raw, universe, selected, right)
        _ -> Left "rawSearchSpace did not expose the expected public filter shape"
  where
    annotation :: Text -> Node Symbol -> Either String (Node Symbol)
    annotation name programs =
        case programs of
            Physical.InternedNode stored
                | [edge] <- filter ((== Symbol name) . edgeSymbol) (Physical.internedNodeEdges stored)
                , [child] <- edgeChildren edge ->
                    Right child
            _ -> Left ("missing or non-singleton component annotation: " ++ show name)

-- | Inspect stored bodies without unfolding Mu or following Rec leaves.
observe :: Physical.NodeId -> String -> Node Symbol -> Observation
observe actualU label root =
    let (ordinary, mus, unions, edges) = walk Set.empty Set.empty 0 Set.empty 0 [root]
        identifiers = map number (Set.toAscList mus)
     in Observation
            { operation = label
            , ordinaryNodes = ordinary
            , muNodes = Set.size mus
            , unionNodes = unions
            , storedEdges = Set.size edges
            , retainedMuIds = identifiers
            , closed = Set.null (freeVars root)
            , empty = root == EmptyNode
            , muSubsetOfActualU = all (== actualU) (Set.toList mus)
            }
  where
    number (Physical.NodeId value) = value
    walk seen edges ordinary mus unions pending =
        case pending of
            [] -> (ordinary, mus, unions, edges)
            Physical.EmptyNode : rest -> walk seen edges ordinary mus unions rest
            Physical.Rec _ : rest -> walk seen edges ordinary mus unions rest
            Physical.InternedNode stored : rest
                | Set.member (Physical.internedNodeId stored) seen ->
                    walk seen edges ordinary mus unions rest
                | otherwise ->
                    let rows = Physical.internedNodeEdges stored
                     in walk
                            (Set.insert (Physical.internedNodeId stored) seen)
                            (foldr (Set.insert . Physical.edgeIdentity) edges rows)
                            (ordinary + 1)
                            mus
                            unions
                            (concatMap edgeChildren rows ++ rest)
            Physical.InternedMu stored : rest
                | Set.member (Physical.internedMuId stored) seen ->
                    walk seen edges ordinary mus unions rest
                | otherwise ->
                    walk
                        (Set.insert (Physical.internedMuId stored) seen)
                        edges
                        ordinary
                        (Set.insert (Physical.internedMuId stored) mus)
                        unions
                        (Physical.internedMuBody stored : rest)
            Physical.InternedUnion stored : rest
                | Set.member (Physical.internedUnionId stored) seen ->
                    walk seen edges ordinary mus unions rest
                | otherwise ->
                    walk
                        (Set.insert (Physical.internedUnionId stored) seen)
                        edges
                        ordinary
                        mus
                        (unions + 1)
                        (Physical.internedUnionMembers stored ++ rest)

-- | Compare both intersection orders and one repeated intersection with U.
reportCase :: ProbeCase -> Either String ([Observation], [(String, Bool)], [String])
reportCase spec = do
    (raw, universe, prefix, other) <- annotations spec
    case universe of
        Physical.InternedMu stored ->
            let actualU = Physical.internedMuId stored
                forward = intersect universe prefix
                backward = intersect prefix universe
                repeated = intersect forward universe
                observations =
                    [ observe actualU "rawSearchSpace" raw
                    , observe actualU "U" universe
                    , observe actualU "P" prefix
                    , observe actualU "Q" other
                    , observe actualU "U-intersect-P" forward
                    , observe actualU "P-intersect-U" backward
                    , observe actualU "(U-intersect-P)-intersect-U" repeated
                    , observe actualU "P-intersect-Q" (intersect prefix other)
                    ]
                comparisons =
                    [ ("intersection-order-physical-equality", forward == backward)
                    , ("repeated-physical-equality", repeated == forward)
                    ]
             in Right (observations, comparisons, violations observations)
        _ -> Left "poly annotation is not a stored Mu; actual U identity was not established"

-- | Report violations without converting an observation into a test failure.
violations :: [Observation] -> [String]
violations observations =
    [ operation item ++ ": " ++ issue
    | item <- observations
    , (holds, issue) <-
        [ (closed item, "returned graph is not closed")
        , (muSubsetOfActualU item, "retained Mu identity differs from actual U")
        ]
    , not holds
    ]

{- | Exercise equality reduction of two extracted generalized Pair types.
This observes the occurs-check case; it does not establish its semantics.
-}
reportOccursCheck :: Either String ([Observation], [String])
reportOccursCheck = do
    let spec =
            ProbeCase
                "occurs-check"
                (TCons "Pair" [TVar "a", TVar "a"])
                (TCons "Pair" [TVar "b", TCons "List" [TVar "b"]])
                (TCons "Int" [])
                False
    (_, universe, first, second) <- annotations spec
    case universe of
        Physical.InternedMu stored ->
            let condition = equalityConstraint (mkEqConstraints [[path [0], path [1]]])
                equated = Node [mkEdge (Symbol "equated") [first, second] condition]
                reduced = reducePartially equated
                observations =
                    [ observe (Physical.internedMuId stored) "equated-Pair-prefixes" equated
                    , observe (Physical.internedMuId stored) "reducePartially" reduced
                    ]
             in Right (observations, violations observations)
        _ -> Left "poly annotation is not a stored Mu in the occurs-check case"

{- | Force the complete small report within the timeout before printing it.
Keep the exception handler outside timeout so it cannot absorb the timer.
-}
runBounded :: String -> String -> IO ()
runBounded name report = do
    result <- try (timeout 3000000 (evaluate (length report))) :: IO (Either SomeException (Maybe Int))
    case result of
        Left exception -> putStrLn (name ++ ": EXCEPTION " ++ show exception)
        Right Nothing -> putStrLn (name ++ ": TIMEOUT (3 seconds; rerun later cases in fresh processes)")
        Right (Just _) -> putStrLn (name ++ ": " ++ report)

-- | Run the fixed cases, or select one case for a fresh-process observation.
main :: IO ()
main = do
    arguments <- getArgs
    let available = map caseName cases ++ ["occurs-check"]
        run name
            | name == "occurs-check" = runBounded name (show reportOccursCheck)
            | otherwise =
                case filter ((== name) . caseName) cases of
                    [spec] -> runBounded name (show (reportCase spec))
                    _ -> putStrLn ("Unknown case: " ++ name)
    putStrLn "Returned stored graphs only; no transient-allocation, semantic-equivalence, or termination claim."
    case arguments of
        [] -> mapM_ run available
        ["--list"] -> mapM_ putStrLn available
        ["--case", name] -> run name
        _ -> putStrLn "Usage: AllTypesPrefixClosure [--list | --case NAME]"
