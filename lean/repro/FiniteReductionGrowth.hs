-- | Check structural growth during a finite equality reduction.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.CFTA.Constraint (Guard (..), semanticConstraint)
import qualified Data.CFTA.Equality as Equality
import qualified Data.CFTA.Term as Term
import qualified Data.Set as Set
import System.Timeout (timeout)

-- | Give the same leaf different residual guard representations.
leaf :: Guard -> Equality.Node String
leaf guard = Equality.Node [Equality.mkEdge "a" [] (semanticConstraint guard)]

-- | Add one binary constructor and its residual guard.
guardedPair :: Guard -> Equality.Node String -> Equality.Node String -> Equality.Node String
guardedPair guard left right = Equality.Node [Equality.mkEdge "f" [left, right] (semanticConstraint guard)]

-- | Add one unconstrained binary constructor.
pair :: Equality.Node String -> Equality.Node String -> Equality.Node String
pair = guardedPair Top

-- | Two acyclic domains with one possible term and different row representations.
initial :: [Equality.Node String]
initial = [left, right]
  where
    same = Same (Equality.path []) (Equality.path [])
    a = leaf Top
    b = leaf same
    c = leaf (Or [same])
    d = leaf (Not Bottom)
    aa = pair a a
    ab = pair a b
    ba = pair b a
    ac = pair a c
    ca = pair c a
    left =
        pair
            (pair ac ab)
            ( Equality.union
                [ pair (Equality.union [ab, ba]) (Equality.union [pair a d, ca])
                , pair (Equality.union [guardedPair (Not Bottom) a b, ca]) ac
                ]
            )
    right = Equality.union [pair (pair aa aa) (pair ba aa), pair (pair ca ab) (pair ba aa)]

-- | The two classes cross between the first and second child domains.
classes :: Equality.EqConstraints
classes =
    Equality.mkEqConstraints
        [ [Equality.path [0, 0], Equality.path [1, 1]]
        , [Equality.path [0, 1], Equality.path [1, 0]]
        ]

{- | Instrument one source pass on this fixture.
All required paths exist. Each class contains two paths with no prefix overlap.
-}
pass :: [Equality.Node String] -> [Equality.Node String]
pass nodes = foldr reduceClass nodes (Equality.unsafeSubsumptionOrderedEclasses classes)
  where
    reduceClass paths old = foldr (\(path, target) -> Equality.modifyAtPath (Equality.intersect target) path) old edits
      where
        members = Set.toAscList (Equality.unPathEClass paths)
        edits = [(path, intersection [Equality.getPath other old | other <- members, other /= path]) | path <- members]
    intersection [] = Equality.EmptyNode
    intersection (node : rest) = foldr Equality.intersect node rest

-- | Construct the only term shape that the fixture can represent.
perfect :: Int -> Term.Term String
perfect 0 = Term.Node "a" []
perfect depth = let child = perfect (depth - 1) in Term.Node "f" [child, child]

-- | Check that every stored row has exactly the supplied term shape.
onlyShape :: Term.Term String -> Equality.Node String -> Bool
onlyShape (Term.Node symbol children) node = all matches (Equality.nodeEdges node)
  where
    matches edge =
        Equality.edgeSymbol edge == symbol
            && length (Equality.edgeChildren edge) == length children
            && and (zipWith onlyShape children (Equality.edgeChildren edge))

-- | Show that structural intersection does not satisfy absorption.
checkAbsorption :: IO ()
checkAbsorption = do
    let same = Same (Equality.path []) (Equality.path [])
        first = Equality.union [leaf same, leaf (Or [same])]
        second = leaf (Not Bottom)
        once = Equality.intersect first second
        twice = Equality.intersect first once
    print ("absorption", once == twice, length (Equality.nodeEdges once), length (Equality.nodeEdges twice))
    unless (once /= twice) $ fail "The source representation now satisfies this absorption case."

-- | Check each pass and return its first structural fixed point.
walk :: Int -> [Equality.Node String] -> IO [Equality.Node String]
walk count nodes = do
    print (count, map Equality.edgeCount nodes, map Equality.nodeCount nodes)
    let term = perfect 3
    unless
        ( all (onlyShape term) nodes
            && all (`Equality.accepts` term) nodes
            && all ((== 0) . Equality.numNestedMu) nodes
            && all (Set.null . Equality.freeVars) nodes
        )
        $ fail "A pass changed the singleton finite language."
    let next = pass nodes
    if next == nodes
        then do
            unless (count == 6) $ fail "The fixture no longer needs six changing rounds."
            pure nodes
        else if count == 12 then fail "The diagnostic exceeded its round bound." else walk (count + 1) next

-- | Compare the instrumented schedule with the public fixed-point operation.
main :: IO ()
main = do
    checkAbsorption
    expected <- walk 0 initial
    result <- timeout 5000000 $ do
        let reduced = Equality.reduceEqConstraints classes Equality.EmptyConstraints initial
        _ <- evaluate (sum (map Equality.edgeCount reduced))
        pure reduced
    case result of
        Nothing -> fail "The public finite reduction did not finish."
        Just reduced -> do
            unless (reduced == expected) $ fail "The public result differs from the instrumented fixed point."
            print ("public-fixed-point", reduced == pass reduced)
