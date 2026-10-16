{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

-- Draft source-review reproducer. It has not been compiled or run.
-- The independent predicate checks the invariant at every Chain node.
module Main (main) where

import Data.CFTA.Gen.Refinement.Derive
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Refinement.Expression (Expr, Literal (..))
import qualified Data.CFTA.Gen.Refinement as G
import GHC.Generics (Generic)

-- Each nonnegative integer encodes one finite value.
data Chain = End Bool | Next Chain
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (HasFTA)

instance Literal Chain where
    toLiteral (End False) = 0
    toLiteral (End True) = 1
    toLiteral (Next rest) = 2 + toLiteral rest
    fromLiteral 0 = End False
    fromLiteral 1 = End True
    fromLiteral value
        | value >= 2 = Next (fromLiteral (value - 2))
        | otherwise = error "negative integer outside the Chain encoding"
    literalRange = (Just (End False), Nothing)

data ChainNode e = EndNode e | NextNode e
    deriving stock (Generic)
    deriving anyclass (NodeView)

rules :: Invariant ChainNode NoMeasures
rules = Contracted $ \case
    EndNode flag -> flag .== literal True
    NextNode _ -> true

pools :: ChainNode Expr -> [FieldPool]
pools (NextNode rest) = [rest `drawnFrom` G.elements [End False]]
pools (EndNode _) = []

selected :: Atoms
selected = fieldAtoms @Chain pools <> atom @Bool (G.elements [False, True])

wide :: Atoms
wide = atom @Chain (G.elements [End False]) <> atom @Bool (G.elements [False, True])

allNodes :: Chain -> Bool
allNodes (End flag) = flag
allNodes (Next rest) = allNodes rest

main :: IO ()
main = do
    let value = Next (End False)
    putStrLn "(field holds, type-wide holds, independent all-node invariant):"
    print (holds selected rules value, holds wide rules value, allNodes value)
    putStrLn "High-level field-local derivation status:"
    print (fmap (const ()) (deriveLTAFrom @Chain 0 selected rules))
    putStrLn "High-level type-wide replacement status:"
    print (fmap (const ()) (deriveLTAFrom @Chain 0 wide rules))
    putStrLn "Field-local generated values and independent validity:"
    case deriveLTAFrom @Chain 0 selected rules of
        Left problem -> print problem
        Right generator -> do
            compiled <- G.compile generator
            print (fmap (map (\member -> (member, allNodes member))) (G.values compiled))
