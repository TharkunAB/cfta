{-# LANGUAGE OverloadedStrings #-}

-- | Save, reopen, inspect, and query one recursive constrained language.
module Main (main) where

import Control.Exception (bracketOnError, finally)
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Text.Encoding as Text
import qualified Data.Tree as Tree
import System.Directory (removeFile, renameFile)
import System.Environment (getArgs)
import System.FilePath (takeDirectory)
import System.IO (hClose, openBinaryTempFile)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Guard (Satisfies),
    conjoinConstraints,
    equalityConstraint,
    noConstraint,
    semanticConstraint,
 )
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Serialization.Text (explainTextError, parseGraph, printGraph)
import qualified Data.CFTA.Sized as Sized
import Data.CFTA.Symbol (Symbol (RefinedSymbol), eraseRefinements)

-- | The source state identities have a derived exact label codec.
data State = Atom | Expr deriving (Eq, Ord, Show, Read)

-- | The graph retains recursion, refinements, and a constraint on equal children.
graph :: FTA.PlainFTA State Symbol
graph =
    either (error . show) id $
        FTA.mkFTA
            Expr
            [ (Expr, [FTA.Transition "pair" [Atom, Atom] samePositive, FTA.Transition "wrap" [Expr] noConstraint])
            , (Atom, [FTA.Transition zero [] noConstraint, FTA.Transition one [] noConstraint])
            ]
  where
    zero = RefinedSymbol "zero" $ refinementFormula (.== 0)
    one = RefinedSymbol "one" $ refinementFormula (.== 1)
    samePositive =
        conjoinConstraints
            (equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
            (semanticConstraint $ Satisfies (path [0]) $ refinementFormula (.> 0))

-- | Replace the target only after the complete file has been written and closed.
save :: FilePath -> IO ()
save target =
    bracketOnError
        (openBinaryTempFile (takeDirectory target) ".cfta-graph")
        (\(temporary, handle) -> hClose handle `finally` removeFile temporary)
        ( \(temporary, handle) -> do
            ByteString.hPut handle $ ByteString.fromStrict $ Text.encodeUtf8 $ printGraph graph
            hClose handle
            renameFile temporary target
        )

-- | Display the complete graph, then rebuild its structural size queries.
inspect :: FTA.PlainFTA State Symbol -> IO ()
inspect restored = do
    putStr $ Tree.drawTree $ fmap (either show show) $ FTA.toTree restored
    withZ3 [] $ \solver -> do
        classes <- Sized.sizedUpTo solver 5 restored >>= either (fail . show) pure
        print [Sized.countOfSize classes size | size <- [1 .. 5]]
        print [fmap eraseRefinements $ Sized.unrankOfSize classes size 0 | size <- [3 .. 5]]

-- | Run the example in memory, or save and reopen it in separate processes.
main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        [] -> either (fail . explainTextError) inspect $ parseGraph $ printGraph graph
        ["save", target] -> save target
        ["load", source] -> do
            bytes <- ByteString.readFile source
            text <- either (fail . show) pure $ Text.decodeUtf8' $ ByteString.toStrict bytes
            either (fail . explainTextError) inspect $ parseGraph text
        _ -> fail "usage: cfta-graph-snapshot [save FILE | load FILE]"
