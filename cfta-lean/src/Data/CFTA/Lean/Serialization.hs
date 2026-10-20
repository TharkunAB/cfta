{-# LANGUAGE OverloadedStrings #-}

-- | Save a language with the logical context required to interpret it.
module Data.CFTA.Lean.Serialization (
    Context (..),
    Snapshot (..),
    printSnapshot,
    parseSnapshot,
) where

import Data.Bifunctor (first)
import Data.Text (Text)
import qualified Data.Text as Text

import Data.CFTA.Formula (Formula, Name, Sort)
import Data.CFTA.Language (Language)
import Data.CFTA.Lean.Theory (Theory)
import qualified Data.CFTA.Serialization.Text as Language

{- | The interpretation of a language's logical names and values.
Native definitions require the same external Lean and Mathlib environment.
Server addresses, solver caches, and proof results are not part of this data.
-}
data Context = Context
    { contextTheory :: Theory
    , contextDeclarations :: [(Name, Sort)]
    , contextAssumptions :: [Formula]
    }
    deriving (Eq, Show, Read)

-- | An editable language and the logical context required to query it.
data Snapshot state = Snapshot
    { snapshotContext :: Context
    , snapshotLanguage :: Language state
    }
    deriving (Eq, Show)

{- | Print the context followed by the complete readable language.
The context uses derived 'Show' and 'Read' instances. The language uses the
standard language codec, including source facts, exclusions, and row order.
-}
printSnapshot :: (Show state) => Snapshot state -> Text
printSnapshot snapshot =
    "lean-language 1;\n"
        <> Text.pack (show $ snapshotContext snapshot)
        <> "\n"
        <> Language.printLanguage (snapshotLanguage snapshot)

{- | Restore the context and validate the language structure without a solver.
Native definitions are trusted Lean code. Querying a snapshot can execute that
code on the configured Kimina server. Parsing does not execute it.
-}
parseSnapshot :: (Ord state, Read state, Show state) => Text -> Either String (Snapshot state)
parseSnapshot input = do
    body <- maybe (Left "expected lean-language 1;") Right $ Text.stripPrefix "lean-language 1;" input
    case reads (Text.unpack body) of
        [(context, rest)] ->
            Snapshot context
                <$> first Language.explainTextError (Language.parseLanguage $ Text.stripStart $ Text.pack rest)
        _ -> Left "invalid Lean language context"
