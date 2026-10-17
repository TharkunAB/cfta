-- | Self-contained JSON snapshots of explicit graphs, documents, and languages.
module Data.CFTA.Serialization.JSON (
    DecodeError (..),
    explainDecodeError,
    encodeGraph,
    decodeGraph,
    encodeDocument,
    decodeDocument,
    encodeLanguage,
    decodeLanguage,
) where

import Data.CFTA.Serialization.Internal.JSON
