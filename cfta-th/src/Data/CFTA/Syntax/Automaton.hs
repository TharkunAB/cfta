-- | Read explicit automata with the same syntax as the automaton quoter.
module Data.CFTA.Syntax.Automaton (parseAutomaton, parseAutomatonWith) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.String (fromString)
import Text.Parsec (ParseError)

import Data.CFTA (FTA)
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Syntax.Automaton.Internal

{- | Parse an automaton with literal symbols and no named constraints.
The first argument names the source in diagnostics. Cycles and empty rows
are valid. Each symbol must have one arity throughout the graph.
-}
parseAutomaton :: FilePath -> String -> Either ParseError (FTA String Symbol Constraint)
parseAutomaton source = parseAutomatonWith source Map.empty Map.empty

{- | Parse an automaton with named symbols and constraints. A symbol binding
can contain a refined symbol. Unknown bindings and structural errors include
their source positions. Constraint interpretation stays with the existing
automaton APIs. This function does not start a solver or enumerate terms.
-}
parseAutomatonWith ::
    FilePath ->
    Map String Symbol ->
    Map String Constraint ->
    String ->
    Either ParseError (FTA String Symbol Constraint)
parseAutomatonWith source symbols constraints contents = do
    definition <- parseDefinition source contents
    resolveDefinition show resolveSymbol resolveConstraint noConstraint definition
  where
    resolveSymbol _ (Literal text) = Right $ fromString text
    resolveSymbol position (Bound name) =
        maybe (Left $ errorAt position $ "unknown symbol binding " <> show name) Right $ Map.lookup name symbols
    resolveConstraint position name =
        maybe (Left $ errorAt position $ "unknown constraint binding " <> show name) Right $ Map.lookup name constraints
