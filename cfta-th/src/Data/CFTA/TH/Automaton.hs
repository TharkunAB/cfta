{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Compile explicit automaton notation to the checked graph constructor.
module Data.CFTA.TH.Automaton (automaton) where

import Data.Char (isUpper)
import Data.String (fromString)
import Language.Haskell.TH
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Text.Parsec (SourcePos)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Syntax.Automaton.Internal

{- | Quote an explicit graph with named states and ordered children:

@
[automaton|
start N;
N = "zero" | "succ"(N);
|]
@

Use @\$name@ for a Haskell 'Symbol' and @where name@ for a Haskell
'Constraint'. Names can be qualified. A symbol binding can have a refinement.
The quote checks the graph structure and binding names at compile time.
GHC checks the binding types. Different bindings can alias the same symbol,
so the result is @Either (FTAError String Symbol) (FTA String Symbol Constraint)@.
'FTA.mkFTA' checks the final symbol arities when the expression is evaluated.

This is an expression quoter. Use 'Data.CFTA.Syntax.Automaton.parseAutomatonWith'
to read the same syntax from a file without Template Haskell.
-}
automaton :: QuasiQuoter
automaton =
    QuasiQuoter
        { quoteExp = quoteAutomaton
        , quotePat = unsupported
        , quoteType = unsupported
        , quoteDec = unsupported
        }
  where
    unsupported _ = fail "automaton is an expression quoter; use it on the right side of a binding"

-- | Parse the quote and generate one call to the existing graph constructor.
quoteAutomaton :: String -> Q Exp
quoteAutomaton contents = case parseDefinition "automaton quote" contents of
    Left err -> fail $ show err
    Right (Definition (_, initial) rows) -> do
        rowsExpression <- ListE <$> traverse quoteRow rows
        resultType <- [t|Either (FTA.FTAError String Symbol) (FTA.FTA String Symbol Constraint)|]
        pure $ SigE (AppE (AppE (VarE 'FTA.mkFTA) (LitE $ StringL initial)) rowsExpression) resultType

-- | Generate a row without changing its alternative order.
quoteRow :: Row -> Q Exp
quoteRow (Row (_, state) alternatives) = do
    transitions <- ListE <$> traverse quoteAlternative alternatives
    pure $ TupE [Just $ LitE $ StringL state, Just transitions]

-- | Generate the symbol and annotation expressions of one transition.
quoteAlternative :: Alternative -> Q Exp
quoteAlternative (Alternative position symbol children annotation) = do
    symbolExpression <- case symbol of
        Literal text -> pure $ AppE (VarE 'fromString) (LitE $ StringL text)
        Bound name -> binding position name
    constraintExpression <- maybe (pure $ VarE 'noConstraint) (uncurry binding) annotation
    pure $
        foldl
            AppE
            (ConE 'FTA.Transition)
            [ symbolExpression
            , ListE [LitE $ StringL child | (_, child) <- children]
            , constraintExpression
            ]

-- | Resolve a Haskell name while retaining the quote position in an error.
binding :: SourcePos -> String -> Q Exp
binding position name = do
    resolved <- lookupValueName name
    case resolved of
        Nothing -> fail $ show position <> ": unknown Haskell binding " <> show name
        Just found -> pure $ case nameBase found of
            first : _ | isUpper first -> ConE found
            _ -> VarE found
