{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Quote an explicit graph in the text format of cfta-serialization.
module Data.CFTA.TH.Automaton (automaton) where

import Data.Char (isUpper)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Haskell.TH
import Language.Haskell.TH.Quote (QuasiQuoter (..))

import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Serialization.Text (explainTextError, graphQuoteNames, parseGraphQuote)
import Data.CFTA.Symbol (Symbol)

{- | Quote an explicit graph. The quote is the graph format of
"Data.CFTA.Serialization.Text" without its @graph 1;@ line:

@
[automaton|
start Expr;
state Expr {
  zero;
  \$one;
  add(Expr, Expr) where \$validAdd;
}
|]
@

@\$name@ takes the place of a symbol, and @where \$name@ the place of a
constraint. The name is a Haskell 'Symbol' or 'Constraint' in scope, and can be
qualified. The quote checks its syntax, its names, and its state rows at compile
time. GHC checks the types of the named values. The result has the type
@Either (TextError String) (PlainFTA String Symbol)@: two names can hold the
same symbol, so 'Data.CFTA.mkFTA' checks the symbol arities when the
expression is evaluated.
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

-- | Check the quote, and read it again with the named values when the expression is evaluated.
quoteAutomaton :: String -> Q Exp
quoteAutomaton contents = case graphQuoteNames $ Text.pack contents of
    Left failure -> fail $ "automaton quote, " <> explainTextError failure
    Right (symbols, constraints) ->
        appsE
            [ varE 'parseGraphQuote
            , values ''Symbol symbols
            , values ''Constraint constraints
            , appE (varE 'Text.pack) (stringE contents)
            ]

-- | A map from each name to its Haskell value, with the type of the value given, so that GHC checks it.
values :: Name -> [Text] -> Q Exp
values typ names = appE (varE 'Map.fromList) $ listE $ map value names
  where
    value name = do
        found <- lookupValueName (Text.unpack name)
        reference <- case found of
            Nothing -> fail $ "automaton quote: " <> Text.unpack name <> " is not in scope"
            Just resolved -> pure $ case nameBase resolved of
                first : _ | isUpper first -> conE resolved
                _ -> varE resolved
        tupE [appE (varE 'Text.pack) (stringE $ Text.unpack name), sigE reference (conT typ)]
