{-# LANGUAGE OverloadedStrings #-}

{- | Equality saturation over the terms of the search, with
"Data.CFTA.EGraph", to decide whether the printed laws prove a law.

The type of a term is its sort. A law gives the rules of its two
directions ('EG.equation'): its template variables are pattern variables,
and its type variables are sort variables.

'equalUnder' builds an e-graph for one query, so its answer depends only on
the laws, the two terms, and the limits.
-}
module Specftacular.EGraph (
    defaultEGraphLimits,
    Law,
    lawSides,
    equalUnder,
) where

import qualified Data.Text as Text

import qualified Data.CFTA.EGraph as EG
import Data.CFTA.Symbol (Symbol (Symbol))

import Specftacular.Rewriting (isTemplateVar, isTypeVar)
import Specftacular.Types

-- | Eight iterations, 4000 e-nodes, and no backoff.
defaultEGraphLimits :: EG.Limits
defaultEGraphLimits = EG.Limits 8 4000 0

-- | The rules of a law.
type Law = [EG.Rule Symbol Symbol]

-- | The rules of a law, or Nothing for a term that is not a law.
lawSides :: Sig -> Term -> Maybe Law
lawSides sig (Term "(==)" [_, l, r]) = EG.equation <$> lawPattern (toTemplate sig l) <*> lawPattern (toTemplate sig r)
lawSides _ _ = Nothing

-- | A side of a law: the first child of a term is its type.
lawPattern :: Term -> Maybe (EG.Pattern Symbol Symbol)
lawPattern (Term h [ty]) | isTemplateVar h = Just (EG.PSorted (sortPattern ty) (EG.PVar (name h)))
lawPattern (Term h (ty : ts)) = EG.PSorted (sortPattern ty) . EG.PNode h <$> traverse lawPattern ts
lawPattern _ = Nothing

sortPattern :: Term -> EG.SortPattern Symbol
sortPattern (Term h []) | isTypeVar h = EG.SVar (name h)
sortPattern (Term h ts) = EG.SNode h (map sortPattern ts)

name :: Symbol -> String
name (Symbol text) = Text.unpack text

{- | Whether the laws make two terms of the search equal within the limits,
and the report of the saturation.
-}
equalUnder :: EG.Limits -> [Law] -> Term -> Term -> (Bool, EG.Report)
equalUnder limits laws a b = (EG.reportStop report == EG.Equal, report)
  where
    (ca, g1) = EG.addTermWith view a EG.emptyEGraph
    (cb, g2) = EG.addTermWith view b g1
    (_, report) = EG.saturateUntilEqual limits (concat laws) ca cb g2
    view (Term s (ty : ts)) = (Just ty, s, ts)
    view (Term s []) = (Nothing, s, [])
