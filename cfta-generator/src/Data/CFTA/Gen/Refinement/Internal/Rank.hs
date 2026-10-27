{- | Ranks of a surface in a compiled refinement generator.

The engine terms of a compiled generator carry private structure: the choice
index, the keyed joins of the arguments, and labels that name the integers
under them. A user term has none of it. The support of the generator is the
automaton of the engine terms, so a user term is matched against the support.
The match is by the surface of the engine term ('Data.CFTA.Gen.Label.surface'):
a private node adds nothing, and its children are read in order. The match
finds the engine terms whose surface is the given term. 'ranksOf' then ranks
each of them, and it checks the whole term, so a term that is not in the
language has no rank.

An integer leaf is the leaf of the support with the symbol of
'integersText'. It matches a leaf of the term whose symbol is the integer.
The integers bind where they match. A constructor takes its exact label from
the integers under it, in the order of the engine term, as
'Data.CFTA.Gen.Refinement.Internal.Compile.exactLabel' does when 'compile'
fills the term. So the order of the engine term decides the labels, and not
the order of the term.
-}
module Data.CFTA.Gen.Refinement.Internal.Rank (
    ranksOfSurface,
) where

import Control.Monad.State.Strict (State, evalState, gets, modify')
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Text.Read (readMaybe)

import qualified Data.CFTA as FTA
import Data.CFTA.Gen
import Data.CFTA.Gen.Refinement.Internal.Compile (exactLabel, integerSymbol, integersText)
import Data.CFTA.Index (Rank)
import Data.CFTA.Interned (InternedState, stateOf, toRows)
import Data.CFTA.Symbol (Symbol, symbolText)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | An engine term with the integers under it, in the order of the engine term, and the rest of the forest.
type Match = (Term (Label Symbol), [Integer], [Term Symbol])

type Rows = Map.Map InternedState [FTA.Transition InternedState (Label Symbol) ()]

{- | The ranks of a term in a generator. The symbols of the term are ordinary
symbols: a constructor by its name, and an integer leaf by its integer. A
term that the generator does not hold has no rank. One term can have several
ranks, as for 'ranksOf'.
-}
ranksOfSurface :: Gen Symbol a -> Term Symbol -> Either GenError [Rank]
ranksOfSurface generator target = do
    root <- support generator
    let rows = fmap (map (fmap (const ()))) (toRows root)
        candidates = [term | (term, _, []) <- evalState (matchPrefix rows (stateOf root) [target]) Map.empty]
    nubOrd . concat <$> traverse (ranksOf generator) (nubOrd candidates)

-- | The matches of the surface of a state with a prefix of a forest, memoized by state and forest.
matchPrefix :: Rows -> InternedState -> [Term Symbol] -> State (Map.Map (InternedState, [Term Symbol]) [Match]) [Match]
matchPrefix rows state forest = do
    known <- gets (Map.lookup (state, forest))
    case known of
        Just matches -> pure matches
        Nothing -> do
            matches <- concat <$> traverse viaTransition (Map.findWithDefault [] state rows)
            modify' (Map.insert (state, forest) matches)
            pure matches
  where
    viaTransition transition = case (FTA.transitionSymbol transition, forest) of
        (Label label, Term.Node symbol children : rest)
            | symbolText label == integersText ->
                pure
                    [ (Term.Node (Label (integerSymbol value)) [], [value], rest)
                    | null children
                    , Just value <- [readMaybe $ Text.unpack $ symbolText symbol]
                    ]
            | symbolText label /= symbolText symbol -> pure []
            | otherwise -> do
                inside <- sequential (FTA.transitionChildren transition) children
                pure [(Term.Node (Label (exactLabel integers label)) terms, integers, rest) | (terms, integers, []) <- inside]
        (Label _, []) -> pure []
        (private, _) -> do
            inside <- sequential (FTA.transitionChildren transition) forest
            pure [(Term.Node private terms, integers, rest) | (terms, integers, rest) <- inside]
    sequential [] rest = pure [([], [], rest)]
    sequential (child : others) input = do
        firsts <- matchPrefix rows child input
        concat
            <$> traverse
                ( \(term, integers, rest) -> do
                    laters <- sequential others rest
                    pure [(term : terms, integers <> more, rest') | (terms, more, rest') <- laters]
                )
                firsts
