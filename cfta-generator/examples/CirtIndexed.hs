{- | A finite language of function syntax inspired by the indexed Val example
in section 2.1.4 of CIRT (arXiv:2611.20867). A program is a Boolean literal,
the identity, a constant function, or a function that calls its argument.
-}
module Main (main) where

import Control.Monad (forM, unless)
import Data.List (sort)

import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (everyRank)
import qualified Data.CFTA.Interned as FTA
import Data.CFTA.Term (Term (Node))

-- | The type index of a closed program.
data Type = Bit | Arrow Type Type deriving (Eq, Ord, Show)

{- | Construct the state for a type. Each child index is a proper subterm of
the parent index. In particular, @at x@ denotes @\f -> f x@. Its child has
the argument type of the callback.
-}
programs :: Type -> FTA.Node String
programs Bit = FTA.Node [FTA.Edge "false" [], FTA.Edge "true" []]
programs (Arrow input result) =
    FTA.Node $
        [FTA.Edge "const" [programs result]]
            <> [FTA.Edge "id" [] | input == result]
            <> [FTA.Edge "at" [programs argument] | Arrow argument returned <- [input], returned == result]

-- | All types up to an arrow depth. A base type has depth zero.
types :: Int -> [Type]
types depth
    | depth <= 0 = [Bit]
    | otherwise = Bit : [Arrow input result | input <- smaller, result <- smaller]
  where
    smaller = types (depth - 1)

-- | All raw programs up to a constructor depth. A leaf has depth zero.
syntax :: Int -> [Term String]
syntax depth =
    [Node name [] | name <- ["false", "true", "id"]]
        <> [Node name [child] | depth > 0, name <- ["at", "const"], child <- syntax (depth - 1)]

{- | Infer every type a raw program can have in the finite set of indices.
The set must contain Bit and the subterms of each index.
-}
infer :: [Type] -> Term String -> [Type]
infer indices = go
  where
    go (Node name []) | name `elem` ["false", "true"] = [Bit]
    go (Node "id" []) = [Arrow t t | t <- indices, Arrow t t `elem` indices]
    go (Node name [child]) = filter (`elem` indices) $ do
        t <- go child
        other <- indices
        case name of
            "const" -> [Arrow other t]
            "at" -> [Arrow (Arrow t other) other]
            _ -> []
    go _ = []

-- | Values used to execute a closed program.
data Value = Boolean Bool | Function (Value -> Maybe Value)

-- | Apply a function value.
apply :: Value -> Value -> Maybe Value
apply (Function f) = f
apply (Boolean _) = const Nothing

-- | Execute the program using ordinary Haskell functions.
evaluate :: Term String -> Maybe Value
evaluate (Node "false" []) = Just (Boolean False)
evaluate (Node "true" []) = Just (Boolean True)
evaluate (Node "id" []) = Just (Function Just)
evaluate (Node "const" [child]) = do
    value <- evaluate child
    pure (Function (const (Just value)))
evaluate (Node "at" [child]) = do
    argument <- evaluate child
    pure (Function (\callback -> apply callback argument))
evaluate _ = Nothing

-- | Check every type and rank. Call two generated programs with negation.
main :: IO ()
main = do
    let bound = 3
        indices = types bound
        raw = syntax bound
        inferred = [(program, infer indices program) | program <- raw]
    counts <- forM indices $ \index -> do
        let gen = Gen.fromAutomaton (programs index)
            expected = sort [program | (program, ts) <- inferred, index `elem` ts]
        ranks <- either (fail . show) (pure . everyRank) (Gen.cardinality gen)
        decoded <- either (fail . show) pure (traverse (Gen.unrank gen) ranks)
        unless (sort decoded == expected && traverse (Gen.rankOfTerm gen) decoded == Right ranks) $
            fail ("language or rank mismatch at " <> show index)
        pure (length decoded)
    let callbackIndex = Arrow (Arrow Bit Bit) Bit
        callbacks = Gen.fromAutomaton (programs callbackIndex)
        at name = Node "at" [Node name []]
        negateValue (Boolean b) = Just (Boolean (not b))
        negateValue (Function _) = Nothing
        run name = do
            rank <- Gen.rankOfTerm callbacks (at name)
            program <- Gen.unrank callbacks rank
            pure $ do
                f <- evaluate program
                Boolean b <- apply f (Function negateValue)
                pure b
    unless (map run ["false", "true"] == [Right (Just True), Right (Just False)]) $
        fail "a callback received the wrong Boolean"
    unless
        ( callbackIndex `notElem` infer indices (at "id")
            && Gen.rankOfTerm callbacks (at "id") == Left Gen.TermNotInLanguage
        )
        $ fail "a callback expecting a Boolean received a function"
    putStrLn $
        show (length indices)
            <> " type indices, "
            <> show (length raw)
            <> " raw programs, "
            <> show (sum counts)
            <> " typed programs across indices; all ranks replayed"
