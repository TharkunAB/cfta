-- | Write the text of an expression through a mask, one character at a time, and see where the mask refuses a sum.
module Main (main) where

import Control.Monad (foldM, unless)

import Data.CFTA.Gen.ExpressionLanguage (
    equalCompletions,
    equalTextMask,
    expressionSizeBound,
    expressionText,
    expressionTexts,
    structuralAutomaton,
 )
import Data.CFTA.Index (Cardinality (..), Size (..))
import Data.CFTA.Mask
import Data.CFTA.Mask.Text
import Data.CFTA.Mask.Vocabulary (vocabulary, vocabularyMask)
import Data.CFTA.Sized.Prefix (completionCount, prefixCompletions)
import Data.CFTA.Term (Term (Node))

-- | An expression whose sum has two equal children: @(a)+(a)*b@.
equalExpression :: Term Char
equalExpression = Node '*' [Node '+' [Node '(' [Node 'a' []], Node '(' [Node 'a' []]], Node 'b' []]

-- | A sum with two different children: @a+b@.
unequalSum :: Term Char
unequalSum = Node '+' [Node 'a' [], Node 'b' []]

-- | The mask of the texts of the expressions without the equality, up to the same bound.
structuralTextMask :: Mask TextToken (Term Char)
structuralTextMask =
    textMask expressionTexts . completionsMask . either (error . show) id $
        prefixCompletions (Size expressionSizeBound) structuralAutomaton

-- | The characters of a prefix of a text.
characters :: Mask TextToken term -> String
characters mask = [character | Character character <- maskPrefix mask]

-- | A token as text.
showToken :: TextToken -> String
showToken token = case token of
    Character character -> [character]
    EndOfText -> "<end>"

-- | The offered tokens of a mask as text.
offeredText :: Mask TextToken term -> String
offeredText = unwords . map (showToken . fst) . maskNext

{- | Write a text one token at a time, then the end of the text. At each step
the token must be one that the mask offers. The result is the mask after the
end, or the place, the token, the reason, and the offered tokens of the first
refusal. The function prints one line for each step.
-}
write :: Mask TextToken term -> String -> IO (Either (Int, TextToken, Refusal, [TextToken]) (Mask TextToken term))
write start written = go 0 start $ map Character written <> [EndOfText]
  where
    go _ mask [] = pure $ Right mask
    go place mask (token : rest) = do
        let offered = map fst $ maskNext mask
        putStrLn $ "  " <> show (characters mask) <> " offers " <> offeredText mask
        case maskStep mask token of
            Left refusal -> pure $ Left (place, token, refusal, offered)
            Right after -> do
                unless (token `elem` offered) $ fail $ "the mask steps a token that it does not offer: " <> show token
                go (place + 1) after rest

main :: IO ()
main = do
    -- 1. The mask of the texts of the expressions with the equality.
    let count = completionCount equalCompletions
    putStrLn $ "1. The mask has the texts of " <> show count <> " expressions with the equality."
    putStrLn $ "  at the empty prefix: " <> offeredText equalTextMask
    unless (count == Cardinality 472) $ fail $ "wrong number of expressions: " <> show count

    -- 2. A decoder loop with 'maskNext' and 'maskStep' writes the text of an expression.
    putStrLn $ "2. Write " <> expressionText equalExpression
    ended <- write equalTextMask (expressionText equalExpression)
    case ended of
        Right mask -> do
            putStrLn $ "  the term: " <> show (maskTerms mask)
            unless (maskTerms mask == [equalExpression]) $ fail "wrong term"
        Left refused -> fail $ "the mask refuses an expression with the equality: " <> show refused

    -- 3. The same loop refuses the text of a sum with two different children at the first character that only such a sum has.
    putStrLn $ "3. Write " <> expressionText unequalSum
    refused <- write equalTextMask (expressionText unequalSum)
    case refused of
        Left (place, token, refusal, offered) -> do
            putStrLn $ "  refused at place " <> show place <> " after " <> show (take place $ expressionText unequalSum)
            putStrLn $ "  token " <> show token <> ", reason " <> show refusal <> ", offered " <> show offered
            unless ((place, refusal, offered) == (2, TokenRejected, [Character 'a'])) $ fail "wrong place, reason, or tokens"
        Right _ -> fail "the mask accepts a sum with two different children"

    -- 4. Without the equality, the mask offers b after a+, as a grammar of the texts does.
    let structural = foldM maskStep structuralTextMask $ map Character "a+"
    putStrLn $ "4. Without the equality, \"a+\" offers " <> either show offeredText structural
    unless (fmap (map fst . maskNext) structural == Right [Character '(', Character 'a', Character 'b']) $
        fail "wrong tokens without the equality"

    -- 5. 'readText' does both in one call.
    let readEqual = readText equalTextMask $ expressionText equalExpression
        readUnequal = readText equalTextMask $ expressionText unequalSum
    putStrLn "5. readText"
    print readEqual
    print readUnequal
    unless (readEqual == Right [equalExpression]) $ fail "wrong term from readText"
    unless (readUnequal == Left (TextError 2 TokenRejected [Character 'a'])) $ fail "wrong error from readText"

    -- 6. The expression as a sequence of entries of a vocabulary. Some entries have more than one character.
    let entries = ["(a", "(", "a", ")", "+", "+(", "*", "b", "<end>"]
        tokens entry = if entry == "<end>" then [EndOfText] else map Character entry
        entryMask = vocabularyMask (vocabulary [(entry, tokens entry) | entry <- entries]) equalTextMask
        written = ["(a", ")", "+(", "a", ")", "*", "b", "<end>"]
    putStrLn $ "6. entries at the empty prefix: " <> show (map fst $ maskNext entryMask)
    case foldM maskStep entryMask written of
        Left refusal -> fail $ "the vocabulary refuses an entry: " <> show refusal
        Right mask -> unless (maskTerms mask == [equalExpression]) $ fail "wrong term from the vocabulary"
