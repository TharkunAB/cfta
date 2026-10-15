{-# LANGUAGE OverloadedStrings #-}

{- | The tests of the package. The test with a server runs only on request:
DECISION_MODEL_LIVE=1 asks Nimble v3 on the local Ollama. The test unloads the
model at the end.
-}
module Main (main) where

import Control.Monad (forM_, when)
import Data.Aeson (Value (..), decode)
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.ByteString.Char8 as ByteString
import qualified Data.ByteString.Lazy as LazyByteString
import Data.IORef (modifyIORef, newIORef, readIORef)
import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe (isNothing)
import qualified Data.Text as Text
import System.Environment (lookupEnv)
import Test.Hspec

import Decision
import qualified Decision.Ollama as Ollama

main :: IO ()
main = do
    live <- lookupEnv "DECISION_MODEL_LIVE"
    hspec $ do
        combinators
        ollama
        when (live == Just "1") liveOllama

-- | A question with options f0, f1, and so on, with descriptions.
question :: Int -> Question
question n =
    Question
        { questionState = "A Haskell programmer wants a function of type [Int] -> Int."
        , questionText = "Which function most likely has this type?"
        , questionOptions =
            [Option ("f" <> Text.pack (show i)) ("f" <> Text.pack (show i) <> " :: [Int] -> Int") | i <- [0 .. n - 1]]
        }

-- | A model that gives the score n - i to the option at the position i, and records the questions.
byPosition :: IO (DecisionModel, IO [Question])
byPosition = do
    asked <- newIORef []
    let model = DecisionModel $ \q -> do
            modifyIORef asked (q :)
            let n = length (questionOptions q)
            pure (Right [fromIntegral (n - i) | i <- [0 .. n - 1]])
    pure (model, reverse <$> readIORef asked)

-- | The value at a path of keys in a JSON value.
at :: [Key.Key] -> Value -> Maybe Value
at [] value = Just value
at (key : rest) (Object o) = KeyMap.lookup key o >>= at rest
at _ _ = Nothing

-- | The number of fields of a JSON object.
size :: Value -> Maybe Int
size (Object o) = Just (KeyMap.size o)
size _ = Nothing

-- | True when each string occurs in the body after the string before it.
inOrder :: [ByteString.ByteString] -> LazyByteString.ByteString -> Bool
inOrder needles body = go needles (LazyByteString.toStrict body)
  where
    go [] _ = True
    go (needle : rest) haystack = case ByteString.breakSubstring needle haystack of
        (_, found) | ByteString.null found -> False
        (_, found) -> go rest (ByteString.drop (ByteString.length needle) found)

-- | The names of the options of a question.
names :: Question -> [String]
names = map (Text.unpack . optionName) . questionOptions

combinators :: Spec
combinators = do
    describe "chunks" $ do
        it "keeps a question with at most n options" $
            chunks 255 (question 255) `shouldBe` [question 255]
        it "splits a longer question into parts of equal size, each with the option none" $ do
            let parts = chunks 255 (question 300)
            map (length . questionOptions) parts `shouldBe` [151, 151]
            map (last . names) parts `shouldBe` ["none", "none"]
            concatMap (init . names) parts `shouldBe` names (question 300)
        it "makes the fewest parts" $
            map (length . questionOptions) (chunks 20 (question 39)) `shouldBe` [14, 14, 14]

    describe "chunked" $ do
        it "gives the scores of the options without the scores of none" $ do
            (model, asked) <- byPosition
            scores <- scoreOptions (chunked 20 model) (question 25)
            scores `shouldBe` Right ([14, 13 .. 2] ++ [13, 12 .. 2])
            map (length . questionOptions) <$> asked `shouldReturn` [14, 13]
        it "gives the scores of fixedModel for each option" $ do
            let score option = fromIntegral (Text.length (optionName option))
            scoreOptions (chunked 20 (fixedModel score)) (question 100)
                `shouldReturn` Right (map score (questionOptions (question 100)))

    describe "bothOrders" $ do
        it "removes a bias of the position" $ do
            (model, _) <- byPosition
            scoreOptions (bothOrders model) (question 4) `shouldReturn` Right [2.5, 2.5, 2.5, 2.5]
        it "keeps the scores of fixedModel" $ do
            let score option = if optionName option == "f2" then 1 else 0
            scoreOptions (bothOrders (fixedModel score)) (question 4) `shouldReturn` Right [0, 0, 1, 0]
        it "reverses each part inside chunked" $ do
            (model, asked) <- byPosition
            _ <- scoreOptions (chunked 20 (bothOrders model)) (question 25)
            let parts = map names (chunks 20 (question 25))
            map names <$> asked `shouldReturn` concat [[part, reverse part] | part <- parts]

    describe "ranked"
        $ it "puts the highest score first, and keeps the order of equal scores"
        $ ranked "abcd" [1, 3, 1, 2] `shouldBe` [('b', 3), ('d', 2), ('a', 1), ('c', 1)]

ollama :: Spec
ollama = describe "Decision.Ollama" $ do
    it "encodes a small request" $
        Ollama.requestBody Ollama.defaultOllama{Ollama.ollamaSeed = Just 7} (question 2)
            `shouldBe` "{\"model\":\"nimble-v3:9b-q4_K_M\",\"state\":\"A Haskell programmer wants a function of type [Int] -> Int.\",\"questions\":{\"q0\":{\"type\":\"choice\",\"instructions\":\"Which function most likely has this type?\",\"criteria\":{\"f0\":\"f0 :: [Int] -> Int\",\"f1\":\"f1 :: [Int] -> Int\"}}},\"keep_alive\":\"5m\",\"options\":{\"temperature\":0.0,\"seed\":7}}"
    it "encodes the requests of a question with 300 options as two questions of 150 options and none" $ do
        let parts = chunks 255 (question 300)
            bodies = map (Ollama.requestBody Ollama.defaultOllama) parts
        length bodies `shouldBe` 2
        forM_ (zip parts bodies) $ \(part, body) -> do
            let value = decode body :: Maybe Value
                criteria = at ["questions", "q0", "criteria"] =<< value
            (at ["model"] =<< value) `shouldBe` Just (String "nimble-v3:9b-q4_K_M")
            (at ["questions", "q0", "type"] =<< value) `shouldBe` Just (String "choice")
            (at ["options", "temperature"] =<< value) `shouldBe` Just (Number 0)
            isNothing (at ["options", "seed"] =<< value) `shouldBe` True
            (size =<< criteria) `shouldBe` Just 151
            inOrder [ByteString.pack ("\"" <> name <> "\":") | name <- names part] body `shouldBe` True
    it "reads the scores of a reply in the order of the options" $
        Ollama.replyScores
            (question 3)
            "{\"answers\":{\"q0\":{\"type\":\"choice\",\"choice\":\"f2\",\"probabilities\":{\"f2\":0.5,\"f0\":0.2,\"f1\":0.3}}}}"
            `shouldBe` Right [0.2, 0.3, 0.5]
    it "fails on a reply without the score of an option" $
        Ollama.replyScores (question 3) "{\"answers\":{\"q0\":{\"probabilities\":{\"f0\":0.4,\"f1\":0.6}}}}"
            `shouldBe` Left "the reply has no score for the option f2"
    it "fails on a reply that is not JSON" $
        Ollama.replyScores (question 3) "{\"answers\":" `shouldSatisfy` either ("bad reply" `isPrefixOf`) (const False)
    it "fails on two options with the same name" $ do
        model <- Ollama.ollama Ollama.defaultOllama{Ollama.ollamaUrl = "http://127.0.0.1:1"}
        scoreOptions model (question 2){questionOptions = [Option "a" "x", Option "a" "y"]}
            `shouldReturn` Left "two options have the name \"a\""
    it "fails when the server refuses the connection" $ do
        model <- Ollama.ollama Ollama.defaultOllama{Ollama.ollamaUrl = "http://127.0.0.1:1"}
        scoreOptions model (question 2) >>= (`shouldSatisfy` either ("refused" `isInfixOf`) (const False))
        Ollama.unload Ollama.defaultOllama{Ollama.ollamaUrl = "http://127.0.0.1:1"}
            >>= (`shouldSatisfy` either ("no reply from http://127.0.0.1:1/api/generate" `isPrefixOf`) (const False))
    it "gives no scores and sends no request for a question without options" $ do
        model <- Ollama.ollama Ollama.defaultOllama{Ollama.ollamaUrl = "http://127.0.0.1:1"}
        scoreOptions model (question 0) `shouldReturn` Right []

-- | The scores of a question asked two times. Each time, the scores sum to about 1.
askTwice :: DecisionModel -> Question -> IO ([Double], [Double])
askTwice model q = (,) <$> ask <*> ask
  where
    ask = do
        answer <- scoreOptions model q
        scores <- either (\problem -> expectationFailure problem >> pure []) pure answer
        length scores `shouldBe` length (questionOptions q)
        abs (sum scores - 1) `shouldSatisfy` (< 1.0e-6)
        pure scores

liveOllama :: Spec
liveOllama = describe "Nimble v3 on the local Ollama" $
    it "gives the same scores two times at the temperature 0" $
        Ollama.withOllama Ollama.defaultOllama $ \model -> do
            (first, second) <- askTwice model (question 3)
            first `shouldBe` second
