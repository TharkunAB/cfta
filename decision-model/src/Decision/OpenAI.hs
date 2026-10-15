{-# LANGUAGE OverloadedStrings #-}

{- | A decision model from a chat model on a server with an API that is
compatible with OpenAI (@POST /v1/chat/completions@), such as Ollama, vLLM or
the server of llama.cpp. The server must give the log probabilities of the
tokens. A decision model such as Nimble v3 has no chat API; use
"Decision.Ollama" for it.

The prompt shows the options with the labels A to T, and the model answers
with one token. The score of an option is the probability of its label as
that token, divided by the sum of the probabilities of all the labels. The
reply gives the 20 likeliest tokens. A label that is not one of them gets the
score 0, and the probability of tokens that are not labels is not used. Thus
a question has at most 20 options in a request. The model of 'openAI' asks a
longer question in parts of 19 options and the option "none" (see
'Decision.chunked'). A chat model often gives almost all of the probability
to one label, so its scores separate the options less than the scores of a
decision model.

At the temperature 0, the scores of a request change a little with the
requests before it, because the server keeps parts of earlier prompts. On
Ollama, the first request of a prompt gets other scores than the next
requests of the same prompt.
-}
module Decision.OpenAI (
    -- * Settings
    OpenAI (..),
    defaultOpenAI,

    -- * Models
    openAI,

    -- * Requests and replies
    requestBody,
    replyScores,
) where

import Data.Aeson (eitherDecode, object, pairs, withObject, (.:), (.=))
import Data.Aeson.Encoding (encodingToLazyByteString)
import Data.Aeson.Types (Parser, Value, parseEither)
import qualified Data.ByteString.Lazy as LazyByteString
import Data.Text (Text)
import qualified Data.Text as Text
import Network.HTTP.Client (defaultManagerSettings, newManager)

import Decision (DecisionModel (..), Option (..), Question (..), chunked)
import Decision.Http (post)

-- | The server and the model, and how the model answers.
data OpenAI = OpenAI
    { openAIUrl :: String
    -- ^ The base URL of the API, with its path, such as @http://localhost:11434/v1@.
    , openAIModel :: Text
    , openAITemperature :: Double
    , openAISeed :: Maybe Int
    , openAIReasoningEffort :: Maybe Text
    {- ^ The value @none@ stops the reasoning of a model that reasons before
    it answers. Then the first token is the answer. Use 'Nothing' for a
    server that does not accept the field.
    -}
    , openAITimeout :: Int
    -- ^ The time limit of a request in seconds. The first request loads the model.
    }
    deriving (Eq, Show)

{- | The chat model with this name on the API of a local Ollama that is
compatible with OpenAI, at the temperature 0, without a seed and without
reasoning. A request has a time limit of 10 minutes.
-}
defaultOpenAI :: Text -> OpenAI
defaultOpenAI name =
    OpenAI
        { openAIUrl = "http://localhost:11434/v1"
        , openAIModel = name
        , openAITemperature = 0
        , openAISeed = Nothing
        , openAIReasoningEffort = Just "none"
        , openAITimeout = 600
        }

{- | The model on the server. It asks a question with more than 20 options in
parts (see 'Decision.chunked'). A question without options gets no scores and
no request.
-}
openAI :: OpenAI -> IO DecisionModel
openAI settings = do
    manager <- newManager defaultManagerSettings
    pure $ chunked (length labels) $ DecisionModel $ \question -> case questionOptions question of
        [] -> pure (Right [])
        _ ->
            (>>= replyScores question)
                <$> post manager (openAITimeout settings) (openAIUrl settings <> "/chat/completions") (requestBody settings question)

-- | The labels of the options, one token each.
labels :: [Text]
labels = map Text.singleton ['A' .. 'T']

{- | The JSON body of the request for a question with at most 20 options. The
prompt has the state, the question, and one line for each option, with its
label, its name and its description. The prompt does not show the name of the
question.
-}
requestBody :: OpenAI -> Question -> LazyByteString.ByteString
requestBody settings question =
    encodingToLazyByteString . pairs $
        "model" .= openAIModel settings
            <> "messages" .= [message "system" "Answer with the label of one option and nothing else.", message "user" prompt]
            <> "max_tokens" .= (1 :: Int)
            <> "temperature" .= openAITemperature settings
            <> maybe mempty ("seed" .=) (openAISeed settings)
            <> "logprobs" .= True
            <> "top_logprobs" .= length labels
            <> maybe mempty ("reasoning_effort" .=) (openAIReasoningEffort settings)
  where
    message :: Text -> Text -> Value
    message role content = object ["role" .= role, "content" .= content]
    prompt =
        Text.intercalate "\n" $
            [questionState question, "", questionText question, ""]
                ++ zipWith (\label o -> label <> ". " <> optionName o <> ": " <> optionDescription o) labels (questionOptions question)

{- | The scores in a reply, in the order of the options of the question, from
the log probabilities of the first token. A reply that is not JSON of the
expected form is a failure, and so is a reply in which no label is one of the
likeliest tokens.
-}
replyScores :: Question -> LazyByteString.ByteString -> Either String [Double]
replyScores question body = do
    tokens <- either (Left . ("bad reply: " <>)) Right (eitherDecode body >>= parseEither firstTokens)
    let probability label = sum [exp logprob | (token, logprob) <- tokens, Text.strip token == label]
        probabilities = map probability (take (length (questionOptions question)) labels)
        total = sum probabilities
    if total > 0
        then Right (map (/ total) probabilities)
        else Left ("no label is one of the likeliest tokens: " <> show (map fst tokens))
  where
    firstTokens :: Value -> Parser [(Text, Double)]
    firstTokens = withObject "reply" $ \o -> do
        choices <- o .: "choices"
        choice <- case choices of
            choice : _ -> pure choice
            [] -> fail "no choices"
        content <- choice .: "logprobs" >>= (.: "content")
        first <- case content of
            first : _ -> pure first
            [] -> fail "no tokens"
        first .: "top_logprobs" >>= traverse (withObject "token" (\t -> (,) <$> t .: "token" <*> t .: "logprob"))
