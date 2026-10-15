{-# LANGUAGE OverloadedStrings #-}

{- | A decision model on Ollama's decision API (@POST /v1/systemone@), such as
Nimble v3. The API takes a model with the capability "decision". A chat model
does not have it.

One request asks one question with the type "choice": the names of the
options are the criteria, and their descriptions explain them. The reply
gives a probability for each option. The order of the options in the request
is their order in the question, and the scores depend on it (see
'Decision.bothOrders').

The API takes at most 255 options in a question and 64 KiB in a request. The
model of 'ollama' asks a longer question in parts (see 'Decision.chunked'). A
request that is too large fails with the status 413. For long descriptions,
put the model in 'Decision.chunked' with fewer options.

The probabilities of a question in a request with more questions are not the
same as the probabilities of the question alone. Thus each request has one
question.

At the temperature 0, the scores of a request depend on the requests that the
server answered after it loaded the model, because the server keeps parts of
earlier prompts. The same requests after a load get the same scores. Thus a
run in 'withOllama' that starts when the model is not loaded gets the same
scores in each run, if no other program uses the model at the same time. With
the 'ollamaKeepAlive' @0@, each request loads the model again, and the scores
do not depend on earlier requests. Then a request takes about 5 seconds more
for Nimble v3.
-}
module Decision.Ollama (
    -- * Settings
    Ollama (..),
    defaultOllama,

    -- * Models
    ollama,
    unload,
    withOllama,

    -- * Requests and replies
    requestBody,
    replyScores,
) where

import Control.Exception (finally)
import Control.Monad (void)
import Data.Aeson (eitherDecode, pairs, withObject, (.:), (.=))
import Data.Aeson.Encoding (encodingToLazyByteString, pair)
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Aeson.Types (parseEither)
import qualified Data.ByteString.Lazy as LazyByteString
import Data.List (sort)
import Data.Text (Text)
import qualified Data.Text as Text
import Network.HTTP.Client (defaultManagerSettings, newManager)

import Decision (DecisionModel (..), Option (..), Question (..), chunked)
import Decision.Http (post)

-- | The server and the model, and how the model answers.
data Ollama = Ollama
    { ollamaUrl :: String
    -- ^ The server, without a path, such as @http://localhost:11434@.
    , ollamaModel :: Text
    , ollamaTemperature :: Double
    , ollamaSeed :: Maybe Int
    , ollamaKeepAlive :: Text
    {- ^ How long the server keeps the model loaded after a request, such as
    @5m@. The value @0@ unloads the model after each request. Then the scores
    do not depend on earlier requests, but each request loads the model.
    -}
    , ollamaTimeout :: Int
    -- ^ The time limit of a request in seconds. The first request loads the model.
    }
    deriving (Eq, Show)

{- | Nimble v3 (@nimble-v3:9b-q4_K_M@) on a local Ollama, at the temperature 0,
without a seed. The server keeps the model loaded for 5 minutes after a
request, and a request has a time limit of 10 minutes.
-}
defaultOllama :: Ollama
defaultOllama =
    Ollama
        { ollamaUrl = "http://localhost:11434"
        , ollamaModel = "nimble-v3:9b-q4_K_M"
        , ollamaTemperature = 0
        , ollamaSeed = Nothing
        , ollamaKeepAlive = "5m"
        , ollamaTimeout = 600
        }

{- | The model on the server. It asks a question with more than 255 options in
parts (see 'Decision.chunked'). A question without options gets no scores and
no request. Two options with the same name in one request are a failure.
-}
ollama :: Ollama -> IO DecisionModel
ollama settings = do
    manager <- newManager defaultManagerSettings
    pure $ chunked 255 $ DecisionModel $ \question -> case questionOptions question of
        [] -> pure (Right [])
        options
            | Just name <- duplicate (map optionName options) ->
                pure (Left ("two options have the name " <> show name))
            | otherwise ->
                (>>= replyScores question)
                    <$> post manager (ollamaTimeout settings) (ollamaUrl settings <> "/v1/systemone") (requestBody settings question)
  where
    duplicate names = case [a | (a, b) <- zip sorted (drop 1 sorted), a == b] of
        name : _ -> Just name
        [] -> Nothing
      where
        sorted = sort names

-- | Ask the server to unload the model now.
unload :: Ollama -> IO (Either String ())
unload settings = do
    manager <- newManager defaultManagerSettings
    let body = encodingToLazyByteString (pairs ("model" .= ollamaModel settings <> "keep_alive" .= (0 :: Int)))
    void <$> post manager (ollamaTimeout settings) (ollamaUrl settings <> "/api/generate") body

{- | Give the model to an action, and unload the model at the end, also when
the action fails. The server keeps the model loaded between the requests of
the action for the time of 'ollamaKeepAlive'. A failure to unload does not
change the result.
-}
withOllama :: Ollama -> (DecisionModel -> IO a) -> IO a
withOllama settings action = do
    model <- ollama settings
    action model `finally` unload settings

{- | The JSON body of the request for a question with at most 255 options. The
key of the question is its name. The criteria have the order of the options.
-}
requestBody :: Ollama -> Question -> LazyByteString.ByteString
requestBody settings question =
    encodingToLazyByteString . pairs $
        "model" .= ollamaModel settings
            <> "state" .= questionState question
            <> pair "questions" (pairs (pair (Key.fromText (questionName question)) (pairs choice)))
            <> "keep_alive" .= ollamaKeepAlive settings
            <> pair "options" (pairs ("temperature" .= ollamaTemperature settings <> maybe mempty ("seed" .=) (ollamaSeed settings)))
  where
    choice =
        "type" .= ("choice" :: Text)
            <> "instructions" .= questionText question
            <> pair "criteria" (pairs (mconcat [Key.fromText (optionName o) .= optionDescription o | o <- questionOptions question]))

{- | The scores in a reply, in the order of the options of the question. A
reply that is not JSON of the expected form is a failure, and so is a reply
without a probability for an option.
-}
replyScores :: Question -> LazyByteString.ByteString -> Either String [Double]
replyScores question body = do
    probabilities <-
        either (Left . ("bad reply: " <>)) Right $
            eitherDecode body
                >>= parseEither
                    (withObject "reply" (\o -> o .: "answers" >>= (.: Key.fromText (questionName question)) >>= (.: "probabilities")))
    traverse (score probabilities . optionName) (questionOptions question)
  where
    score probabilities name =
        maybe
            (Left ("the reply has no score for the option " <> Text.unpack name))
            Right
            (KeyMap.lookup (Key.fromText name) probabilities)
