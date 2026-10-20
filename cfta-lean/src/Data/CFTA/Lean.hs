{-# LANGUAGE OverloadedStrings #-}

{- | An LTA entailment solver backed by the Kimina Lean server.

Each query checks two closed propositions: the implication and its negation.
A checked proof gives 'Yes' or 'No'. A failed proof is 'Unknown'.
The client does not start Lean or change the server configuration.
-}
module Data.CFTA.Lean (
    Options (..),
    defaultOptions,
    withKimina,
    fallback,
    entailmentProposition,
) where

import Control.Exception (catch)
import Control.Monad (unless)
import Data.Aeson (Value (..), eitherDecode, encode, object, withObject, (.!=), (.:), (.:?), (.=))
import Data.Aeson.Types (Parser, parseEither)
import Data.Either (fromRight)
import Data.Text (Text)
import qualified Data.Text as Text
import Network.HTTP.Client (
    HttpException,
    Request (..),
    RequestBody (RequestBodyLBS),
    defaultManagerSettings,
    httpLbs,
    newManager,
    parseRequest,
    responseBody,
    responseStatus,
    responseTimeoutMicro,
 )
import Network.HTTP.Types (statusIsSuccessful)

import Data.CFTA.Formula (Formula, Name, Sort (..))
import Data.CFTA.Lean.Formula (entailmentProposition)
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached)
import Data.CFTA.Refinement.Verdict (
    Entailment,
    Verdict (..),
    entailmentWithBindings,
    entailsWithBindings,
 )

-- | The Kimina endpoint and the time allowed for each proof.
data Options = Options
    { optionUrl :: String
    -- ^ The HTTP server URL, without @/api/check@.
    , optionTimeoutSeconds :: Int
    -- ^ The Kimina proof timeout. The HTTP timeout also allows queueing and imports.
    }
    deriving (Eq, Show)

-- | The local Kimina server, with ten seconds for each proof.
defaultOptions :: Options
defaultOptions = Options "http://127.0.0.1:8000" 10

{- | Use Kimina under fixed declarations and ambient assumptions.

Undeclared values have sort 'IntSort'. Fresh bindings copy the declared sort;
they do not assert equality. 'entailmentProposition' describes the supported
formula subset. Unsupported formulas do not make an HTTP request.

The server must provide Mathlib. Transport errors, malformed replies, failed
proofs, unfinished proofs, and timeouts give 'Unknown'. Configuration errors
raise an exception. Cancellation is not caught.
-}
withKimina :: Options -> [(Name, Sort)] -> [Formula] -> (Entailment -> IO a) -> IO a
withKimina options declarations assumptions action = do
    let seconds = optionTimeoutSeconds options
    unless (seconds > 0 && seconds <= 3600) $
        fail "cfta-lean: optionTimeoutSeconds must be between 1 and 3600"
    request <- parseRequest (reverse (dropWhile (== '/') (reverse (optionUrl options))) <> "/api/check")
    manager <- newManager defaultManagerSettings
    let query bindings antecedent consequent =
            case entailmentProposition declarations assumptions bindings antecedent consequent of
                Left _ -> pure Unknown
                Right proposition -> do
                    let snippets =
                            [ object ["id" .= ("yes" :: Text), "code" .= proof proposition]
                            , object ["id" .= ("no" :: Text), "code" .= proof ("¬ (" <> proposition <> ")")]
                            ]
                        body = object ["snippets" .= snippets, "timeout" .= seconds, "reuse" .= True]
                        check = do
                            response <-
                                httpLbs
                                    request
                                        { method = "POST"
                                        , requestHeaders = [("Content-Type", "application/json")]
                                        , requestBody = RequestBodyLBS (encode body)
                                        , -- A batch can queue and import before both checks finish.
                                          responseTimeout = responseTimeoutMicro ((60 + 4 * seconds) * 1000000)
                                        }
                                    manager
                            pure $
                                if statusIsSuccessful (responseStatus response)
                                    then
                                        fromRight Unknown $
                                            eitherDecode (responseBody response) >>= parseEither verdict
                                    else Unknown
                    check `catch` transportFailure
    action (entailmentWithBindings query)

{- | Use the second solver only when the first returns 'Unknown' or reaches
the Z3 time limit. Pass the same fresh bindings to both solvers.
-}
fallback :: Entailment -> Entailment -> Entailment
fallback first second = entailmentWithBindings $ \bindings antecedent consequent -> do
    answer <-
        entailsWithBindings first bindings antecedent consequent
            `catch` z3Timeout
    case answer of
        Unknown -> entailsWithBindings second bindings antecedent consequent
        _ -> pure answer

-- | A transport failure does not decide an entailment.
transportFailure :: HttpException -> IO Verdict
transportFailure _ = pure Unknown

-- | A Z3 timeout permits the fallback solver to try the query.
z3Timeout :: TimeLimitReached -> IO Verdict
z3Timeout _ = pure Unknown

-- | Check a closed proposition with a bounded, fixed tactic portfolio.
proof :: Text -> Text
proof proposition =
    Text.unlines
        [ "import Mathlib"
        , "set_option maxHeartbeats 400000"
        , "example : " <> proposition <> " := by"
        , "  solve"
        , "  | omega"
        , "  | norm_num"
        , "  | decide"
        , "  | intros; nlinarith"
        , "  | grind"
        , "  | push_neg; solve"
        , "    | (repeat' first | refine Exists.intro (0 : Int) ?_); norm_num"
        , "    | (repeat' first | refine Exists.intro (1 : Int) ?_); norm_num"
        , "    | (repeat' first | refine Exists.intro (-1 : Int) ?_); norm_num"
        ]

-- | Require exactly the two requested results. Contradictory proofs fail closed.
verdict :: Value -> Parser Verdict
verdict = withObject "Kimina check response" $ \response -> do
    results <- response .: "results" >>= traverse result
    case (lookup "yes" results, lookup "no" results, length results) of
        (Just True, Just False, 2) -> pure Yes
        (Just False, Just True, 2) -> pure No
        _ -> pure Unknown

-- | Accept only a completed Lean response with no errors or unfinished proofs.
result :: Value -> Parser (Text, Bool)
result = withObject "Kimina result" $ \entry -> do
    identifier <- entry .: "id"
    serverError <- entry .:? "error" :: Parser (Maybe Text)
    reply <- entry .:? "response"
    valid <- case (serverError, reply) of
        (Nothing, Just response) -> checked response
        (Just _, Nothing) -> pure False
        _ -> fail "Kimina result must contain exactly one error or response"
    pure (identifier, valid)
  where
    checked = withObject "Lean response" $ \response -> do
        replError <- response .:? "message" :: Parser (Maybe Text)
        environment <- response .:? "env" :: Parser (Maybe Integer)
        messages <- response .:? "messages" .!= [] >>= traverse message
        sorries <- response .:? "sorries" .!= [] :: Parser [Value]
        case (replError, environment) of
            (Just _, Nothing) -> pure False
            (Nothing, Just env) | env >= 0 -> pure (and messages && null sorries)
            _ -> fail "Lean response has no valid environment or REPL error"
    message = withObject "Lean message" $ \entry -> do
        severity <- entry .: "severity" :: Parser Text
        contents <- entry .: "data" :: Parser Text
        unless (severity `elem` ["info", "trace", "warning", "error"]) $
            fail "Unknown Lean message severity"
        pure (severity /= "error" && not ("declaration uses 'sorry'" `Text.isInfixOf` contents))
