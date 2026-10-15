{-# LANGUAGE OverloadedStrings #-}

-- | The one HTTP request of the clients: a POST of a JSON body.
module Decision.Http (
    post,
) where

import Control.Exception (try)
import qualified Data.ByteString.Lazy as LazyByteString
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8Lenient)
import Network.HTTP.Client
import Network.HTTP.Types (statusCode, statusIsSuccessful)

{- | Send a JSON body to a URL in a POST request, with a time limit in seconds,
and give the body of the reply. The result is a failure when the server does
not reply, or when its status is not a success.
-}
post :: Manager -> Int -> String -> LazyByteString.ByteString -> IO (Either String LazyByteString.ByteString)
post manager seconds url body = do
    result <- try $ do
        request <- parseRequest ("POST " <> url)
        httpLbs
            request
                { requestBody = RequestBodyLBS body
                , requestHeaders = [("Content-Type", "application/json")]
                , responseTimeout = responseTimeoutMicro (seconds * 1000000)
                }
            manager
    pure $ case result of
        Left (HttpExceptionRequest _ problem) -> Left ("no reply from " <> url <> ": " <> show problem)
        Left (InvalidUrlException _ problem) -> Left ("bad URL " <> url <> ": " <> problem)
        Right response
            | statusIsSuccessful (responseStatus response) -> Right (responseBody response)
            | otherwise ->
                Left $
                    "status "
                        <> show (statusCode (responseStatus response))
                        <> " from "
                        <> url
                        <> ": "
                        <> Text.unpack (decodeUtf8Lenient (LazyByteString.toStrict (responseBody response)))
