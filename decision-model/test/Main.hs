{-# LANGUAGE OverloadedStrings #-}

-- | The tests of the package.
module Main (main) where

import Data.IORef (modifyIORef, newIORef, readIORef)
import qualified Data.Text as Text
import Test.Hspec

import Decision

main :: IO ()
main = hspec combinators

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
