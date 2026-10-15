{-# LANGUAGE OverloadedStrings #-}

{- | Decision models: a model gives a score to each option of a question.

A program asks a question, such as "which library component is the outermost
function of the program?", with its options. A decision model gives one score
for each option. "Decision.Ollama" and "Decision.OpenAI" give models that run
on a server. 'fixedModel' gives a model without I/O, for tests.

A model on a server scores a limited number of options in one request, and
its scores depend on the order of the options. 'chunked' asks a long question
in parts, and 'bothOrders' asks each question in two orders. Put 'bothOrders'
inside 'chunked':

> chunked 250 (bothOrders model)

Then each part has the same options in the two orders.
-}
module Decision (
    -- * Questions
    Option (..),
    Question (..),
    question,

    -- * Models
    DecisionModel (..),
    fixedModel,

    -- * Combinators
    chunked,
    chunks,
    bothOrders,

    -- * Results
    ranked,
) where

import Data.List (sortOn)
import Data.Ord (Down (..))
import Data.Text (Text)

-- | One option of a question: its name, and a description for the model.
data Option = Option
    { optionName :: Text
    , optionDescription :: Text
    }
    deriving (Eq, Show)

{- | A question to a model: its name, what it is about, the question, and the
options.
-}
data Question = Question
    { questionName :: Text
    {- ^ The name of the question, such as @q0@ or @best_fit@. Ollama's decision
    API shows the name to the model, so the name changes the scores.
    -}
    , questionState :: Text
    -- ^ What the decision is about, such as the type of the program.
    , questionText :: Text
    , questionOptions :: [Option]
    }
    deriving (Eq, Show)

-- | A question with the name @q0@, from what it is about, the question, and the options.
question :: Text -> Text -> [Option] -> Question
question = Question "q0"

{- | A model gives one score for each option of a question, in the order of
the options. A higher score is likelier, and a score is not negative. A model
can fail, with a message.
-}
newtype DecisionModel = DecisionModel
    { scoreOptions :: Question -> IO (Either String [Double])
    }

-- | A model without I/O: the score of each option comes from the option.
fixedModel :: (Option -> Double) -> DecisionModel
fixedModel score = DecisionModel $ \q -> pure $ Right $ map score (questionOptions q)

{- | The questions that @'chunked' n@ asks for a question. A question with at
most @n@ options stays one question. A question with more options becomes the
fewest parts of at most @n - 1@ of its options. The sizes of the parts differ
by one at most. Each part has its options in their order, and then the option
"none" ("None of these options."). A value of @n@ less than 2 counts as 2.
-}
chunks :: Int -> Question -> [Question]
chunks limit q
    | total <= n = [q]
    | otherwise = [q{questionOptions = part ++ [none]} | part <- split sizes options]
  where
    n = max 2 limit
    options = questionOptions q
    total = length options
    parts = (total + n - 2) `div` (n - 1)
    sizes = [total `div` parts + (if k < total `mod` parts then 1 else 0) | k <- [0 .. parts - 1]]
    split [] _ = []
    split (size : rest) remaining = let (part, after) = splitAt size remaining in part : split rest after
    none = Option "none" "None of these options."

{- | A model that asks a question with more than @n@ options in 'chunks'. It
asks the parts one after the other, and stops at the first failure. It gives
the scores of the options of the question, without the scores of the options
"none". A score is relative to the other options of its part, so a
comparison of the scores of two parts is approximate.
-}
chunked :: Int -> DecisionModel -> DecisionModel
chunked n model = DecisionModel $ \q -> case chunks n q of
    [one] -> scoreOptions model one
    parts -> scoreParts parts
  where
    scoreParts [] = pure (Right [])
    scoreParts (part : rest) = do
        answer <- scoreOptions model part
        case answer of
            Left problem -> pure (Left problem)
            Right scores -> fmap (take (length (questionOptions part) - 1) scores ++) <$> scoreParts rest

{- | A model that asks each question two times: with the options in their
order, and in the reverse order. The score of an option is the mean of its two
scores. The scores of a model depend on the order of the options, and the
mean removes most of this bias.
-}
bothOrders :: DecisionModel -> DecisionModel
bothOrders model = DecisionModel $ \q -> do
    forward <- scoreOptions model q
    case forward of
        Left problem -> pure (Left problem)
        Right scores -> do
            backward <- scoreOptions model q{questionOptions = reverse (questionOptions q)}
            pure $ zipWith (\a b -> (a + b) / 2) scores . reverse <$> backward

{- | Items with their scores, the highest score first. Items with equal scores
keep their order. The items are the options of a question, or other items in
the same order, such as the laws that the options describe.
-}
ranked :: [a] -> [Double] -> [(a, Double)]
ranked items scores = sortOn (Down . snd) (zip items scores)
