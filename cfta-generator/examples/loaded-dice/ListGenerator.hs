-- | The finite natural-list example from Loaded Dice, expressed with CFTA.
module ListGenerator (
    Choice (..),
    Parameters,
    maximumLength,
    alphabetSize,
    requestedWeights,
    initial,
    targetMasses,
    listEvent,
    lengthMasses,
    rationalWeights,
    fit,
    decode,
) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Sized.Prefix (Completions, completionWeightBy, prefixCompletions)
import Data.CFTA.Sized.Prefix.Train (Dual (..))
import Data.CFTA.Term (Term (..))

-- | Constructors retain the remaining fuel of the original generator.
data Choice = Stop Int | Continue Int | Element Int
    deriving (Eq, Ord, Read, Show)

-- | One stopping logit per remaining fuel value.
type Parameters = Map.Map Int Double

-- | The reference generator stops after at most five elements.
maximumLength :: Int
maximumLength = 5

-- | Elements are uniform integers from zero through nine.
alphabetSize :: Int
alphabetSize = 10

-- | Positive relative weights for the requested length classes.
requestedWeights :: Map.Map Int Integer
requestedWeights = Map.fromList [(0, 3), (2, 2), (5, 5)]

-- | Every original stopping probability starts at one half.
initial :: Parameters
initial = Map.fromList [(remaining, 0) | remaining <- [1 .. maximumLength]]

-- | Reject an empty target or a nonpositive weight before normalization.
targetMasses :: Map.Map Int Integer -> Either String (Map.Map Int Rational)
targetMasses weights = do
    unless (not (Map.null weights) && all (> 0) weights) $
        Left "Specify at least one length class, with positive integer weights."
    pure $ Map.map (\weight -> fromInteger weight / fromInteger (sum weights)) weights

-- | Compile all lists, or the event that a list has the requested length.
listEvent :: Maybe Int -> Either String (Completions Choice)
listEvent wanted = do
    unless (maximumLength >= 0 && alphabetSize > 0) $ Left "Use nonnegative fuel and a nonempty alphabet."
    unless (maybe True (\size -> size >= 0 && size <= maximumLength) wanted) $
        Left "The requested length class is outside the generator's support."
    automaton <- either (Left . show) Right $ FTA.mkFTA maximumLength rows
    either (Left . show) Right $ prefixCompletions (fromIntegral $ 2 * maximumLength + 1) automaton
  where
    lowest = maybe 0 (maximumLength -) wanted
    node symbol children = FTA.Transition symbol children noConstraint
    rows =
        (-1, [node (Element value) [] | value <- [0 .. alphabetSize - 1]])
            : [ ( remaining
                , [node (Stop remaining) [] | maybe True (== maximumLength - remaining) wanted]
                    ++ [node (Continue remaining) [-1, remaining - 1] | remaining > lowest]
                )
              | remaining <- [lowest .. maximumLength]
              ]

-- | Compile each length event once and share its count table across fit steps.
events :: Either String (Map.Map Int (Completions Choice))
events = traverse (listEvent . Just) $ Map.fromList [(size, size) | size <- [0 .. maximumLength]]

-- | Sum each length event with the supplied symbol weights.
lengthMasses :: (Num number) => (Choice -> number) -> Either String (Map.Map Int number)
lengthMasses weight = Map.map (completionWeightBy weight) <$> events

-- | Evaluate the sigmoid without overflowing an exponential.
sigmoid :: Double -> Double
sigmoid value
    | value >= 0 = 1 / (1 + exp (-value))
    | otherwise = let exponential = exp value in exponential / (1 + exponential)

-- | Reject non-finite parameters before numerical conversion or training.
finiteParameters :: Parameters -> Either String ()
finiteParameters parameters =
    unless (all (\value -> not (isNaN value || isInfinite value)) parameters) $
        Left "Generator logits and gradients must be finite."

-- | Convert each stop once; compute its complement in Rational.
rationalWeights :: Parameters -> Either String (Choice -> Rational)
rationalWeights parameters = do
    finiteParameters parameters
    let stops = Map.map (toRational . sigmoid) parameters
        stop remaining = Map.findWithDefault (1 / 2) remaining stops
    pure $ \choice -> case choice of
        Stop 0 -> 1
        Stop remaining -> stop remaining
        Continue remaining -> 1 - stop remaining
        Element _ -> 1 / fromIntegral alphabetSize

-- | Evaluate local probabilities and derivatives by the original stopping logits.
dualWeight :: Parameters -> Choice -> Dual Int Double
dualWeight parameters choice = case choice of
    Stop 0 -> 1
    Stop remaining -> stop remaining
    Continue remaining -> 1 - stop remaining
    Element _ -> Dual (1 / fromIntegral alphabetSize) Map.empty
  where
    stop remaining =
        let value = sigmoid $ Map.findWithDefault 0 remaining parameters
         in Dual value $ Map.singleton remaining (value * (1 - value))

-- | Differentiate KL(target || generated lengths) through the CFTA event masses.
loss :: Map.Map Int Rational -> Parameters -> Either String (Dual Int Double)
loss target parameters = do
    finiteParameters parameters
    actual <- lengthMasses $ dualWeight parameters
    sum <$> traverse (contribution actual) (Map.toList target)
  where
    contribution actual (size, desired) = do
        Dual value gradient <- maybe (Left "A requested length class is absent.") Right $ Map.lookup size actual
        unless (value > 0 && not (isNaN value || isInfinite value)) $
            Left "A requested length has zero or non-finite probability."
        let mass = fromRational desired
        unless (mass > 0) $ Left "A target probability is too small for Double training."
        pure $ Dual (mass * (log mass - log value)) $ Map.map ((-mass / value) *) gradient

-- | Reproduce 1,000 gradient updates at rate 0.3 and report the initial/final KL.
fit :: Either String (Parameters, Double, Double)
fit = do
    target <- targetMasses requestedWeights
    Dual before _ <- loss target initial
    fitted <- foldM (step target) initial [1 .. 1000 :: Int]
    Dual after _ <- loss target fitted
    pure (fitted, before, after)
  where
    step target parameters _ = do
        Dual _ gradient <- loss target parameters
        finiteParameters gradient
        let updated = Map.unionWith (+) parameters $ Map.map ((-0.3) *) gradient
        finiteParameters updated
        pure updated

-- | Remove the deterministic fuel labels from a generated list term.
decode :: Term Choice -> Either String [Int]
decode term = case term of
    Node (Stop _) [] -> Right []
    Node (Continue _) [Node (Element value) [], rest] -> (value :) <$> decode rest
    _ -> Left $ "The generated term is not a list: " ++ show term
