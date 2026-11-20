{-# LANGUAGE PatternSynonyms #-}

{- | Exhaustive checks for equations in a finite, many-sorted signature.
Terms use the sort annotations of "Specftacular.Types". A signature gives
each first-order symbol one arity and one interpretation. Each carrier maps
its values to their observation classes. The result applies to these tables.
-}
module Specftacular.FiniteLaw (
    Carriers,
    Assignment,
    Operation (..),
    Theory,
    finiteTheory,
    ContextFrame (..),
    refineObservations,
    distinguishingContext,
    ScopedLaw,
    proveOn,
    applyAt,
    promote,
    derives,
) where

import Control.Monad (foldM, unless, when, zipWithM)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)

import qualified Data.CFTA.EGraph as EG
import Data.CFTA.Symbol (Symbol)

import Specftacular.EGraph (Law, equalUnder)
import Specftacular.Types (Term, pattern Term)

-- | Argument sorts, result sort, and the result for each argument tuple.
data Operation = Operation [Term] Term (Map [Integer] Integer)

-- | The finite carrier at each sort, with one class label per value.
type Carriers = Map Term (Map Integer Integer)

-- | The values of the free variables in an equation.
type Assignment = Map Symbol Integer

-- | An immutable signature and the equations admitted for it.
data Theory = Theory Carriers (Map Symbol Operation) [Law]

-- | Check the domain and range of every operation, including constants.
finiteTheory :: Carriers -> Map Symbol Operation -> Either String Theory
finiteTheory carriers operations = do
    mapM_ check (Map.toList operations)
    pure (Theory carriers operations [])
  where
    check (name, Operation inputs output table) = do
        domains <- traverse (carrier carriers) inputs
        range <- carrier carriers output
        unless (Map.keys table == traverse Map.keys domains) $
            Left ("Incomplete or ill-sorted operation table for " ++ show name)
        unless (all (`Map.member` range) table) $
            Left ("Result outside the carrier of " ++ show name)

-- | Find a declared finite carrier.
carrier :: Carriers -> Term -> Either String (Map Integer Integer)
carrier carriers sort = maybe (Left ("Unknown sort " ++ show sort)) Right (Map.lookup sort carriers)

-- | An operation around the hole, with the argument values before and after it.
data ContextFrame = ContextFrame !Symbol ![Integer] ![Integer]
    deriving (Eq, Ord, Show)

{- | Give each sort the coarsest congruence contained in its observation classes.
See Note [Contextual observation classes].
-}
refineObservations :: Theory -> Theory
refineObservations (Theory carriers ops laws) =
    Theory (NonEmpty.last $ observationRounds (contextsOf ops) carriers) ops laws

{- | Explain why two values lie in separate refined observation classes.

Pass the theory with the original observations. Frames run from the hole
outward. An empty context distinguishes values that already have different
observations. A nonempty result uses the fewest enclosing operations.
-}
distinguishingContext :: Theory -> Term -> Integer -> Integer -> Either String (Maybe [ContextFrame])
distinguishingContext (Theory carriers ops _) sort first second = do
    values <- carrier carriers sort
    unless (Map.member first values && Map.member second values) (Left "Value outside the observation carrier")
    pure $ explain (reverse $ NonEmpty.toList $ observationRounds contexts carriers) sort first second
  where
    contexts = contextsOf ops
    explain [] _ _ _ = Nothing
    explain (current : earlier) input a b
        | sameClass current input a b = Nothing
        | null earlier = Just []
        | Just shorter <- explain earlier input a b = Just shorter
        | otherwise =
            listToMaybe
                [ frame : rest
                | ((frame, output), table) <- contextsAt contexts input
                , Just rest <- [explain earlier output (table Map.! a) (table Map.! b)]
                ]

-- | Unary operations obtained by fixing every argument other than the hole.
type Contexts = Map Term (Map (ContextFrame, Term) (Map Integer Integer))

-- | Collect the unary operations directly from the validated operation tables.
contextsOf :: Map Symbol Operation -> Contexts
contextsOf ops =
    Map.fromListWith
        (Map.unionWith Map.union)
        [ (input, Map.singleton (ContextFrame name before after, output) (Map.singleton hole result))
        | (name, Operation inputs output table) <- Map.toList ops
        , (index, input) <- zip [0 ..] inputs
        , (arguments, result) <- Map.toList table
        , (before, hole : after) <- [splitAt index arguments]
        ]

-- | Read the typed contexts with the given input sort.
contextsAt :: Contexts -> Term -> [((ContextFrame, Term), Map Integer Integer)]
contextsAt contexts sort = Map.toList $ Map.findWithDefault Map.empty sort contexts

{- Note [Contextual observation classes]
---------------------------------------
Round zero records the supplied classes. Each new round compares the old
classes and the old classes of every one-hole application. By induction,
round n distinguishes exactly the pairs that some context of depth at most
n can distinguish. At a fixed point the classes agree under every context.
Replacing one argument at a time then gives congruence for whole operations.

Every strict round splits a finite block. Canonical labels let us compare
partitions directly. Already-promoted laws used a congruent original
partition, so refining it preserves their proofs of observational equality.
-}

-- | Partitions after observing contexts of increasing depth.
observationRounds :: Contexts -> Carriers -> NonEmpty.NonEmpty Carriers
observationRounds contexts carriers = initial NonEmpty.:| refine initial
  where
    initial = Map.map canonicalClasses carriers
    refine current
        | next == current = []
        | otherwise = next : refine next
      where
        next = Map.mapWithKey (\sort -> canonicalClasses . Map.mapWithKey (observe sort)) current
        observe sort value old =
            ( old
            , [ current Map.! output Map.! (table Map.! value)
              | ((_, output), table) <- contextsAt contexts sort
              ]
            )

-- | Use the lowest member of each class as its stable label.
canonicalClasses :: (Ord label) => Map Integer label -> Map Integer Integer
canonicalClasses labels = Map.map (representatives Map.!) labels
  where
    representatives = Map.fromListWith min [(label, value) | (value, label) <- Map.toList labels]

-- | Compare two values in a given observation partition.
sameClass :: Carriers -> Term -> Integer -> Integer -> Bool
sameClass carriers sort a b = values Map.! a == values Map.! b
  where
    values = carriers Map.! sort

{- Note [Promoting an observational equation]
--------------------------------------------
An equation can hold on the selected assignments even when a context
distinguishes its sides. Keep the checked right-hand values with the scope.
To use the equation in a context, check all assignments and each operation
of the signature. Equal input classes must give the same output class.
Induction over a first-order context then gives contextual equality.

Keep the rules inside the checked theory. Adding an observer such as snd
can invalidate a class defined by fst. Ground queries check the same
signature before they use its rules.
-}

-- | An equation checked on a nonempty set of assignments.
data ScopedLaw = ScopedLaw Theory (Map Assignment Integer) Bool (EG.Pattern Symbol Symbol) (EG.Pattern Symbol Symbol)

{- | Check both sides on every assignment admitted by the guard.
An unknown guard result or an empty scope makes the check fail.
-}
proveOn ::
    Theory ->
    Map Symbol Term ->
    (Assignment -> Maybe Bool) ->
    Term ->
    Term ->
    Either String ScopedLaw
proveOn theory@(Theory carriers ops _) variables guard left right = do
    when (any (`Map.member` ops) (Map.keys variables)) $
        Left "A variable shadows an operation"
    domains <- traverse (fmap Map.keys . carrier carriers) variables
    Checked sort patternL evalL <- checkTerm ops variables left
    Checked sortR patternR evalR <- checkTerm ops variables right
    unless (sort == sortR) (Left "The sides have different sorts")
    classes <- carrier carriers sort
    let check (rows, full) assignment = case guard assignment of
            Nothing -> Left ("Unknown guard at " ++ show assignment)
            Just False -> Right (rows, False)
            Just True -> do
                l <- evalL assignment
                r <- evalR assignment
                case (Map.lookup l classes, Map.lookup r classes) of
                    (Just a, Just b) | a == b -> pure (Map.insert assignment r rows, full)
                    _ -> Left ("Different or unknown observations at " ++ show assignment)
    (rows, full) <- foldM check (Map.empty, True) (sequenceA domains)
    when (Map.null rows) (Left "The guard admits no assignments")
    pure (ScopedLaw theory rows full patternL patternR)

{- | Return the right-hand value for the root observation at a checked
assignment. A parent operation can distinguish the two values.
-}
applyAt :: ScopedLaw -> Assignment -> Maybe Integer
applyAt (ScopedLaw _ rows _ _ _) assignment = Map.lookup assignment rows

{- | Install a fully covered equation after checking congruence of the signature.
See Note [Promoting an observational equation].
-}
promote :: ScopedLaw -> Either String Theory
promote (ScopedLaw (Theory carriers ops prior) _ full left right) = do
    unless full (Left "The equation covers only part of its domain")
    mapM_ congruent (Map.toList ops)
    let rules = EG.equation left right
    when (null rules) (Left "Neither side binds the variables of the other side")
    pure (Theory carriers ops (rules : prior))
  where
    congruent (name, Operation inputs output table) = do
        domains <- traverse (carrier carriers) inputs
        range <- carrier carriers output
        let check seen (arguments, value) = do
                key <- zipWithM Map.lookup arguments domains
                result <- Map.lookup value range
                case Map.lookup key seen of
                    Just old | old /= result -> Nothing
                    _ -> Just (Map.insert key result seen)
        case foldM check Map.empty (Map.toList table) of
            Nothing -> Left ("Operation distinguishes equal observation classes: " ++ show name)
            Just _ -> Right ()

{- | Ask whether the admitted rules derive an equation on ground terms
within the saturation limits.
-}
derives :: EG.Limits -> Theory -> Term -> Term -> Either String Bool
derives limits (Theory _ ops laws) left right = do
    Checked sortL _ _ <- checkTerm ops Map.empty left
    Checked sortR _ _ <- checkTerm ops Map.empty right
    unless (sortL == sortR) (Left "The sides have different sorts")
    pure (fst (equalUnder limits laws left right))

-- | A well-sorted pattern and its evaluator in the declared signature.
data Checked = Checked Term (EG.Pattern Symbol Symbol) (Assignment -> Either String Integer)

-- | Check sort annotations and arities before constructing a rule or a query.
checkTerm :: Map Symbol Operation -> Map Symbol Term -> Term -> Either String Checked
checkTerm ops variables (Term name (sort : children)) = do
    let sorted = EG.PSorted (literalSort sort)
    case Map.lookupIndex name variables of
        Just i -> do
            unless (null children && Map.lookup name variables == Just sort) $
                Left ("Ill-sorted variable " ++ show name)
            pure (Checked sort (sorted (EG.PVar (show i))) (require name))
        Nothing -> do
            Operation inputs output table <- require name ops
            args <- traverse (checkTerm ops variables) children
            unless (map (\(Checked s _ _) -> s) args == inputs && output == sort) $
                Left ("Ill-sorted application of " ++ show name)
            let pattern' = sorted (EG.PNode name [p | Checked _ p _ <- args])
                eval assignment = do
                    values <- traverse (\(Checked _ _ f) -> f assignment) args
                    require values table
            pure (Checked sort pattern' eval)
  where
    literalSort (Term s ts) = EG.SNode s (map literalSort ts)
    require key values = maybe (Left ("No interpretation for " ++ show key)) Right (Map.lookup key values)
checkTerm _ _ (Term name []) = Left ("Missing sort annotation on " ++ show name)
