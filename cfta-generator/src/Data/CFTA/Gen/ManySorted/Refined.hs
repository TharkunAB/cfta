{-# LANGUAGE ScopedTypeVariables #-}

{- | Refinements in a run-time signature.

A value sort can carry a condition on its integers, and a function can carry a
measure and a precondition. The measure of a function is the integer of the
terms that it builds, as a term of the measures of its arguments. The
precondition is a formula about the measures of the arguments. A value has
its own integer as its measure.

The generator is a refinement generator of "Data.CFTA.Gen.Refinement", compiled
with a solver. The values of a sort are 'Data.CFTA.Gen.Refinement.every' with the
condition, and 'Data.CFTA.Gen.Refinement.compile' counts them as integer points
and does not list them. A function is 'Data.CFTA.Gen.Refinement.measured', or
'Data.CFTA.Gen.Refinement.guarded' when it has no measure, so a term is in the
language only when the solver proves the preconditions of all its nodes.

The route is the refinement generator and not an automaton import, for two
reasons. The automaton import of "Data.CFTA.Gen" counts the accepting runs of
an automaton and has no symbolic integers. The liquid automaton import reads a
guard over the refinement of a child, which is a type and not one integer, so
a precondition on the value of a term such as @add(a, b)@ needs a state for each
refinement. The refinement generator tracks the measure of each node as a
term of the integers of its leaves, so it counts the preconditions without
listing the values.

A value sort is an 'Interval' or a 'Pool'. The entries of a pool are leaves. An
entry has a measure when 'projectInteger' of the codec gives an integer for its
symbol, and then its integer is the measure. An entry without an integer has no
measure, so a function can use it only if no measure or precondition names that
argument. A condition on a pool sort keeps the entries whose integer satisfies
it, and it drops the entries without an integer.

Limits that come from the refinement generators: a condition and a precondition
must be linear, and a recursive signature needs a bound on the nesting of the
functions. A signature has no variables here.
-}
module Data.CFTA.Gen.ManySorted.Refined (
    RefinedSignature (..),
    FunctionSemantics (..),
    RefinedError (..),
    RefinedTypeError (..),
    refinedGen,
    refinedTypeCheck,
    unary,
    binary,
) where

import Data.List (isPrefixOf)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

import Data.CFTA.Constraint (contractTermName)
import Data.CFTA.Gen.Error (GenError)
import Data.CFTA.Gen.ManySorted
import Data.CFTA.Gen.Refinement (LTAGen)
import qualified Data.CFTA.Gen.Refinement as LTAGen
import Data.CFTA.Index (Arity (..))
import Data.CFTA.Path (ChildIndex (..), Path, path)
import Data.CFTA.Refinement (Entailment (entails), Verdict (..))
import Data.CFTA.Refinement.Expression (
    Expr,
    Formula,
    Refinement,
    freeNames,
    literal,
    refinementFormula,
    true,
    variable,
    (.&&),
    (.<=),
    (.==),
 )
import Data.CFTA.Refinement.Guard (ContractBuilder (..), MeasureBuilder (..))
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | What a function means for the integers of its terms.
data FunctionSemantics = FunctionSemantics
    { semanticsMeasure :: Maybe ([Expr] -> Expr)
    -- ^ The integer of a term as a term of the integers of its arguments, one for each argument. A parent can name the measure in its own measure or precondition only if the function has one.
    , semanticsPrecondition :: Maybe ([Expr] -> Formula)
    -- ^ A formula about the integers of the arguments, one for each argument. It is linear.
    }

-- | A signature with refinements. Its symbols are 'Symbol'.
data RefinedSignature sort = RefinedSignature
    { refinedBase :: SortedSignature sort Symbol
    -- ^ The sorts, the functions, the roots, and the value sorts. A value sort has an 'Interval'.
    , refinedSemantics :: [(Symbol, FunctionSemantics)]
    -- ^ The semantics of some functions. A function without an entry has no measure and no precondition.
    , refinedConditions :: [(sort, Refinement)]
    -- ^ A condition on the integers of a value sort, besides its interval.
    , refinedNesting :: Int
    -- ^ The functions nested in a term, at most. The bound 0 gives the values and the constants.
    }

-- | A reason why a refined signature is not valid.
data RefinedError sort
    = -- | The base signature is not valid.
      RefinedBaseError !(SignatureError sort Symbol)
    | -- | A condition names a sort that has no values.
      ConditionWithoutValues !sort
    | -- | An entry of the semantics names a symbol that is not a function.
      SemanticsOfUnknownFunction !Symbol
    | -- | The nesting is negative.
      NegativeNesting !Int
    deriving (Eq, Show)

-- | A measure or a precondition of a function with one argument, from a function of the term of the argument.
unary :: (Expr -> r) -> [Expr] -> r
unary f [a] = f a
unary _ arguments = error ("unary: " <> show (length arguments) <> " arguments")

-- | A measure or a precondition of a function with two arguments, from a function of their terms.
binary :: (Expr -> Expr -> r) -> [Expr] -> r
binary f [a, b] = f a b
binary _ arguments = error ("binary: " <> show (length arguments) <> " arguments")

-- | A function as a contract with the formula of the list of the terms of the arguments.
data ListContract = ListContract !Int ([Expr] -> Formula)

instance ContractBuilder ListContract where
    contractArity (ListContract count _) = Arity count
    contractFormulaFrom index (ListContract count formula) =
        formula [variable (contractTermName (index + fromIntegral position)) | position <- [0 .. count - 1]]

-- | A measure of the list of the terms of the arguments.
data ListMeasure = ListMeasure !Int ([Expr] -> Expr)

instance MeasureBuilder ListMeasure where
    measureArity (ListMeasure count _) = Arity count
    measureTermFrom index (ListMeasure count measure) =
        measure [variable (contractTermName (index + fromIntegral position)) | position <- [0 .. count - 1]]

checkRefined :: (Ord sort) => ValueCodec sort Symbol -> RefinedSignature sort -> Either (RefinedError sort) ()
checkRefined codec refined = do
    either (Left . RefinedBaseError) Right $ checkSignatureWith (Just codec) base
    case [sort | (sort, _) <- refinedConditions refined, sort `notElem` map valueSort (sortedValues base)] of
        sort : _ -> Left $ ConditionWithoutValues sort
        [] -> Right ()
    case [symbol | (symbol, _) <- refinedSemantics refined, symbol `notElem` map functionSymbol (sortedFunctions base)] of
        symbol : _ -> Left $ SemanticsOfUnknownFunction symbol
        [] -> Right ()
    if refinedNesting refined < 0 then Left $ NegativeNesting $ refinedNesting refined else Right ()
  where
    base = refinedBase refined

{- | The terms of a refined signature as a compiled refinement generator.

The solver decides the preconditions once, and 'Data.CFTA.Gen.Refinement.compile'
counts the values of a value sort without listing them. The result is a finite
generator, so all queries of "Data.CFTA.Gen" apply. The compile step can fail
with a 'GenError', for example 'Data.CFTA.Gen.Error.InexactMeasure' when a
precondition or a measure names an argument whose function has no measure.
-}
refinedGen ::
    (Ord sort) =>
    Entailment ->
    ValueCodec sort Symbol ->
    RefinedSignature sort ->
    IO (Either (Either (RefinedError sort) GenError) (LTAGen (Term Symbol)))
refinedGen solver codec refined = case checkRefined codec refined of
    Left err -> pure $ Left $ Left err
    Right () -> either (Left . Right) Right <$> LTAGen.compileWith solver generator
  where
    base = refinedBase refined
    semantics = Map.fromList (refinedSemantics refined)
    conditions = Map.fromListWith (\new old v -> old v .&& new v) (refinedConditions refined)
    sorts = Map.keys (Map.fromList [(sort, ()) | sort <- sortedSorts base])

    -- One generator for each sort and each nesting level, shared.
    table = LazyMap.fromList [((level, sort), generatorAt level sort) | level <- [0 .. refinedNesting refined], sort <- sorts]
    generatorAt level sort =
        LTAGen.oneof $
            values sort
                <> [constant f | f <- functionsOf sort, null (functionArguments f)]
                <> [applied level f | level > 0, f <- functionsOf sort, not (null (functionArguments f))]
    functionsOf sort = [f | f <- sortedFunctions base, functionResult f == sort]
    generator = LTAGen.oneof [table LazyMap.! (refinedNesting refined, root) | root <- sortedRoots base]

    values sort = case [valueSource v | v <- sortedValues base, valueSort v == sort] of
        Interval low high : _ ->
            [ (\n -> Term.Node (injectInteger codec n) []) <$> (LTAGen.every @Integer `LTAGen.satisfying` bounded)
            ]
          where
            bounded v = literal low .<= v .&& v .<= literal high .&& extra v
        Pool symbols : _ ->
            [ conditioned $
                LTAGen.oneof
                    [ LTAGen.leaf (Term.Node symbol []) symbol (poolRefinement symbol)
                    | symbol <- symbols
                    ]
            ]
        [] -> []
      where
        extra = fromMaybe (const true) (Map.lookup sort conditions)
        conditioned pooled
            | Map.member sort conditions = pooled `LTAGen.satisfying` extra
            | otherwise = pooled

    -- The refinement of a pool entry: its integer when it has one, and nothing otherwise.
    poolRefinement symbol = case projectInteger codec symbol of
        Just n -> \v -> v .== literal n
        Nothing -> const true

    constant f =
        let symbol = functionSymbol f
            refinement = case semanticsMeasure =<< Map.lookup symbol semantics of
                Just measure -> \v -> v .== measure []
                Nothing -> const true
         in LTAGen.leaf (Term.Node symbol []) symbol refinement

    applied level f = case Map.lookup symbol semantics of
        Nothing -> LTAGen.node symbol child
        Just FunctionSemantics{semanticsMeasure = Nothing, semanticsPrecondition = precondition} ->
            LTAGen.guarded symbol (ListContract count (fromMaybe (const true) precondition)) child
        Just FunctionSemantics{semanticsMeasure = Just measure, semanticsPrecondition = precondition} ->
            LTAGen.measured symbol (ListContract count (fromMaybe (const true) precondition)) (ListMeasure count measure) child
      where
        symbol = functionSymbol f
        count = length (functionArguments f)
        child = Term.Node symbol <$> traverse (\argument -> table LazyMap.! (level - 1, argument)) (functionArguments f)

-- | A reason why a term is not a term of a refined signature.
data RefinedTypeError sort
    = -- | The term is not well-typed in the base signature.
      NotWellTyped !(TypeError sort Symbol)
    | -- | The integer of a value fails the condition of its sort.
      ConditionFailed !Path !Symbol
    | -- | The solver does not decide the condition of a value.
      ConditionUnknown !Path !Symbol
    | -- | The solver proves that the precondition of a function fails.
      PreconditionFailed !Path !Symbol
    | -- | The solver does not decide the precondition of a function. The solver could not prove it, and could not refute it. A precondition that names an argument without a measure is also unknown.
      PreconditionUnknown !Path !Symbol
    | -- | The nesting of the functions exceeds the bound.
      NestingExceeded !Path !Symbol
    deriving (Eq, Show)

{- | Check that a term is a term of a refined signature.

The term must be well-typed as 'typeCheckWith' says. Then the first node in
preorder that fails is reported: a value that fails the condition of its sort,
a function whose precondition the solver refutes, or a function that exceeds
the nesting. A verdict of 'Unknown' is kept apart from 'No': it gives
'ConditionUnknown' or 'PreconditionUnknown'.

The measure of each node is a term of the integers of its values, so the solver
decides each precondition on the integers of this term.
-}
refinedTypeCheck ::
    (Ord sort) =>
    Entailment ->
    ValueCodec sort Symbol ->
    RefinedSignature sort ->
    Term Symbol ->
    IO (Either (RefinedTypeError sort) sort)
refinedTypeCheck solver codec refined term = case typeCheckWith codec (refinedBase refined) term of
    Left err -> pure $ Left $ NotWellTyped err
    Right sort -> fmap (const sort) <$> walk [] 0 term
  where
    base = refinedBase refined
    semantics = Map.fromList (refinedSemantics refined)
    conditions = Map.fromListWith (\new old v -> old v .&& new v) (refinedConditions refined)

    -- The measures of the nodes, bottom-up and pure, then the checks in preorder.
    measureOf (Term.Node symbol children) = case integerOf symbol of
        Just n | null children -> Just (literal n)
        _ -> do
            FunctionSemantics{semanticsMeasure = Just measure} <- Map.lookup symbol semantics
            measure <$> traverse measureOf children
    integerOf = projectInteger codec

    walk reversed depth (Term.Node symbol children)
        | null children
        , Just sort <- valueSortOf codec base symbol = do
            let condition = fromMaybe (const true) (Map.lookup sort conditions)
                -- A value without an integer has the refinement that holds for all integers.
                consequent = maybe (refinementFormula condition) (condition . literal) (integerOf symbol)
            verdict <- entails solver true consequent
            pure $ case verdict of
                Yes -> Right ()
                No -> Left $ ConditionFailed here symbol
                Unknown -> Left $ ConditionUnknown here symbol
        | depth + 1 > refinedNesting refined && not (null children) = pure $ Left $ NestingExceeded here symbol
        | Just FunctionSemantics{semanticsPrecondition = Just precondition} <- Map.lookup symbol semantics = do
            let arguments =
                    [ fromMaybe (variable ("unmeasured_" <> show position)) (measureOf child)
                    | (position, child) <- zip [0 :: Int ..] children
                    ]
            let formula = precondition arguments
            -- An argument without a measure is a free name. The solver would
            -- refute the precondition for some value of the name, which is not
            -- a refutation of the term.
            verdict <-
                if any (isPrefixOf "unmeasured_") (freeNames formula)
                    then pure Unknown
                    else entails solver true formula
            case verdict of
                Yes -> inChildren
                No -> pure $ Left $ PreconditionFailed here symbol
                Unknown -> pure $ Left $ PreconditionUnknown here symbol
        | otherwise = inChildren
      where
        here = path (map ChildIndex (reverse reversed))
        inChildren = firstFailure [walk (index : reversed) (depth + 1) child | (index, child) <- zip [0 ..] children]

    firstFailure [] = pure (Right ())
    firstFailure (action : rest) = action >>= either (pure . Left) (const (firstFailure rest))
