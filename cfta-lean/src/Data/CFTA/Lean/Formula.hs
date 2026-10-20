{-# LANGUAGE OverloadedStrings #-}

{- | Translate refinement entailment to a closed Lean proposition.

The supported values are integers, booleans, and named types from a theory.
Functions must be fully applied. Predicates denote propositions.
All formula connectives and quantifiers are supported. Terms can use integer
literals, negation, addition, subtraction, multiplication, and conditionals.
Division and remainder require a positive integer literal as the divisor.
They use Lean's Euclidean integer division and remainder.

Real sorts, casts, higher-order sorts, and function-valued terms are rejected.
An undeclared value has integer sort. An undeclared applied function takes
integers and returns an integer. Inconsistent uses are rejected.
-}
module Data.CFTA.Lean.Formula (
    entailmentProposition,
    renderEntailment,
) where

import Control.Monad (foldM, unless)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import Data.CFTA.Formula (Formula (..), Name (..), Relation (..), Sort (..), Term (..), freeNames)
import Data.CFTA.Lean.Theory (Theory)
import qualified Data.CFTA.Lean.Theory as Theory
import Data.CFTA.Symbol (valueName)

{- | Universally close the implication from the ambient assumptions and the
antecedent to the consequent.

A binding @(fresh, original)@ copies the declared sort of @original@, or
integer sort when it has no declaration. It does not assert equality.
A fresh name must not occur in the declarations or be free in an ambient
assumption. The distinguished 'valueName' has an implicit integer declaration
unless an explicit declaration gives its sort. Repeated declarations or fresh
bindings must agree on the sort. The same rule applies to repeated names
within one quantifier.

Generated identifiers replace all source names. Quantifier bindings have
lexical scope. No source name becomes Lean source text.
-}
entailmentProposition ::
    [(Name, Sort)] ->
    [Formula] ->
    [(Name, Name)] ->
    Formula ->
    Formula ->
    Either String Text
entailmentProposition declarations assumptions bindings antecedent consequent =
    snd <$> renderEntailment [] declarations assumptions bindings antecedent consequent

{- | Type check an entailment and render its definitions and closed proposition.
Keep every declared value in the closure. A declared type can be empty, so
removing an unused value would change the meaning of the closed proposition.
-}
renderEntailment ::
    Theory ->
    [(Name, Sort)] ->
    [Formula] ->
    [(Name, Name)] ->
    Formula ->
    Formula ->
    Either String (Text, Text)
renderEntailment theory declarations assumptions bindings antecedent consequent = do
    unless (length theory == Set.size (Set.fromList (map fst theory))) (Left "Duplicate theory name")
    supplied <- checkedBindings theory declarations
    unless
        (all (`Map.notMember` supplied) (Map.keys (functionEnvironment theory)))
        (Left "A declaration conflicts with a theory name")
    definitions <- theoryText theory
    let declared = supplied <> Map.singleton (Name (Text.pack valueName)) IntSort
        reserved = Map.keysSet declared <> Map.keysSet (functionEnvironment theory) <> Set.fromList (concatMap freeNames assumptions)
        freshBinding fresh (name, original) = do
            unless (name `Set.notMember` reserved) (Left "A fresh binding conflicts with the ambient scope")
            insertSort fresh (name, Map.findWithDefault IntSort original declared)
    fresh <- foldM freshBinding Map.empty bindings
    let globals = functionEnvironment theory
        known = fresh <> declared <> Map.map fst globals
        uses = concatMap (freeUses Set.empty) (assumptions <> [antecedent, consequent])
    inferred <- foldM insertSort Map.empty [(name, sort) | (name, sort) <- uses, Map.notMember name known]
    let used = fresh <> declared <> Map.restrictKeys inferred (Set.fromList (map fst uses))
        variables =
            Map.fromList
                [ (name, (sort, "cfta_f" <> decimal index))
                | (index, (name, sort)) <- zip [0 :: Int ..] (Map.toAscList used)
                , Map.notMember name globals
                ]
        environment = variables <> globals
    premise <- formulaText theory 0 environment (And (assumptions <> [antecedent]))
    conclusion <- formulaText theory 0 environment consequent
    proposition <- quantify theory "∀" (Map.elems variables) (binary "→" premise conclusion)
    pure (definitions, proposition)

-- | Insert a sort, and reject a different sort for an existing name.
insertSort :: Map Name Sort -> (Name, Sort) -> Either String (Map Name Sort)
insertSort sorts (name, sort) = case Map.lookup name sorts of
    Just old | old /= sort -> Left "A name has incompatible sorts or application arities"
    _ -> Right (Map.insert name sort sorts)

-- | Validate declarations. A nullary function has its result sort.
checkedBindings :: Theory -> [(Name, Sort)] -> Either String (Map Name Sort)
checkedBindings theory = foldM add Map.empty
  where
    add sorts (name, sort) = do
        checked <- supportedSort theory sort
        insertSort sorts (name, checked)

-- | Accept scalar values and first-order functions over scalar values.
supportedSort :: Theory -> Sort -> Either String Sort
supportedSort theory sort = case sort of
    IntSort -> Right IntSort
    BoolSort -> Right BoolSort
    FunctionSort [] result -> scalar result
    FunctionSort arguments result -> FunctionSort <$> traverse scalar arguments <*> scalar result
    RealSort -> Left "Real sorts are not supported"
    NamedSort name arguments -> case lookup name theory of
        Just (Theory.TypeConstructor arity _)
            | arity == length arguments && arity >= 0 -> NamedSort name <$> traverse scalar arguments
        _ -> Left "Unknown named type or incorrect type arity"
  where
    scalar IntSort = Right IntSort
    scalar BoolSort = Right BoolSort
    scalar named@NamedSort{} = supportedSort theory named
    scalar RealSort = Left "Real sorts are not supported"
    scalar FunctionSort{} = Left "Higher-order sorts are not supported"

-- | Collect the default sorts of free uses, without crossing a binding.
freeUses :: Set Name -> Formula -> [(Name, Sort)]
freeUses bound formula = case formula of
    Top -> []
    Bottom -> []
    And parts -> foldMap (freeUses bound) parts
    Or parts -> foldMap (freeUses bound) parts
    Not inner -> freeUses bound inner
    Atom _ left right -> termUses left <> termUses right
    Predicate _ arguments -> foldMap termUses arguments
    Forall names inner -> under names inner
    Exists names inner -> under names inner
  where
    under names = freeUses (bound <> Set.fromList (map fst names))
    use name sort = [(name, sort) | name `Set.notMember` bound]
    termUses term = case term of
        Lit _ -> []
        Var name -> use name IntSort
        App name [] -> use name IntSort
        App name arguments ->
            use name (FunctionSort (replicate (length arguments) IntSort) IntSort) <> foldMap termUses arguments
        Neg inner -> termUses inner
        Add left right -> termUses left <> termUses right
        Sub left right -> termUses left <> termUses right
        Mul left right -> termUses left <> termUses right
        Div left right -> termUses left <> termUses right
        Mod left right -> termUses left <> termUses right
        Ite condition yes no -> freeUses bound condition <> termUses yes <> termUses no
        Cast inner _ -> termUses inner

-- | Render a formula in its lexical environment.
formulaText :: Theory -> Int -> Map Name (Sort, Text) -> Formula -> Either String Text
formulaText theory depth environment formula = case formula of
    Top -> Right "True"
    Bottom -> Right "False"
    And parts -> connective "True" "∧" <$> traverse recurse parts
    Or parts -> connective "False" "∨" <$> traverse recurse parts
    Not inner -> ("(¬ " <>) . (<> ")") <$> recurse inner
    Atom relation left right -> do
        (leftSort, leftText) <- termText theory depth environment left
        (rightSort, rightText) <- termText theory depth environment right
        unless (leftSort == rightSort) (Left "A comparison has different operand sorts")
        unless (relation `elem` [Eq, Ne] || leftSort == IntSort) (Left "An ordered comparison requires integers")
        pure (binary (relationText relation) leftText rightText)
    Predicate name arguments -> do
        (expected, identifier) <- predicateSignature theory name
        actual <- traverse (termText theory depth environment) arguments
        unless (map fst actual == expected) (Left "A predicate has incorrect argument sorts or arity")
        pure ("(" <> Text.unwords (identifier : map snd actual) <> ")")
    Forall names inner -> boundFormula "∀" names inner
    Exists names inner -> boundFormula "∃" names inner
  where
    recurse = formulaText theory depth environment
    boundFormula quantifier names inner = do
        checked <- checkedBindings theory names
        unless (all ((`Map.notMember` functionEnvironment theory) . fst) names) (Left "A binder conflicts with a theory name")
        let entries =
                [ (name, (checked Map.! name, "cfta_b" <> decimal depth <> "_" <> decimal index))
                | (index, (name, _)) <- zip [0 :: Int ..] names
                ]
            nested = Map.fromList entries <> environment
        body <- formulaText theory (depth + 1) nested inner
        quantify theory quantifier (map snd entries) body

-- | Check and render a scalar term.
termText :: Theory -> Int -> Map Name (Sort, Text) -> Term -> Either String (Sort, Text)
termText theory depth environment term = case term of
    Lit literal -> Right (IntSort, "(" <> decimal literal <> " : Int)")
    Var name -> value =<< named name
    App name arguments -> do
        (sort, identifier) <- named name
        case (sort, arguments) of
            (FunctionSort expected result, _) -> do
                actual <- traverse recurse arguments
                unless (map fst actual == expected) (Left "A function application has incorrect argument sorts or arity")
                pure (result, "(" <> Text.unwords (identifier : map snd actual) <> ")")
            (_, []) -> value (sort, identifier)
            _ -> Left "A scalar name is applied to arguments"
    Neg inner -> do
        text <- integer inner
        pure (IntSort, "(-" <> text <> ")")
    Add left right -> arithmetic "+" left right
    Sub left right -> arithmetic "-" left right
    Mul left right -> arithmetic "*" left right
    Div left right -> quotient "Int.ediv" left right
    Mod left right -> quotient "Int.emod" left right
    Ite condition yes no -> do
        predicate <- formulaText theory depth environment condition
        (yesSort, yesText) <- recurse yes
        (noSort, noText) <- recurse no
        unless (yesSort == noSort) (Left "A conditional has different branch sorts")
        typ <- sortText theory yesSort
        pure
            ( yesSort
            , "(@ite "
                <> typ
                <> " "
                <> predicate
                <> " (Classical.propDecidable "
                <> predicate
                <> ") "
                <> yesText
                <> " "
                <> noText
                <> ")"
            )
    Cast _ _ -> Left "Casts are not supported"
  where
    recurse = termText theory depth environment
    named name = maybe (Left "A name has no sort") Right (Map.lookup name environment)
    value pair@(sort, _) = case sort of
        IntSort -> Right pair
        BoolSort -> Right pair
        NamedSort{} -> Right pair
        _ -> Left "Function-valued terms are not supported"
    integer operand = do
        (sort, text) <- recurse operand
        unless (sort == IntSort) (Left "Arithmetic requires integer operands")
        pure text
    arithmetic operator left right = do
        leftText <- integer left
        rightText <- integer right
        pure (IntSort, binary operator leftText rightText)
    quotient operator left right = case right of
        Lit divisor | divisor > 0 -> do
            leftText <- integer left
            rightText <- integer right
            pure (IntSort, "(" <> operator <> " " <> leftText <> " " <> rightText <> ")")
        _ -> Left "Division and remainder require a positive integer literal divisor"

-- | Render a quantifier. An empty binding list leaves the body unchanged.
quantify :: Theory -> Text -> [(Sort, Text)] -> Text -> Either String Text
quantify _ _ [] body = Right body
quantify theory quantifier names body = do
    binders <- traverse binder names
    pure ("(" <> quantifier <> " " <> Text.unwords binders <> ", " <> body <> ")")
  where
    binder (sort, name) = (\typ -> "(" <> name <> " : " <> typ <> ")") <$> sortText theory sort

-- | Render a supported Lean type.
sortText :: Theory -> Sort -> Either String Text
sortText theory sort = case sort of
    IntSort -> Right "Int"
    BoolSort -> Right "Bool"
    FunctionSort arguments result -> do
        sorts <- traverse (sortText theory) (arguments <> [result])
        pure ("(" <> Text.intercalate " → " sorts <> ")")
    RealSort -> Left "Real sorts are not supported"
    NamedSort name arguments -> do
        _ <- supportedSort theory sort
        case lookup name theory of
            Just (Theory.TypeConstructor _ expression) -> do
                rendered <- traverse (sortText theory) arguments
                pure ("(" <> Text.unwords (("(" <> expression <> ")") : rendered) <> ")")
            _ -> Left "Unknown named type"

-- | Generate a distinct Lean name for a theory entry.
definitionName :: Int -> Text
definitionName index = "cfta_d" <> decimal index

-- | The types and generated names of interpreted functions.
functionEnvironment :: Theory -> Map Name (Sort, Text)
functionEnvironment theory =
    Map.fromList
        [ (name, (if null arguments then result else FunctionSort arguments result, definitionName index))
        | (index, (name, Theory.Function arguments result _)) <- zip [0 :: Int ..] theory
        ]

-- | The signature and generated name of a global predicate.
predicateSignature :: Theory -> Name -> Either String ([Sort], Text)
predicateSignature theory name =
    case [(definition, definitionName index) | (index, (key, definition)) <- zip [0 :: Int ..] theory, key == name] of
        [(Theory.Predicate arguments _, identifier)] -> (,) <$> traverse (supportedSort theory) arguments <*> pure identifier
        [(Theory.Defined parameters _, identifier)] -> (,) <$> traverse (supportedSort theory . snd) parameters <*> pure identifier
        _ -> Left "Unknown predicate"

{- | Render typed definitions in dependency order.
Shared definitions can refer only to earlier entries and their parameters.
-}
theoryText :: Theory -> Either String Text
theoryText theory = Text.unlines . snd <$> foldM define ([], []) (zip [0 :: Int ..] theory)
  where
    define (earlier, lines') (index, (name, definition)) = do
        line <- case definition of
            Theory.TypeConstructor arity _ -> do
                unless (arity >= 0) (Left "Negative type constructor arity")
                pure ""
            Theory.Function arguments result expression -> do
                _ <- supportedSort theory (FunctionSort arguments result)
                typ <- sortText theory (FunctionSort arguments result)
                pure ("@[simp] def " <> definitionName index <> " : " <> typ <> " := " <> expression)
            Theory.Predicate arguments expression -> do
                types <- traverse (fmap (<> " → ") . sortText theory) arguments
                pure ("@[simp] def " <> definitionName index <> " : " <> Text.concat types <> "Prop := " <> expression)
            Theory.Defined parameters body -> do
                unless (length parameters == Set.size (Set.fromList (map fst parameters))) (Left "Duplicate definition parameter")
                checked <- checkedBindings theory parameters
                unless
                    (all ((`Map.notMember` functionEnvironment theory) . fst) parameters)
                    (Left "A parameter conflicts with a theory name")
                let variables = Map.fromList [(key, (checked Map.! key, "cfta_p" <> decimal i)) | (i, (key, _)) <- zip [0 :: Int ..] parameters]
                    globals = functionEnvironment earlier
                unless (all (`Map.member` (variables <> globals)) (freeNames body)) (Left "A shared definition has an unbound name")
                rendered <- formulaText earlier 0 (variables <> globals) body
                binders <-
                    traverse
                        (\(sort, identifier) -> (\typ -> "(" <> identifier <> " : " <> typ <> ")") <$> sortText theory sort)
                        [variables Map.! key | (key, _) <- parameters]
                pure ("@[simp] def " <> definitionName index <> " " <> Text.unwords binders <> " : Prop := " <> rendered)
        pure (earlier <> [(name, definition)], lines' <> [line | not (Text.null line)])

-- | Render a comparison operator.
relationText :: Relation -> Text
relationText relation = case relation of
    Eq -> "="
    Ne -> "≠"
    Gt -> ">"
    Ge -> "≥"
    Lt -> "<"
    Le -> "≤"

-- | Join formulas with the given connective and its empty result.
connective :: Text -> Text -> [Text] -> Text
connective empty _ [] = empty
connective _ _ [part] = part
connective empty operator (part : rest) = binary operator part (connective empty operator rest)

-- | Parenthesize a binary expression.
binary :: Text -> Text -> Text -> Text
binary operator left right = "(" <> left <> " " <> operator <> " " <> right <> ")"

-- | Render a generated numeric identifier suffix or an integer literal.
decimal :: (Show a) => a -> Text
decimal = Text.pack . show
