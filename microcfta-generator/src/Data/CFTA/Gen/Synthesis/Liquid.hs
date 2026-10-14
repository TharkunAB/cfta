{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Refinement-typed component synthesis on liquid tree automata.

This is Hegel, the synthesizer of Mishra and Jagannathan, /Liquid Tree
Automata/ (2026), on the engine of microcfta. A query gives arguments with
refinement types and a goal refinement type. The synthesizer runs Algorithm 1
of the paper: it adds the applications of one more size to the automaton,
prunes the applications whose arguments do not satisfy the refinements of
the parameters, merges similar states (a state whose type is a subtype of
another replaces it), and stops at the first size at which the goal is not
empty.

The encoding: a state stands for terms of one type. A query argument is a
leaf whose refinement says that its value is the argument (@v == x@) and
satisfies the argument's refinement. An application of a component is one
transition with a child for each argument, as in the term @take x xs@. Its
guard is a 'Holds' over the children for each refined parameter: the
children's refinements are assumed, and the formal parameters are the
children. Its refinement is inferred: the component's result refinement,
with the formal parameters replaced by the children's values, and the facts
that the children's refinements state about those values. A state is one
term, so a name for the state stands for one value, as the let-bound names
of A-normal form do in the paper. The base types are unified when the
application is built, so a polymorphic component gets one instance for each
application.

A refinement is the conjunction of the qualifiers that the inferred
refinement implies: the atoms of the library and the query, instantiated
with the query's arguments. So there are finitely many
refinements of each base type, and similarity is a subset test.

The reduction uses 'prune', 'similarity', and 'minimize' of
"Data.CFTA.Refinement"; the 'Reduction' option leaves out a step, as the
ablations of the paper do.

A function value is a value of the logic, and the measure @ap@, which the
solver must declare with two arguments, applies it: @ap f x@. A query's
function argument and a component of one base parameter are values, with
their types as refinements: @incr@ has @forall x. ap v x == x + 1@. Every
application says that its value is its head applied to its arguments. A
higher-order component states its result with @ap@, as
@forall k. at v k == ap f (at xs k)@ for @map@.

With 'optionConditionals', a term whose guard holds only under a condition
gets the condition as a requirement, and a conditional @if c t e@ at the goal
can be a solution, as in the paper's starred queries.

'checker' and 'preciseChecker' check single programs of
"Data.CFTA.Gen.Synthesis" against a query, with the same inference and
entailment. "Data.CFTA.Gen.Synthesis.Hybrid" lists Hectare's programs and
checks them this way.
-}
module Data.CFTA.Gen.Synthesis.Liquid (
    -- * Refinement types
    RType (..),
    refined,
    plain,
    (.:),
    (-->),
    measure,
    baseOf,
    parseRType,
    renderRType,

    -- * Libraries and queries
    Component,
    LiquidQuery (..),
    parseQuery,

    -- * Synthesis
    Reduction (..),
    Options (..),
    defaultOptions,
    Statistics (..),
    Outcome (..),
    synthesize,
    renderTerm,

    -- * Checks of single programs
    Checker (..),
    checker,
    preciseChecker,
    componentRoles,
) where

import Control.Applicative ((<|>))
import Control.Exception (try)
import Control.Monad (filterM, foldM, unless, when)
import Data.Char (isAlphaNum, isDigit, isLower, isSpace)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (inits, intercalate, nub, tails)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)
import System.IO (hPutStrLn, stderr)
import Text.ParserCombinators.ReadP (
    ReadP,
    between,
    chainl1,
    look,
    many1,
    munch,
    munch1,
    option,
    pfail,
    satisfy,
    (+++),
 )
import qualified Text.ParserCombinators.ReadP as ReadP

import Data.CFTA.Formula (Formula (..), Name (..), Sort (IntSort))
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Gen.Synthesis (Type (..), typeParser)
import qualified Data.CFTA.Gen.Synthesis as Synthesis
import Data.CFTA.Gen.Synthesis.Internal.Syntax (lexeme, parseWhole, token)
import Data.CFTA.Index (ArgumentIndex (..))
import Data.CFTA.Refinement (
    Automaton,
    ChildIndex (..),
    Entailment (entailsWithBindings),
    Guard (Holds, Satisfies),
    Node (Node),
    Subtyping (..),
    Verdict (..),
    contractTermName,
    edgeChildren,
    entailmentWithBindings,
    minimize,
    noConstraint,
    nodeEdges,
    path,
    prune,
    semanticConstraint,
    similarityWithin,
    transitionRefinement,
    transitionSymbol,
    pattern Transition,
 )
import qualified Data.CFTA.Refinement as Refinement
import Data.CFTA.Refinement.Expression (
    Expr,
    Refinement,
    fromExpr,
    lnot,
    refinementFormula,
    toExpr,
    variable,
    (.&&),
    (./=),
    (.<),
    (.<=),
    (.==),
    (.>),
    (.>=),
    (.||),
 )
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..))
import Data.CFTA.Symbol (Symbol (Symbol), symbolText, valueName)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- Refinement types

{- | A refinement type: a base type with a refinement of its value, or a
dependent function type whose parameter name can occur in the result.
-}
data RType
    = RBase Type Formula
    | RArrow Text RType RType
    deriving (Eq, Show)

-- | The base type with a refinement, as in @{v : int | v >= 0}@.
refined :: Type -> Refinement -> RType
refined typ refinement = RBase typ (refinementFormula refinement)

-- | The base type with the refinement that always holds.
plain :: Type -> RType
plain typ = RBase typ Top

infixr 1 -->
infix 2 .:

-- | A named parameter of a function type.
(.:) :: Text -> RType -> (Text, RType)
(.:) = (,)

-- | The dependent function type from a named parameter to a result.
(-->) :: (Text, RType) -> RType -> RType
(-->) (name, parameter) = RArrow name parameter

{- | An uninterpreted function of the logic applied to its arguments, as in
@measure "len" [v]@. The synthesizer declares each measure as a function
from integers to an integer.
-}
measure :: Text -> [Expr] -> Expr
measure name arguments = toExpr $ Formula.App (Name name) (map fromExpr arguments)

-- | The base type of a refinement type, with function types as 'TFun'.
baseOf :: RType -> Type
baseOf (RBase typ _) = typ
baseOf (RArrow _ parameter result) = TFun (baseOf parameter) (baseOf result)

-- Libraries and queries

-- | A library component: its name and its refinement type.
type Component = (Text, RType)

-- | A query: the arguments with their refinement types, and the goal type.
data LiquidQuery = LiquidQuery
    { liquidArguments :: [(Text, RType)]
    , liquidGoal :: RType
    }
    deriving (Show)

{- | Parse a query as a function signature in the syntax of 'parseRType': the
parameters are the arguments, and the result is the goal, as in
@l:{v:[a] | len v >= 1} -> i:Int -> {v:a | v = at l i}@.
-}
parseQuery :: Text -> Either String LiquidQuery
parseQuery text = (\typ -> LiquidQuery (parametersOf typ) (resultOf typ)) <$> parseRType text

-- Syntax

{- | Parse a refinement type in the syntax of LiquidHaskell. The type
@x:T -> R@ is a dependent function type: the parameter @x@ has the type @T@,
and the result @R@ can mention @x@. The arrow associates to the right, and
each parameter has a name. The type @{v:B | p}@ is the base type @B@ with the
refinement @p@ of its value @v@. A base type has the syntax of
'Data.CFTA.Gen.Synthesis.parseType', and a base type without braces has no
refinement. Put the function type of a parameter in parentheses, as in
@f:(a -> b)@.

A refinement compares terms with @=@ (or @==@), @\/=@, @\<@, @\<=@, @>@,
and @>=@. The formula @true@ always holds, and @false@ never holds. A
refinement combines formulas with @not@, @&&@, @||@, @=>@ (implication), and
@\<=>@ (equivalence). Each operator in this list binds more strongly than
the next. The formula @forall k. p@ holds for every integer @k@. Its body
continues to the end of the parentheses or braces around it. A term is an
integer, a name, a measure applied to its arguments, as in
@at xs (len xs - 1)@, or a sum, a difference, or a product, with the
precedences of Haskell.

A Boolean is an integer that is zero or one. So @{v:Bool | v \<=> p}@ means
that @v@ is one or zero, and that it is one exactly when @p@ holds.
-}
parseRType :: Text -> Either String RType
parseRType = parseWhole "refinement type" rtypeParser

-- | The parser of 'parseRType'.
rtypeParser :: ReadP RType
rtypeParser = arrow +++ base
  where
    arrow = do
        name <- identifier
        _ <- token ":"
        parameter <- base
        _ <- token "->"
        RArrow (Text.pack name) parameter <$> rtypeParser
    base = braces +++ (plain <$> typeParser)
    braces = between (token "{") (token "}") $ do
        binder <- identifier
        _ <- token ":"
        typ <- typeParser
        _ <- token "|"
        let resolve name = variable (if name == binder then valueName else name)
            boolean = do
                unless (typ == TCons "Bool" []) pfail
                keyword binder
                operator "<=>"
                truth (variable valueName) <$> formulaParser resolve
        RBase typ <$> (boolean +++ formulaParser resolve)

-- | The parser of a refinement. The function gives the term of each name.
formulaParser :: (String -> Expr) -> ReadP Formula
formulaParser resolve = equivalence
  where
    equivalence = do
        left <- implication
        option left ((left <=>) <$> (operator "<=>" *> implication))
    implication = do
        left <- disjunctive
        option left ((left ==>) <$> (operator "=>" *> implication))
    disjunctive = do
        left <- conjunctive
        option left ((left .||) <$> (operator "||" *> disjunctive))
    conjunctive = do
        left <- unary
        option left ((left .&&) <$> (operator "&&" *> conjunctive))
    unary =
        ReadP.choice
            [ lnot <$> (keyword "not" *> unary)
            , Top <$ keyword "true"
            , Bottom <$ keyword "false"
            , quantified
            , comparison
            , between (token "(") (token ")") equivalence
            ]
    quantified = do
        keyword "forall"
        names <- many1 identifier
        _ <- token "."
        body <- formulaParser (\name -> if name `elem` names then variable name else resolve name)
        -- The body continues to the end of the parentheses or braces around it.
        rest <- look
        unless (all (`elem` (")}" :: String)) (take 1 (dropWhile isSpace rest))) pfail
        pure $ Forall [(Name (Text.pack name), IntSort) | name <- names] body
    comparison = do
        left <- additive
        relation <-
            ReadP.choice
                [ (.==) <$ (operator "=" +++ operator "==")
                , (./=) <$ operator "/="
                , (.<) <$ operator "<"
                , (.<=) <$ operator "<="
                , (.>) <$ operator ">"
                , (.>=) <$ operator ">="
                ]
        relation left <$> additive
    additive = chainl1 multiplicative (((+) <$ operator "+") +++ ((-) <$ operator "-"))
    multiplicative = chainl1 measured ((*) <$ operator "*")
    measured = (measure . Text.pack <$> identifier <*> many1 atomic) +++ atomic
    atomic =
        ReadP.choice
            [ fromInteger . read <$> lexeme (munch1 isDigit)
            , resolve <$> identifier
            , between (token "(") (token ")") additive
            ]

-- | A name of the syntax of 'parseRType' that is not a keyword.
identifier :: ReadP String
identifier = do
    name <- word
    when (name `elem` ["not", "forall", "true", "false"]) pfail
    pure name

-- | A keyword of the syntax of 'parseRType'.
keyword :: String -> ReadP ()
keyword expected = do
    name <- word
    unless (name == expected) pfail

-- | A lowercase letter, and then letters, digits, underscores, and primes, after spaces.
word :: ReadP String
word = lexeme $ (:) <$> satisfy isLower <*> munch (\c -> isAlphaNum c || c `elem` ("_'" :: String))

{- | An operator after spaces. The operator characters run together, so that
@\<=@ is not @\<@.
-}
operator :: String -> ReadP ()
operator expected = do
    found <- lexeme $ munch1 (`elem` ("=<>/&|+-*" :: String))
    unless (found == expected) pfail

infixr 1 ==>

-- | Implication.
(==>) :: Formula -> Formula -> Formula
p ==> q = lnot p .|| q

-- | Equivalence.
(<=>) :: Formula -> Formula -> Formula
p <=> q = (p ==> q) .&& (q ==> p)

-- | A Boolean that holds exactly when the formula does.
truth :: Expr -> Formula -> Formula
truth v formula = (v .== 1 .|| v .== 0) .&& ((v .== 1) <=> formula)

{- | A refinement type in the syntax of 'parseRType', with @v@ for the value of
each refinement. For a type that 'parseRType' gives, 'parseRType' reads the
result back to the same type if the type has no other name @v@.
-}
renderRType :: RType -> String
renderRType typ = case typ of
    RArrow name parameter result -> Text.unpack name <> ":" <> renderParameter parameter <> " -> " <> renderRType result
    RBase base Top -> Synthesis.renderType base
    RBase base formula -> "{v:" <> Synthesis.renderType base <> " | " <> formulaText 0 formula <> "}"
  where
    renderParameter parameter = case parameter of
        RBase TFun{} Top -> "(" <> renderRType parameter <> ")"
        RArrow{} -> "(" <> renderRType parameter <> ")"
        RBase{} -> renderRType parameter
    -- The precedence is 0 for any formula, 1 for a part of a conjunction or
    -- a disjunction, and 2 for the formula of a negation.
    formulaText :: Int -> Formula -> String
    formulaText context formula = case formula of
        Top -> "true"
        Bottom -> "false"
        Atom relation left right -> termText 0 left <> " " <> relationText relation <> " " <> termText 0 right
        Not inner -> "not " <> formulaText 2 inner
        And parts -> parenthesize (context > 0) $ intercalate " && " (map (formulaText 1) parts)
        Or parts -> parenthesize (context > 0) $ intercalate " || " (map (formulaText 1) parts)
        Forall bound inner -> parenthesize (context > 0) $ "forall " <> names bound <> ". " <> formulaText 0 inner
        Exists bound inner -> parenthesize (context > 0) $ "exists " <> names bound <> ". " <> formulaText 0 inner
    names bound = unwords [Text.unpack name | (Name name, _) <- bound]
    relationText relation = case relation of
        Formula.Eq -> "="
        Formula.Ne -> "/="
        Formula.Lt -> "<"
        Formula.Le -> "<="
        Formula.Gt -> ">"
        Formula.Ge -> ">="
    -- The precedence is 0 for any term, 6 and 7 for the operands of a sum, 7
    -- and 8 for the operands of a product, and 10 for the argument of a
    -- measure.
    termText :: Int -> Formula.Term -> String
    termText context term = case term of
        Formula.Var name | name == value -> "v"
        Formula.Var (Name name) -> Text.unpack name
        Formula.Lit constant -> show constant
        Formula.App (Name name) arguments -> parenthesize (context > 9) $ unwords (Text.unpack name : map (termText 10) arguments)
        Formula.Add left right -> parenthesize (context > 6) $ termText 6 left <> " + " <> termText 7 right
        Formula.Sub left right -> parenthesize (context > 6) $ termText 6 left <> " - " <> termText 7 right
        Formula.Mul left right -> parenthesize (context > 7) $ termText 7 left <> " * " <> termText 8 right
        _ -> "(" <> Formula.renderTerm term <> ")"
    parenthesize True text = "(" <> text <> ")"
    parenthesize False text = text

-- Synthesis

-- | Which reduction steps run after each size, as in the paper's ablations.
data Reduction = Reduction
    { reductionPrune :: Bool
    , reductionMinimize :: Bool
    }
    deriving (Eq, Show)

-- | The options of a synthesis run.
data Options = Options
    { optionReduction :: Reduction
    , optionMaximumSize :: Int
    -- ^ The largest number of applications in a solution.
    , optionTrace :: Bool
    -- ^ Print the states and the queries of each size to the standard error.
    , optionConditionals :: Bool
    -- ^ Add the head @if@ and give a term a requirement when its guard holds only under a condition.
    }
    deriving (Show)

-- | Both reductions, at most five applications, as in the paper, no trace, and no conditionals.
defaultOptions :: Options
defaultOptions = Options (Reduction True True) 5 False False

-- | What a run did: the work at each size.
data Statistics = Statistics
    { statisticsSize :: Int
    -- ^ The number of applications of the solutions, or the bound.
    , statisticsStates :: Int
    -- ^ The states before reduction, at the last size.
    , statisticsReducedStates :: Int
    -- ^ The states after reduction, at the last size.
    , statisticsQueries :: Int
    -- ^ The entailment queries.
    , statisticsUndecided :: Int
    -- ^ The entailment queries that the solver could not decide.
    }
    deriving (Eq, Show)

-- | The solutions at the first size at which there is one, or none.
data Outcome = Outcome
    { outcomeSolutions :: [Term Symbol]
    , outcomeAutomaton :: Maybe Automaton
    -- ^ The goal automaton of the solutions: a @goal@ transition over each solution.
    , outcomeStatistics :: Statistics
    }
    deriving (Show)

{- | A state of the construction: its type, and the automaton node whose
transitions are its terms.
-}
data State = State
    { stateType :: RType
    , stateRequirement :: Formula
    -- ^ A condition on the query arguments under which the term is defined: 'Top' for most terms.
    , stateNode :: Automaton
    }

{- | Run Algorithm 1: add the applications of each size, reduce, and stop at
the first size at which some term has the goal type.
-}
synthesize :: Entailment -> Options -> [Component] -> LiquidQuery -> IO (Either String Outcome)
synthesize entailment options components query = do
    (counted, counter, undecided) <- countedEntailment entailment (environmentOf query)
    let
        realizeWith' candidates =
            realizeWith
                counted
                (if optionConditionals options then Just (conditionsOf candidates) else Nothing)
                (abstractWith counted candidates)
        statistics size built reduced = do
            queries <- readIORef counter
            unknown <- readIORef undecided
            pure $ Statistics size (stateCount built) (stateCount reduced) queries unknown
    candidates <- simplifyQualifiers counted (qualifiers components query)
    when (optionTrace options) $
        mapM_
            (\(base, qualifier) -> hPutStrLn stderr $ "qualifier of " <> renderType base <> ": " <> Formula.renderFormula qualifier)
            candidates
    let realize = realizeWith' candidates
        go size bySize
            | size > optionMaximumSize options = Right . Outcome [] Nothing <$> statistics size bySize bySize
            | otherwise = do
                new <- catMaybes <$> traverse realize (applications heads bySize size)
                let built = Map.insert size new bySize
                reduced <- reduceRound counted (optionReduction options) functions built
                when (optionTrace options) $ do
                    queries <- readIORef counter
                    unknown <- readIORef undecided
                    seconds <- getMonotonicTime
                    hPutStrLn stderr $
                        "size "
                            <> show size
                            <> ": built "
                            <> show (length new)
                            <> " new states, kept "
                            <> either (const "?") (show . stateCount) reduced
                            <> " states; "
                            <> show queries
                            <> " queries, "
                            <> show unknown
                            <> " undecided; at "
                            <> show seconds
                    when (optionConditionals options) $
                        either
                            (const (pure ()))
                            ( \states ->
                                mapM_
                                    ( \(requirement, count) -> hPutStrLn stderr ("  " <> show (count :: Int) <> " kept with requirement " <> Formula.renderFormula requirement)
                                    )
                                    $ Map.toList (Map.fromListWith (+) [(stateRequirement state, 1) | state <- concat (Map.elems states)])
                            )
                            reduced
                case reduced of
                    Left err -> pure $ Left err
                    Right states -> do
                        solutions <-
                            goalAutomaton counted (if optionConditionals options then Just realize else Nothing) (liquidGoal query) states
                        case solutions of
                            Left err -> pure $ Left err
                            Right automaton -> case maybe [] goalSolutions automaton of
                                [] -> go (size + 1) states
                                found -> Right . Outcome found automaton <$> statistics size built states
    leaves <-
        catMaybes
            <$> traverse
                realize
                ( map argumentLeaf (liquidArguments query)
                    <> [componentLeaf component | component@(_, typ) <- components, valued components query typ]
                )
    go 1 (Map.singleton 0 leaves)
  where
    heads = headsOf components query
    functions = Map.fromList [(name, typ) | (name, typ@RArrow{}) <- components <> liquidArguments query]

{- | The heads of a query: the components and the query arguments of function
type, each with its function value in the logic.
-}
headsOf :: [Component] -> LiquidQuery -> [(Text, RType, Formula.Term)]
headsOf components query =
    [(name, typ, Formula.Var (functionConstant name)) | (name, typ@RArrow{}) <- components]
        <> [(name, typ, Formula.Var (Name name)) | (name, typ@RArrow{}) <- liquidArguments query]

-- | What the query arguments' refinements state about them.
environmentOf :: LiquidQuery -> Formula
environmentOf query =
    Formula.conjunction
        ( [Formula.substitute [(value, Formula.Var (Name name))] refinement | (name, RBase _ refinement) <- liquidArguments query]
            <> [lifted (Formula.Var (Name name)) typ | (name, typ@RArrow{}) <- liquidArguments query]
        )

{- | The entailment of a run, with the counts of its solver queries and of
the queries that the solver did not decide. The environment holds in every
query. An entailment that the solver cannot decide, or decide within its
time limit, counts as failed: a guard that needs it does not apply, so no
wrong term is kept. The verdicts are kept, because many applications ask
the same questions.
-}
countedEntailment :: Entailment -> Formula -> IO (Entailment, IORef Int, IORef Int)
countedEntailment entailment environment = do
    counter <- newIORef (0 :: Int)
    undecided <- newIORef (0 :: Int)
    known <- newIORef Map.empty
    let counted = entailmentWithBindings $ \bindings antecedent consequent -> do
            let key = (bindings, antecedent, consequent)
            remembered <- Map.lookup key <$> readIORef known
            case remembered of
                Just verdict -> pure verdict
                Nothing | antecedent == consequent -> pure Yes
                Nothing -> do
                    modifyIORef' counter (+ 1)
                    answer <-
                        either (\TimeLimitReached{} -> Unknown) id
                            <$> try (entailsWithBindings entailment bindings (Formula.conjunction [environment, antecedent]) consequent)
                    verdict <-
                        if answer == Unknown
                            then No <$ modifyIORef' undecided (+ 1)
                            else pure answer
                    modifyIORef' known (Map.insert key verdict)
                    pure verdict
    pure (counted, counter, undecided)

{- | A check of single programs against a query, with the inference and the
entailment of 'synthesize'.
-}
data Checker = Checker
    { checkProgram :: Synthesis.Program -> IO Bool
    {- ^ Whether a program is defined and has the goal type. A program is a
    query argument, a constant, a function value, or a head applied to all
    its parameters, as in the terms of 'synthesize'. Another program fails.
    -}
    , checkerQueries :: IO (Int, Int)
    -- ^ The solver queries so far, and the queries that the solver did not decide.
    }

{- | The checker of a query. It builds the state of a program bottom up, as
'synthesize' builds the state of a term: the base types unify, each guard
must hold, and the refinement of a subprogram is abstracted to the
qualifiers. The states of the subprograms are kept, so a subprogram that
many programs share gets one state. The goal check of a program uses its
precise refinement, which implies the abstracted one. The checker does not
make conditionals.
-}
checker :: Entailment -> [Component] -> LiquidQuery -> IO Checker
checker = checkerWith True

{- | The checker of a query that does not abstract: each subprogram keeps its
precise refinement. It asks no qualifier queries, and its refinements grow
with the program.
-}
preciseChecker :: Entailment -> [Component] -> LiquidQuery -> IO Checker
preciseChecker = checkerWith False

{- | The roles of the components in the terms of 'synthesize': the number of
parameters of each component, zero for a constant, and whether it can be an
argument without arguments of its own ('valued').
-}
componentRoles :: [Component] -> LiquidQuery -> [(Text, Int, Bool)]
componentRoles components query = [(name, length (parametersOf typ), valued components query typ) | (name, typ) <- components]

-- | The checker of a query, with or without the abstraction of subprograms to the qualifiers.
checkerWith :: Bool -> Entailment -> [Component] -> LiquidQuery -> IO Checker
checkerWith abstracts entailment components query = do
    (counted, counter, undecided) <- countedEntailment entailment (environmentOf query)
    candidates <-
        if abstracts then simplifyQualifiers counted (qualifiers components query) else pure []
    states <- newIORef Map.empty
    let
        -- Without conditions, each guard is decided when the state is made.
        realize = realizeWith counted (Just [])
        precise = realize (\_ refinement -> pure refinement)
        abstracted = if abstracts then realize (abstractWith counted candidates) else precise
        -- The state of a subprogram, kept for the next programs.
        stateOf program = do
            remembered <- Map.lookup program <$> readIORef states
            case remembered of
                Just state -> pure state
                Nothing -> do
                    state <- pendingOf program >>= maybe (pure Nothing) abstracted
                    modifyIORef' states (Map.insert program state)
                    pure state
        -- The term of a program before its refinement is abstracted.
        pendingOf program = case spine program [] of
            (name, [])
                | Just typ <- lookup name (liquidArguments query) -> pure $ Just (argumentLeaf (name, typ))
                | Just typ <- lookup name components, valued components query typ -> pure $ Just (componentLeaf (name, typ))
            (name, arguments)
                | Just (typ, function) <- lookup name heads
                , length (parametersOf typ) == length arguments -> do
                    children <- traverse stateOf arguments
                    pure $ sequence children >>= application (Just function) name typ
            _ -> pure Nothing
        check program = case liquidGoal query of
            RArrow{} -> pure False
            RBase base goal -> do
                found <- pendingOf program >>= maybe (pure Nothing) precise
                case found of
                    Just State{stateType = RBase actual refinement}
                        | actual == base -> (== Yes) <$> entailsWithBindings counted [] refinement goal
                    _ -> pure False
    pure $ Checker check ((,) <$> readIORef counter <*> readIORef undecided)
  where
    heads = [(name, (typ, function)) | (name, typ, function) <- headsOf components query]
    spine (Synthesis.App function argument) arguments = spine function (argument : arguments)
    spine (Synthesis.Var name) arguments = (name, arguments)

-- | The number of states at all sizes.
stateCount :: Map Int [State] -> Int
stateCount = sum . map length . Map.elems

{- | A term of a state before its refinement is abstracted: its name, its type
with the precise refinement, its children, what the children must satisfy
for each refined parameter, and the condition under which each child is used.
The last two are over the children's names in a guard.
-}
data Pending = Pending Text RType [State] [Formula] [Formula]

-- | The term of a query argument: its value is the argument.
argumentLeaf :: (Text, RType) -> Pending
argumentLeaf (name, typ) = case typ of
    RBase base refinement ->
        Pending
            name
            (RBase base (Formula.conjunction [Atom Formula.Eq (Formula.Var value) (Formula.Var (Name name)), refinement]))
            []
            []
            []
    RArrow{} ->
        Pending
            name
            ( RBase
                (baseOf typ)
                (Formula.conjunction [Atom Formula.Eq (Formula.Var value) (Formula.Var (Name name)), lifted (Formula.Var value) typ])
            )
            []
            []
            []

-- | The term of a component as a value: a constant, or a function passed as an argument.
componentLeaf :: Component -> Pending
componentLeaf (name, typ) = case typ of
    RBase{} -> Pending name typ [] [] []
    RArrow{} ->
        Pending
            name
            ( RBase
                (baseOf typ)
                ( Formula.conjunction
                    [Atom Formula.Eq (Formula.Var value) (Formula.Var (functionConstant name)), lifted (Formula.Var value) typ]
                )
            )
            []
            []
            []

{- | Whether a component is a value: a constant, or a function of one
parameter of a base type to a base type, as @incr@. A function of more
parameters, or with a function parameter, is only applied: its value would
bring nested quantifiers into every refinement that uses it.
-}
firstOrder :: RType -> Bool
firstOrder typ = case typ of
    RBase{} -> True
    RArrow _ (RBase parameter _) (RBase result _) -> not (isFunctionType parameter) && not (isFunctionType result)
    RArrow{} -> False
  where
    isFunctionType TFun{} = True
    isFunctionType _ = False

{- | Whether a component is a leaf: a constant, or a function value of
'firstOrder' type when a head of the library or the query takes a function.
Without such a head, a function value has no use.
-}
valued :: [Component] -> LiquidQuery -> RType -> Bool
valued components query typ = case typ of
    RBase{} -> True
    RArrow{} -> firstOrder typ && any takesFunction (components <> liquidArguments query)
  where
    takesFunction (_, head') = any (isFunction . baseOf . snd) (parametersOf head')
    isFunction TFun{} = True
    isFunction _ = False

{- | The value of a component as a function: a name of the logic for each
component.
-}
functionConstant :: Text -> Name
functionConstant name = Name ("__microcfta_function_" <> name)

{- | The application of a function value to an argument, as the logic sees
it: the measure @ap@, which the solver must declare with two arguments.
-}
applied :: Formula.Term -> Formula.Term -> Formula.Term
applied function argument = Formula.App (Name "ap") [function, argument]

{- | The refinement that a function type gives a function value: for every
argument that satisfies the parameter, the application of the function
satisfies the result. A function parameter's own type is the assumption.
-}
lifted :: Formula.Term -> RType -> Formula
lifted function typ = case typ of
    RBase _ refinement -> Formula.substitute [(value, function)] refinement
    RArrow name parameter result ->
        let bound = Name ("__microcfta_bound_" <> name)
            argument = Formula.Var bound
            assumption = case parameter of
                RBase _ refinement -> Formula.substitute [(value, argument)] refinement
                RArrow{} -> lifted argument parameter
            conclusion = Formula.substitute [(Name name, argument)] (lifted (applied function (Formula.Var (Name name))) result)
         in if conclusion == Top
                then Top
                else Forall [(bound, IntSort)] (if assumption == Top then conclusion else Formula.implies assumption conclusion)

{- | The head @if c t e@ at a base type: the value is @t@ when @c@ is one, and
@e@ otherwise. Its branches are used under these conditions.
-}
conditional :: Type -> RType
conditional base =
    RArrow "c" (RBase (TCons "Bool" []) Top)
        $ RArrow "t" (RBase base Top)
        $ RArrow "e" (RBase base Top)
        $ RBase
            base
            ( Formula.conjunction
                [ Formula.implies chosen (Atom Formula.Eq (Formula.Var value) (Formula.Var (Name "t")))
                , Formula.implies (Not chosen) (Atom Formula.Eq (Formula.Var value) (Formula.Var (Name "e")))
                ]
            )
  where
    chosen = Atom Formula.Eq (Formula.Var (Name "c")) (Formula.Lit 1)

-- | The conditions of the qualifiers, for the requirements of terms.
conditionsOf :: [(Type, Formula)] -> [Formula]
conditionsOf candidates =
    nub
        [ condition
        | (_, qualifier) <- candidates
        , positive <- atomsOf qualifier
        , value `notElem` Formula.freeNames positive
        , condition <- [positive, Not positive]
        ]

{- | The state of a term, with the refinement of a base type abstracted to
the qualifiers that it implies, or none when the term cannot be defined.

The requirement of a term is the conjunction of its children's requirements,
except a requirement that the child's path condition implies, and of a
condition for each obligation that holds only under one. Without conditions,
the guard keeps every obligation, and 'prune' removes a term whose guard
fails. With conditions, an obligation that does not hold gets the first
condition that the query and the children allow and under which it holds, or
the term is left out. The guard then holds: it is the condition implies the
obligation. A term whose requirement the query rules out is left out.
-}
realizeWith :: Entailment -> Maybe [Formula] -> (Type -> Formula -> IO Formula) -> Pending -> IO (Maybe State)
realizeWith entailment conditions abstract (Pending name typ children obligations pathConditions) = do
    discharged <- traverse discharge obligations
    inherited <- traverse inherit (zip children (pathConditions <> repeat Top))
    case sequence discharged of
        Nothing -> pure Nothing
        Just decided -> do
            let requirement = Formula.conjunction (map snd decided <> inherited)
                guard = case map fst decided of
                    [] -> noConstraint
                    [one] -> semanticConstraint (Holds childPaths one)
                    several -> semanticConstraint (Refinement.And [Holds childPaths one | one <- several])
            -- A term whose requirement contradicts the query is never defined.
            impossible <- if requirement == Top then pure False else holds requirement Bottom
            if impossible then pure Nothing else Just <$> build requirement guard
  where
    childPaths = [path [ChildIndex child] | child <- [0 .. length children - 1]]
    assumed = assumedOf children
    -- The facts of the children that have no requirement. The facts of a
    -- child with a requirement hold only under it, so they cannot show it.
    unconditional =
        assumedOf
            [ if stateRequirement child == Top then child else child{stateType = RBase (baseOf (stateType child)) Top}
            | child <- children
            ]
    assumedOf states =
        Formula.conjunction
            [ Formula.substitute [(value, Formula.Var (contractName index))] refinement
            | (index, State (RBase _ refinement) _ _) <- zip [0 ..] states
            ]
    holds antecedent consequent = (== Yes) <$> entailsWithBindings entailment [] antecedent consequent
    discharge obligation = case conditions of
        Nothing -> pure $ Just (obligation, Top)
        Just candidates -> do
            valid <- holds assumed obligation
            if valid
                then pure $ Just (obligation, Top)
                else
                    fmap (\condition -> (Formula.implies condition obligation, condition))
                        <$> findM (abduces obligation) candidates
    -- A condition that the query allows, and under which the obligation holds.
    abduces obligation condition = do
        refuted <- holds (Formula.conjunction [condition, assumed]) Bottom
        if refuted then pure False else holds (Formula.conjunction [condition, assumed]) obligation
    inherit (child, pathCondition)
        | stateRequirement child == Top = pure Top
        | pathCondition == Top = pure (stateRequirement child)
        | otherwise = do
            implied <- holds (Formula.conjunction [pathCondition, unconditional]) (stateRequirement child)
            pure $ if implied then Top else stateRequirement child
    build requirement guard = case typ of
        RBase base precise -> do
            refinement <- abstract base (Formula.conjunction [precise, requirement])
            pure $
                State
                    (RBase base refinement)
                    requirement
                    (Node [Transition (labelled name base requirement) refinement (map stateNode children) guard])
        RArrow{} -> pure $ State typ requirement (Node [Transition (Symbol (escapeName name)) Top (map stateNode children) guard])

-- | The first element for which an action gives 'True'.
findM :: (Monad m) => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ [] = pure Nothing
findM p (x : xs) = p x >>= \found -> if found then pure (Just x) else findM p xs

-- | The name of a child in a guard: each child's refinement holds of its name.
contractName :: Int -> Name
contractName = Name . Text.pack . contractTermName . ArgumentIndex

{- | The symbol of a term of a base type: the name, and the label of its base
type and requirement after an at sign, so that similarity compares only
terms of one base type and one requirement. The name is escaped
('escapeName'), so the first at sign ends it, also when the name or the
label has an at sign.
-}
labelled :: Text -> Type -> Formula -> Symbol
labelled name base requirement = Symbol (escapeName name <> "@" <> labelOf base requirement)

{- | A name with no at sign: each backslash becomes two, and each at sign
becomes a backslash and @a@. A name without them does not change.
-}
escapeName :: Text -> Text
escapeName = Text.concatMap $ \c -> case c of
    '\\' -> "\\\\"
    '@' -> "\\a"
    _ -> Text.singleton c

-- | The name that 'escapeName' escaped.
unescapeName :: Text -> Text
unescapeName = Text.pack . go . Text.unpack
  where
    go ('\\' : 'a' : rest) = '@' : go rest
    go ('\\' : c : rest) = c : go rest
    go (c : rest) = c : go rest
    go [] = []

-- | The base type, and the requirement after a question mark unless it is 'Top'.
labelOf :: Type -> Formula -> Text
labelOf base requirement =
    Text.pack (renderType base) <> if requirement == Top then "" else "?" <> Text.pack (Formula.renderFormula requirement)

-- | A base type as text, as in @List a@.
renderType :: Type -> String
renderType typ = case typ of
    TVar name -> Text.unpack name
    TFun argument result -> "(" <> renderType argument <> " -> " <> renderType result <> ")"
    TCons name [] -> Text.unpack name
    TCons name arguments -> "(" <> unwords (Text.unpack name : map renderType arguments) <> ")"

-- | The name and the label of a symbol, as 'labelled' writes them.
unlabelled :: Symbol -> (Text, Maybe Text)
unlabelled symbol = case Text.breakOn "@" (symbolText symbol) of
    (name, rest) | not (Text.null rest) -> (unescapeName name, Just (Text.drop 1 rest))
    (name, _) -> (unescapeName name, Nothing)

-- | The name of the value of a refinement.
value :: Name
value = Name (Text.pack valueName)

{- | The applications of a size: each head applied to arguments whose sizes
add up to the size minus one. A size counts the applications of a term.
-}
applications :: [(Text, RType, Formula.Term)] -> Map Int [State] -> Int -> [Pending]
applications heads bySize size =
    [ pending
    | (name, typ, function) <- heads
    , let parameters = parametersOf typ
    , sizes <- compositions (size - 1) (length parameters)
    , arguments <- mapM (\argumentSize -> Map.findWithDefault [] argumentSize bySize) sizes
    , Just pending <- [application (Just function) name typ arguments]
    ]

-- | The parameters of a function type.
parametersOf :: RType -> [(Text, RType)]
parametersOf (RArrow name parameter result) = (name, parameter) : parametersOf result
parametersOf RBase{} = []

-- | The result of a function type after all its parameters.
resultOf :: RType -> RType
resultOf (RArrow _ _ result) = resultOf result
resultOf base = base

-- | The ways to write a number as an ordered sum of so many non-negative parts.
compositions :: Int -> Int -> [[Int]]
compositions total 1 = [[total]]
compositions total parts = [first : rest | first <- [0 .. total], rest <- compositions (total - first) (parts - 1)]

{- | The application of a head to argument states, when their base types
unify with the parameters: the transition with its guard and its inferred
result type. A head is applied to all its parameters.
-}
application :: Maybe Formula.Term -> Text -> RType -> [State] -> Maybe Pending
application function name typ arguments = do
    let parameters = parametersOf typ
    substitution <-
        foldM unifyParameter Map.empty (zip (map (baseOf . snd) parameters) (map (baseOf . stateType) arguments))
    let formals = map fst parameters
        named = [(Name formal, Formula.Var (contractName index)) | (index, formal) <- zip [0 ..] formals]
        obligations =
            [ Formula.substitute ((value, Formula.Var (contractName index)) : named) requirement
            | (index, (_, RBase _ requirement)) <- zip [0 ..] parameters
            , requirement /= Top
            ]
        base = baseOf (substituteBase substitution (resultOf typ))
        refinement = case resultOf typ of
            RBase _ result -> inferred function formals (pathConditionsOf name) arguments result
            RArrow{} -> Top
    pure $
        Pending name (RBase base refinement) arguments obligations (map (Formula.substitute named) (pathConditionsOf name))
  where
    unifyParameter substitution (expected, actual) = unify substitution expected actual

{- | The path condition of each parameter of a head, over the formal
parameters: the branches of @if@ are used under its condition and its
negation, and every other parameter always.
-}
pathConditionsOf :: Text -> [Formula]
pathConditionsOf "if" = [Top, chosen, Not chosen]
  where
    chosen = Atom Formula.Eq (Formula.Var (Name "c")) (Formula.Lit 1)
pathConditionsOf _ = []

{- | The precise refinement of an application: the result refinement with
the formal parameters replaced by the arguments' values, that the value is
the head's function value applied to them, and the facts that the arguments'
refinements state about those values, each under the path condition of its
parameter. An argument whose refinement fixes its value, as
@v == x@ does for the query argument @x@, gives that value. Another argument
gives a name, as a let-bound name of A-normal form does. A state is one term,
so an argument that occurs twice has one name.
-}
inferred :: Maybe Formula.Term -> [Text] -> [Formula] -> [State] -> Formula -> Formula
inferred function formals pathConditions arguments result =
    Formula.conjunction
        ( actually result
            : [Atom Formula.Eq (Formula.Var value) (foldl applied head' (map fst actuals)) | Just head' <- [function]]
                <> [ if pathCondition == Top then fact else Formula.implies (actually pathCondition) fact
                   | ((_, Just fact), pathCondition) <- zip actuals (pathConditions <> repeat Top)
                   ]
        )
  where
    actually = Formula.substitute (zip (map Name formals) (map fst actuals))
    nodes = map stateNode arguments
    actuals =
        [ case stateType argument of
            RBase _ refinement ->
                let actual = fromMaybe (Formula.Var name) (definedValue refinement)
                 in (actual, Just (Formula.substitute [(value, actual)] refinement))
            RArrow{} -> (Formula.Var name, Nothing)
        | argument <- arguments
        , let name = Name ("__microcfta_argument_" <> Text.pack (show (length (takeWhile (/= stateNode argument) nodes))))
        ]

-- | The term that a refinement says the value equals, when it says so in a top-level conjunct.
definedValue :: Formula -> Maybe Formula.Term
definedValue refinement = case refinement of
    Atom Formula.Eq (Formula.Var name) term | name == value && value `notElem` termNames term -> Just term
    Atom Formula.Eq term (Formula.Var name) | name == value && value `notElem` termNames term -> Just term
    And parts -> foldr (\part found -> definedValue part <|> found) Nothing parts
    _ -> Nothing
  where
    termNames term = Formula.freeNames (Atom Formula.Eq term term)

-- Qualifiers

{- | The qualifiers, with the base types that they refine. A qualifier is an
atom of a refinement in the library or the query that mentions the value.
The other names of an atom from the library are its formal parameters. Each
is replaced by each query argument of a matching base type, and an atom with a
formal parameter that no argument matches is left out. A second set replaces
an integer formal parameter also by a compound term of the goal, as @n - 1@
from @len v == n - 1 + len l@, a function formal parameter by a compound
term that the goal applies, and another formal parameter by a goal term of
a projection of its type, so that an intermediate term keeps what the
library says about it. Each atom of the goal also gives the atom without a
constant offset on a side of a comparison, as @at v k == ap f x@ from
@at v k == ap f x + 1@: a term before a last step such as @map incr@ has that
weaker goal. For each query argument
@x@, @v == x@ is a qualifier of its base type. As in the liquid types of the
paper's title, a refinement is a conjunction of qualifiers, so there are
finitely many refinements of each base type.

A measure that a component's result is, as @fst@'s result is @proj1 p@, is
a projection. A qualifier with a projection of the value, as
@len (proj1 v) <= x@, also gives the qualifier of the projection's value,
@len v <= x@, for the component's result type: the part of a pair can then
keep what the pair's qualifier says about it. A component whose result type
is a type variable gives no projection.

The base type @Bool@ holds Booleans as zero and one. A condition is an atom
of a qualifier that does not mention the value, or its negation. For each
condition @c@, @v == 1 ==> c@ and @c ==> v == 1@ are qualifiers of @Bool@, so
a Boolean can keep which conditions it decides.
-}
qualifiers :: [Component] -> LiquidQuery -> [(Type, Formula)]
qualifiers components query =
    nub $
        direct
            <> concatMap (ofComponent fromTerms) components
            <> [ (TCons "Bool" [], qualifier)
               | condition <-
                    nub
                        [ c
                        | (_, atom) <- direct
                        , positive <- atomsOf atom
                        , value `notElem` Formula.freeNames positive
                        , c <- [positive, Not positive]
                        ]
               , qualifier <- [Formula.implies true condition, Formula.implies condition true]
               ]
            <> [ (base, projected)
               | (_, atom) <- direct
               , (function, base) <- projectionTypes
               , let projected = mapTerms (\term -> if term == Formula.App function [Formula.Var value] then Formula.Var value else term) atom
               , projected /= atom
               ]
  where
    true = Atom Formula.Eq (Formula.Var value) (Formula.Lit 1)
    projectionTypes =
        [ (function, base)
        | (_, typ) <- components
        , RBase base result <- [resultOf typ]
        , not (isVariable base)
        , Just (Formula.App function _) <- [definedValue result]
        ]
    isVariable TVar{} = True
    isVariable _ = False
    direct =
        [(base, atom) | (_, RBase base refinement) <- liquidArguments query, atom <- atoms refinement]
            <> [(base, atom) | RBase base refinement <- [liquidGoal query], atom <- atoms refinement]
            <> [ (base, weakened)
               | RBase base refinement <- [liquidGoal query]
               , atom <- atoms refinement
               , weakened <- withoutOffsets atom
               ]
            <> [(base, Atom Formula.Eq (Formula.Var value) (Formula.Var name)) | (name, base) <- arguments]
            <> [ (baseOf typ, qualifier)
               | (name, typ) <- constants
               , qualifier <- Atom Formula.Eq (Formula.Var value) (Formula.Var name) : atoms (lifted (Formula.Var value) typ)
               ]
            <> concatMap (ofComponent fromArguments) components
    atoms = filter (elem value . Formula.freeNames) . conjuncts
    arguments = [(Name name, baseOf typ) | (name, typ) <- liquidArguments query]
    -- The components as function values: their names and types.
    constants = [(functionConstant name, typ) | (name, typ@RArrow{}) <- components, valued components query typ]
    fromArguments base =
        [Formula.Var name | (name, actual) <- arguments, isJust (unify Map.empty base actual)]
            <> [Formula.Var name | isFunction base, (name, typ) <- constants, isJust (unify Map.empty base (baseOf typ))]
    isFunction TFun{} = True
    isFunction _ = False
    -- A term of the goal that does not mention the value, as @n - 1@, can
    -- also take the place of an integer formal, one that the goal applies,
    -- as @hd fl@ in @ap(hd fl, s)@, of a function formal, and one whose
    -- measure a component's result is, as @mapM(g, l)@ for @map@, of a
    -- formal of that result's type.
    fromTerms base
        | base == TCons "Int" [] = nub $ fromArguments base <> goalTerms
        | isFunction base =
            nub $ fromArguments base <> [function | Formula.App (Name "ap") [function, _] <- goalTerms, isCompound function]
        | otherwise =
            nub $
                fromArguments base
                    <> [ term
                       | term@(Formula.App function _) <- goalTerms
                       , (projection, typ) <- projectionTypes
                       , function == projection
                       , isJust (unify Map.empty typ base)
                       ]
    goalTerms =
        [ term
        | RBase _ refinement <- [liquidGoal query]
        , term <- termsOf refinement
        , isCompound term
        , value `notElem` Formula.freeNames (Atom Formula.Eq term term)
        ]
    isCompound Formula.Var{} = False
    isCompound Formula.Lit{} = False
    isCompound _ = True
    ofComponent matching (_, typ) =
        let parameters = parametersOf typ
            formals = [(Name formal, baseOf parameter) | (formal, parameter) <- parameters]
            refinements = [(base, refinement) | RBase base refinement <- map snd parameters <> [resultOf typ]]
         in [ (base, instantiated)
            | (base, refinement) <- refinements
            , atom <- atoms refinement
            , instantiated <- instances matching formals atom
            ]
    instances matching formals atom =
        let mentioned = [(formal, base) | (formal, base) <- formals, formal `elem` Formula.freeNames atom]
         in [Formula.substitute (zip (map fst mentioned) choice) atom | choice <- mapM (matching . snd) mentioned]

{- | Simplify the qualifiers under the environment. A part of a disjunction
that the environment rules out goes, and a qualifier that the environment
implies goes, because every state has it.
-}
simplifyQualifiers :: Entailment -> [(Type, Formula)] -> IO [(Type, Formula)]
simplifyQualifiers entailment candidates = do
    simplified <- traverse simplify candidates
    nub
        <$> filterM
            (\(_, qualifier) -> (/= Yes) <$> entails Top qualifier)
            [candidate | candidate@(_, qualifier) <- simplified, qualifier /= Bottom]
  where
    entails = entailsWithBindings entailment []
    simplify (base, Or parts) = (,) base . Formula.disjunction <$> filterM (\part -> (/= Yes) <$> entails Top (Not part)) parts
    simplify candidate = pure candidate

{- | The formula without one constant offset, in each place where a
comparison that mentions the value has one on a side: @at v k == ap f x + 1@
gives @at v k == ap f x@.
-}
withoutOffsets :: Formula -> [Formula]
withoutOffsets formula = case formula of
    Atom relation left right
        | value `elem` Formula.freeNames formula ->
            [Atom relation left' right | left' <- unoffset left] <> [Atom relation left right' | right' <- unoffset right]
    And parts -> And <$> inOne parts
    Or parts -> Or <$> inOne parts
    Not inner -> Not <$> withoutOffsets inner
    Forall bound inner -> Forall bound <$> withoutOffsets inner
    _ -> []
  where
    unoffset (Formula.Add term (Formula.Lit _)) = [term]
    unoffset (Formula.Sub term (Formula.Lit _)) = [term]
    unoffset _ = []
    inOne parts = [before <> (part' : after) | (before, part : after) <- zip (inits parts) (tails parts), part' <- withoutOffsets part]

-- | The atoms of a formula, outside quantifiers.
atomsOf :: Formula -> [Formula]
atomsOf formula = case formula of
    And parts -> concatMap atomsOf parts
    Or parts -> concatMap atomsOf parts
    Not inner -> atomsOf inner
    Atom{} -> [formula]
    _ -> []

-- | The terms of the atoms of a formula, with their subterms.
termsOf :: Formula -> [Formula.Term]
termsOf formula = case formula of
    And parts -> concatMap termsOf parts
    Or parts -> concatMap termsOf parts
    Not inner -> termsOf inner
    Atom _ left right -> subterms left <> subterms right
    _ -> []
  where
    subterms term =
        term : case term of
            Formula.App _ arguments -> concatMap subterms arguments
            Formula.Neg a -> subterms a
            Formula.Add a b -> subterms a <> subterms b
            Formula.Sub a b -> subterms a <> subterms b
            Formula.Mul a b -> subterms a <> subterms b
            Formula.Div a b -> subterms a <> subterms b
            Formula.Mod a b -> subterms a <> subterms b
            Formula.Ite condition a b -> termsOf condition <> subterms a <> subterms b
            Formula.Cast a _ -> subterms a
            _ -> []

-- | Apply a function to every term of a formula, innermost first.
mapTerms :: (Formula.Term -> Formula.Term) -> Formula -> Formula
mapTerms f = formula
  where
    formula phi = case phi of
        And parts -> And (map formula parts)
        Or parts -> Or (map formula parts)
        Not inner -> Not (formula inner)
        Atom relation left right -> Atom relation (term left) (term right)
        Forall bound inner -> Forall bound (formula inner)
        Exists bound inner -> Exists bound (formula inner)
        _ -> phi
    term t = f $ case t of
        Formula.App name arguments -> Formula.App name (map term arguments)
        Formula.Neg a -> Formula.Neg (term a)
        Formula.Add a b -> Formula.Add (term a) (term b)
        Formula.Sub a b -> Formula.Sub (term a) (term b)
        Formula.Mul a b -> Formula.Mul (term a) (term b)
        Formula.Div a b -> Formula.Div (term a) (term b)
        Formula.Mod a b -> Formula.Mod (term a) (term b)
        Formula.Ite condition a b -> Formula.Ite (formula condition) (term a) (term b)
        Formula.Cast a sort -> Formula.Cast (term a) sort
        _ -> t

{- | Abstract a precise refinement of a base type to the conjunction of the
qualifiers of that type that it implies. A qualifier that is a conjunct of
the refinement needs no solver.
-}
abstractWith :: Entailment -> [(Type, Formula)] -> Type -> Formula -> IO Formula
abstractWith entailment candidates base precise =
    Formula.conjunction
        <$> filterM
            ( \qualifier -> if qualifier `elem` known then pure True else (== Yes) <$> entailsWithBindings entailment [] precise qualifier
            )
            [ qualifier
            | (source, qualifier) <- candidates
            , isJust (unify Map.empty source base)
            ]
  where
    known = conjuncts precise

-- Base types

{- | Unify an expected base type with an actual one. The type variables of
the expected type take values; the actual type's variables are rigid.
-}
unify :: Map Text Type -> Type -> Type -> Maybe (Map Text Type)
unify substitution expected actual = case (expected, actual) of
    (TVar name, _) -> case Map.lookup name substitution of
        Just bound -> if bound == actual then Just substitution else Nothing
        Nothing -> Just (Map.insert name actual substitution)
    (TFun expectedArgument expectedResult, TFun actualArgument actualResult) ->
        unify substitution expectedArgument actualArgument >>= \next -> unify next expectedResult actualResult
    (TCons expectedName expectedArguments, TCons actualName actualArguments)
        | expectedName == actualName && length expectedArguments == length actualArguments ->
            foldM (\next (e, a) -> unify next e a) substitution (zip expectedArguments actualArguments)
    _ -> Nothing

-- | A refinement type with the type variables of the substitution replaced.
substituteBase :: Map Text Type -> RType -> RType
substituteBase substitution typ = case typ of
    RBase base refinement -> RBase (go base) refinement
    RArrow name parameter result -> RArrow name (substituteBase substitution parameter) (substituteBase substitution result)
  where
    go (TVar name) = Map.findWithDefault (TVar name) name substitution
    go (TFun argument result) = TFun (go argument) (go result)
    go (TCons name arguments) = TCons name (map go arguments)

-- Reduction

{- | One reduction round of Algorithm 1 on the automaton of all states:
'prune' removes the applications whose guards fail, and 'similarity' with
'minimize' merges the states of one base type whose refinement is a subtype
of another's. The root has a transition for each state with its size, and
the states are read back from the reduced automaton.
-}
reduceRound :: Entailment -> Reduction -> Map Text RType -> Map Int [State] -> IO (Either String (Map Int [State]))
reduceRound entailment reduction functions bySize = do
    let root =
            Node
                [ Transition (Symbol ("size:" <> Text.pack (show size))) Top [stateNode state] noConstraint
                | (size, states) <- Map.toList bySize
                , state <- states
                ]
    pruned <-
        if reductionPrune reduction
            then either (Left . show) Right <$> prune entailment root
            else pure (Right root)
    minimized <- case pruned of
        Left err -> pure (Left err)
        Right automaton
            | reductionMinimize reduction -> do
                similar <-
                    similarityWithin
                        (fmap (Text.takeWhile (/= '?')) . snd . unlabelled . transitionSymbol)
                        (stateSubtyping labels)
                        automaton
                pure $ case similar of
                    Left err -> Left (show err)
                    Right found -> either (Left . show) Right (minimize automaton found)
            | otherwise -> pure (Right automaton)
    pure $ readBack functions labels <$> minimized
  where
    labels =
        Map.fromList
            [ (labelOf base (stateRequirement state), (base, stateRequirement state))
            | states <- Map.elems bySize
            , state@State{stateType = RBase base _} <- states
            ]

{- | Subtyping of two terms of one base type. A refinement is a conjunction
of qualifiers that holds every qualifier it implies, so one refinement implies
another when it has all the other's qualifiers. The subtype must also be
defined wherever the supertype is: each condition of its requirement is a
condition of the supertype's. No solver is asked.
-}
stateSubtyping :: Map Text (Type, Formula) -> Subtyping
stateSubtyping labels = Subtyping $ \_ low high ->
    pure $ case (labelled' low, labelled' high) of
        (Just (lowBase, lowRequirement), Just (highBase, highRequirement))
            | lowBase == highBase
            , includes highRequirement lowRequirement
            , includes (transitionRefinement low) (transitionRefinement high) ->
                Yes
        _ -> No
  where
    labelled' transition = snd (unlabelled (transitionSymbol transition)) >>= (`Map.lookup` labels)
    -- Whether the first conjunction has every conjunct of the second.
    includes larger smaller = all (`elem` conjuncts larger) (filter (/= Top) (conjuncts smaller))

-- | The conjuncts of a formula.
conjuncts :: Formula -> [Formula]
conjuncts (And parts) = concatMap conjuncts parts
conjuncts formula = [formula]

-- | The states of each size of a reduced automaton.
readBack :: Map Text RType -> Map Text (Type, Formula) -> Automaton -> Map Int [State]
readBack functions labels root =
    Map.fromListWith (flip (<>)) $
        [ (read (Text.unpack (Text.drop 5 (symbolText (transitionSymbol keeper)))), [state])
        | keeper <- nodeEdges root
        , child <- edgeChildren keeper
        , not (null (nodeEdges child))
        , Just state <- [stateOf child]
        ]
  where
    stateOf node = case nodeEdges node of
        [] -> Nothing
        transitions@(first : _) -> case unlabelled (transitionSymbol first) of
            (_, Just rendered) -> do
                (base, requirement) <- Map.lookup rendered labels
                Just $ State (RBase base (Formula.disjunction (map transitionRefinement transitions))) requirement node
            (name, Nothing) -> (\typ -> State typ Top node) <$> Map.lookup name functions

-- The goal

{- | The goal automaton: a goal transition for each defined state of the
goal's base type, with the guard that its refinement implies the goal's, and
'prune' decides the guards. There is none when no state has the goal's base
type.

With conditionals, a conditional can also be a solution, as in the paper's
starred queries, where the conditional is the whole program. For each
Boolean @c@, the first term that satisfies the goal and its requirement when
@c@ holds, and the first one when @c@ does not hold, are the branches of the
conditional @if c t e@. This asks two questions for each pair of a Boolean and
a term, not one for each triple.
-}
goalAutomaton ::
    Entailment -> Maybe (Pending -> IO (Maybe State)) -> RType -> Map Int [State] -> IO (Either String (Maybe Automaton))
goalAutomaton entailment conditionals goal states = case goal of
    RArrow{} -> pure $ Left "the goal must be a base type"
    RBase base refinement -> do
        let terms = [state | state <- concat (Map.elems states), baseOf (stateType state) == base]
            booleans =
                [state | state <- concat (Map.elems states), baseOf (stateType state) == TCons "Bool" [], stateRequirement state == Top]
        direct <- filterM defined terms
        branched <- case conditionals of
            Nothing -> pure []
            Just realize -> catMaybes <$> traverse (branch realize base refinement terms) booleans
        let candidates = direct <> branched
            root =
                Node
                    [Transition "goal" Top [stateNode state] (semanticConstraint (Satisfies (path [0]) refinement)) | state <- candidates]
        if null candidates
            then pure (Right Nothing)
            else either (Left . show) (Right . Just) <$> prune entailment root
  where
    holds antecedent consequent = (== Yes) <$> entailsWithBindings entailment [] antecedent consequent
    -- A term is a solution only where the query arguments' refinements imply its requirement.
    defined state
        | stateRequirement state == Top = pure True
        | otherwise = holds Top (stateRequirement state)
    branch realize base refinement terms condition = do
        let name = Name "__microcfta_condition"
            chosen = Atom Formula.Eq (Formula.Var name) (Formula.Lit 1)
            known = case stateType condition of
                RBase _ facts -> Formula.substitute [(value, Formula.Var name)] facts
                RArrow{} -> Top
            -- The branch is used when the path can hold, and the path implies
            -- its requirement. Its facts hold under its requirement only.
            solves under term = case stateType term of
                RBase _ facts -> do
                    unreachable <- holds (Formula.conjunction [known, under]) Bottom
                    defined' <- holds (Formula.conjunction [known, under]) (stateRequirement term)
                    if unreachable || not defined'
                        then pure False
                        else holds (Formula.conjunction [known, under, stateRequirement term, facts]) refinement
                RArrow{} -> pure False
        true <- findM (solves chosen) terms
        false <- findM (solves (Not chosen)) terms
        case (true, false) of
            (Just t, Just e)
                | stateNode t /= stateNode e ->
                    maybe (pure Nothing) realize (application Nothing "if" (conditional base) [condition, t, e])
            _ -> pure Nothing

-- | The solutions of a goal automaton: the terms under its goal transitions.
goalSolutions :: Automaton -> [Term Symbol]
goalSolutions automaton = [child | term <- Refinement.terms automaton, child <- Term.subForest term]

-- | A term in the syntax of the paper's solutions, as in @take x (fst p)@.
renderTerm :: Term Symbol -> String
renderTerm term = case Term.subForest term of
    [] -> name
    children -> name <> " " <> unwords (map nested children)
  where
    name = Text.unpack (fst (unlabelled (Term.rootLabel term)))
    nested child = case Term.subForest child of
        [] -> renderTerm child
        _ -> "(" <> renderTerm child <> ")"
