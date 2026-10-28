{-# LANGUAGE OverloadedStrings #-}

{- | SMT-LIB 2.6 text for a theory and for an entailment.

'theoryCommands' declares the datatypes of a theory in one
@declare-datatypes@ command and its definitions in one @define-funs-rec@
command. A split becomes a @match@ term. Each case of the @match@ binds the
fields of its constructor, as the branch of the split does, so the
translation keeps the structure of the body.

'entailmentScript' checks the sorts of a query and unfolds the predicate
definitions, as ground evaluation does. Then it declares the free values,
asserts the assumptions, the antecedent, and the negation of the consequent,
and checks satisfiability. @unsat@ means that the entailment holds. @sat@
means that it does not hold: the definitions terminate, so a model of the
script satisfies them.

Each name becomes a quoted symbol with a prefix for its kind: @t@ for a
datatype sort, @c@ for a constructor, @s@ for a field selector, @f@ for a
function or predicate, @v@ for a free value, and @b@ for a bound name. The
characters @%@, @|@, @\\@, @:@, and the characters outside printable ASCII
become @%@, their decimal code, and @;@. Thus two different names of one kind
give two different symbols, and no name gives an SMT-LIB keyword.

Division and remainder become @div@ and @mod@, which agree with ground
evaluation for a positive divisor. Ground evaluation gives no value for
another divisor. SMT-LIB defines division by a negative number, but Z3 does
not specify division by zero. A query that divides by zero can thus get
@sat@ from Z3 and 'Data.CFTA.Refinement.Verdict.Unknown' from ground
evaluation.

The text needs a solver process. This module does not start one.
-}
module Data.CFTA.Refinement.SmtLib (
    SmtLibError (..),
    theoryCommands,
    entailmentScript,
) where

import Control.Monad (forM, forM_, unless)
import Data.Bifunctor (first)
import Data.Char (ord)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import Data.CFTA.Formula (Formula (..), Name (..), Relation (..), Sort (..), Term (..), freeNames)
import Data.CFTA.Refinement.Definition (DefinitionError, Definitions, unfoldKeeping)
import Data.CFTA.Refinement.Theory (
    Body (..),
    Branch (..),
    Constructor (..),
    Datatype (..),
    Theory,
    TheoryDefinition (..),
    inhabitedDatatypes,
    theoryDatatypes,
    theoryDeclarations,
    theoryDefinitions,
 )

-- | Why a theory or a query has no SMT-LIB text.
data SmtLibError
    = -- | A datatype has no value. SMT-LIB accepts only datatypes with values.
      UninhabitedDatatype !Sort
    | -- | A sort is not an integer, a boolean, a real, or a datatype of the theory.
      SortOutsideTheory !Sort
    | -- | A term has no SMT-LIB form, such as a cast, or a function without a function sort.
      UnsupportedTerm !Term
    | -- | The query fails the sort check, or a predicate has no definition.
      IllSortedQuery !DefinitionError
    deriving (Eq, Show)

-- | The global names of a theory, and the sorts of the free values of a query.
data Context = Context
    { contextConstructors :: !(Set Name)
    , contextDefinitions :: !(Set Name)
    , contextSorts :: !(Set Sort)
    , contextValues :: !(Map Name Sort)
    }

-- | The global names of a theory, with no free values.
theoryContext :: Theory -> Context
theoryContext current =
    Context
        { contextConstructors = Set.fromList [constructorName c | d <- theoryDatatypes current, c <- datatypeConstructors d]
        , contextDefinitions = Set.fromList (map fst (theoryDefinitions current))
        , contextSorts = Set.fromList (map datatypeSort (theoryDatatypes current))
        , contextValues = Map.empty
        }

-- | The commands that declare the datatypes and define the functions and predicates of a theory.
theoryCommands :: Theory -> Either SmtLibError Text
theoryCommands current = do
    forM_ datatypes $ \datatype ->
        unless (datatypeSort datatype `Set.member` inhabitedDatatypes current) $
            Left (UninhabitedDatatype (datatypeSort datatype))
    sorts <- forM datatypes $ \datatype -> do
        name <- sortText context (datatypeSort datatype)
        pure ("(" <> name <> " 0)")
    constructors <- forM datatypes $ \datatype -> fmap (\alternatives -> "(" <> Text.unwords alternatives <> ")") $
        forM (datatypeConstructors datatype) $ \(Constructor name fields) -> do
            selectors <- forM fields $ \(field, sort) -> do
                fieldSort <- sortText context sort
                pure ("(" <> symbol "s" [nameText name, nameText field] <> " " <> fieldSort <> ")")
            pure ("(" <> Text.unwords (symbol "c" [nameText name] : selectors) <> ")")
    signatures <- forM definitions $ \(name, definition) -> do
        let (parameters, result) = case definition of
                FunctionDefinition typed sort _ -> (typed, sortText context sort)
                PredicateDefinition typed _ -> (typed, Right "Bool")
        binders <- traverse (binder context) parameters
        resultText <- result
        pure ("(" <> symbol "f" [nameText name] <> " (" <> Text.unwords binders <> ") " <> resultText <> ")")
    bodies <- forM definitions $ \(_, definition) -> case definition of
        FunctionDefinition parameters _ body -> bodyText (term context) (bound parameters) body
        PredicateDefinition parameters body -> bodyText (formula context) (bound parameters) body
    pure
        $ Text.unlines
        $ [ "(declare-datatypes (" <> Text.unwords sorts <> ") (" <> Text.unwords constructors <> "))"
          | not (null datatypes)
          ]
            <> [ "(define-funs-rec (" <> Text.unwords signatures <> ")\n  (" <> Text.intercalate "\n   " bodies <> "))"
               | not (null definitions)
               ]
  where
    datatypes = theoryDatatypes current
    definitions = theoryDefinitions current
    context = theoryContext current
    bound = Set.fromList . map fst

-- | A body. A split becomes a @match@ term with one case for each branch.
bodyText :: (Set Name -> a -> Either SmtLibError Text) -> Set Name -> Body a -> Either SmtLibError Text
bodyText leaf locals body = case body of
    Expression expression -> leaf locals expression
    Split scrutinee branches -> do
        cases <- forM branches $ \(Branch constructor fields inner) -> do
            rendered <- bodyText leaf (Set.fromList fields <> locals) inner
            let shape = application (symbol "c" [nameText constructor]) [symbol "b" [nameText field] | field <- fields]
            pure ("(" <> shape <> " " <> rendered <> ")")
        pure ("(match " <> symbol "b" [nameText scrutinee] <> " (" <> Text.unwords cases <> "))")

{- | The script of an entailment under a theory, predicate definitions,
declarations, and ambient assumptions. The arguments are those of
'Data.CFTA.Refinement.Ground.groundEntailment', and the script adds the
declarations of the theory. Each declared value and each free value is a
constant of the script. A free value without a declaration is an integer.
-}
entailmentScript ::
    Theory ->
    Definitions ->
    [(Name, Sort)] ->
    [Formula] ->
    [(Name, Name)] ->
    Formula ->
    Formula ->
    Either SmtLibError Text
entailmentScript current definitions declarations assumptions bindings antecedent consequent = do
    commands <- theoryCommands current
    premises <- traverse (prepare declarations) assumptions
    premise <- prepare scope antecedent
    conclusion <- prepare scope consequent
    let free = concatMap freeNames (premises <> [premise, conclusion])
        values =
            Map.fromList $
                [(name, IntSort) | name <- free, name `Set.notMember` globals]
                    <> [(name, sort) | (name, sort) <- reverse scope, name `Set.notMember` globals]
        context = (theoryContext current){contextValues = values}
    constants <- traverse (constant context) (Map.toList values)
    premiseText <- formula context Set.empty (And (premises <> [premise]))
    conclusionText <- formula context Set.empty conclusion
    pure $
        commands
            <> Text.unlines
                (constants <> ["(assert " <> premiseText <> ")", "(assert (not " <> conclusionText <> "))", "(check-sat)"])
  where
    scope = [(fresh, fromMaybe IntSort (lookup original declarations)) | (fresh, original) <- bindings] <> declarations
    globals = Set.fromList (map fst (theoryDeclarations current)) <> Set.fromList (map fst (theoryDefinitions current))
    signatures = Map.fromList [(name, map snd parameters) | (name, PredicateDefinition parameters _) <- theoryDefinitions current]
    prepare names = first IllSortedQuery . unfoldKeeping signatures definitions (theoryDeclarations current <> names)

-- | Declare a free value. A value of a function sort is a function.
constant :: Context -> (Name, Sort) -> Either SmtLibError Text
constant context (name, sort) = do
    (arguments, result) <- case sort of
        FunctionSort parameters value -> (,) <$> traverse (sortText context) parameters <*> sortText context value
        _ -> (,) [] <$> sortText context sort
    pure ("(declare-fun " <> symbol "v" [nameText name] <> " (" <> Text.unwords arguments <> ") " <> result <> ")")

-- | A typed binder.
binder :: Context -> (Name, Sort) -> Either SmtLibError Text
binder context (name, sort) = (\typ -> "(" <> symbol "b" [nameText name] <> " " <> typ <> ")") <$> sortText context sort

-- | A sort of a value: an integer, a boolean, a real, or a datatype of the theory.
sortText :: Context -> Sort -> Either SmtLibError Text
sortText context sort = case sort of
    IntSort -> Right "Int"
    BoolSort -> Right "Bool"
    RealSort -> Right "Real"
    NamedSort _ _ | sort `Set.member` contextSorts context -> Right (symbol "t" [Text.pack (show sort)])
    _ -> Left (SortOutsideTheory sort)

-- | A formula. The bound names hide the global names and the free values.
formula :: Context -> Set Name -> Formula -> Either SmtLibError Text
formula context locals current = case current of
    Top -> Right "true"
    Bottom -> Right "false"
    And parts -> connective "true" "and" <$> traverse recurse parts
    Or parts -> connective "false" "or" <$> traverse recurse parts
    Not inner -> application "not" . pure <$> recurse inner
    Atom relation left right -> application (relationText relation) <$> traverse (term context locals) [left, right]
    Predicate name arguments -> application (symbol "f" [nameText name]) <$> traverse (term context locals) arguments
    Forall bound inner -> quantified "forall" bound inner
    Exists bound inner -> quantified "exists" bound inner
  where
    recurse = formula context locals
    quantified _ [] inner = recurse inner
    quantified quantifier bound inner = do
        binders <- traverse (binder context) bound
        body <- formula context (Set.fromList (map fst bound) <> locals) inner
        pure ("(" <> quantifier <> " (" <> Text.unwords binders <> ") " <> body <> ")")

-- | A term. A free value that takes arguments needs a function sort.
term :: Context -> Set Name -> Term -> Either SmtLibError Text
term context locals current = case current of
    Lit literal
        | literal < 0 -> Right ("(- " <> decimal (negate literal) <> ")")
        | otherwise -> Right (decimal literal)
    Var name -> Right (named name)
    App name [] -> Right (named name)
    App name arguments -> do
        let global = name `Set.member` contextConstructors context || name `Set.member` contextDefinitions context
        unless (global || takes (length arguments) (Map.lookup name (contextValues context))) $
            Left (UnsupportedTerm current)
        application (named name) <$> traverse recurse arguments
    Neg inner -> application "-" . pure <$> recurse inner
    Add left right -> binary "+" left right
    Sub left right -> binary "-" left right
    Mul left right -> binary "*" left right
    Div left right -> binary "div" left right
    Mod left right -> binary "mod" left right
    Ite condition yes no -> do
        test <- formula context locals condition
        branches <- traverse recurse [yes, no]
        pure (application "ite" (test : branches))
    Cast _ _ -> Left (UnsupportedTerm current)
  where
    recurse = term context locals
    binary operator left right = application operator <$> traverse recurse [left, right]
    named name
        | name `Set.member` locals = symbol "b" [nameText name]
        | name `Set.member` contextConstructors context = symbol "c" [nameText name]
        | name `Set.member` contextDefinitions context = symbol "f" [nameText name]
        | otherwise = symbol "v" [nameText name]
    takes count (Just (FunctionSort parameters _)) = length parameters == count
    takes _ _ = False

-- | A quoted symbol of a kind, from the parts of a name.
symbol :: Text -> [Text] -> Text
symbol kind parts = "|" <> Text.intercalate ":" (kind : map escape parts) <> "|"
  where
    escape = Text.concatMap $ \character ->
        if character `elem` ("%|\\:" :: String) || character < ' ' || character > '~'
            then "%" <> decimal (ord character) <> ";"
            else Text.singleton character

-- | The text of a name.
nameText :: Name -> Text
nameText (Name text) = text

-- | Apply an SMT-LIB function. A constant has no parentheses.
application :: Text -> [Text] -> Text
application function [] = function
application function arguments = "(" <> Text.unwords (function : arguments) <> ")"

-- | Join formulas with a connective, or give its unit for no formulas.
connective :: Text -> Text -> [Text] -> Text
connective unit _ [] = unit
connective _ _ [part] = part
connective _ operator parts = application operator parts

-- | The SMT-LIB function of a comparison.
relationText :: Relation -> Text
relationText relation = case relation of
    Eq -> "="
    Ne -> "distinct"
    Gt -> ">"
    Ge -> ">="
    Lt -> "<"
    Le -> "<="

-- | Show an integer.
decimal :: (Show a) => a -> Text
decimal = Text.pack . show
