{-# LANGUAGE OverloadedStrings #-}

{- | Type-directed component synthesis on equality-constrained automata.

This is Hectare, the synthesizer of Koppel, Guo, de Vries, Solar-Lezama, and
Polikarpova, /Searching Entangled Program Spaces/ (ICFP 2022), on the engine
of microcfta. A query gives typed arguments and a goal type. The synthesizer
builds one automaton of the well-typed programs of a size that apply library
components and use every argument, keeps the programs of the goal type,
reduces the automaton, and lists its programs.

The encoding follows the paper. A type is a term: a type constructor with
its arguments as children, and a function type as the symbol @->@ with an
arrow marker and the argument and result types. A program term has its type
as its first child. A component has its type as its only child: each type
variable of a component becomes the node of all types, and equality
constraints tie its occurrences, so that each use of the component chooses
its own instance. An application has four children: the result type, the
arrow marker, the function, and the argument, and three equalities say that
the function has an arrow type from the type of the argument to the result
type. The type variables of a query are rigid: they are leaves that only the
node of all types and the query's own arguments contain.

Components of the same type form one group, and the automaton has one symbol
for each group, its representative. A program of representatives stands for
every program that replaces each representative by a member of its group
('expand').

'programsOfSize' reads the reduced automaton as a generator: the
well-typed programs of a size get exact counts, ranks, uniform sampling,
and shrinking. A type variable that the goal does not fix keeps the node of
all types, so a program can have many typed terms, and the import cannot
count them. 'programsOfSizeUpToDepth' bounds the typed terms by a depth.
-}
module Data.CFTA.Gen.Synthesis (
    -- * Types
    Type (..),
    (~>),
    typeVariables,
    parseType,
    typeParser,
    renderType,

    -- * Libraries and queries
    Library (..),
    library,
    Query (..),

    -- * Programs
    Program (..),
    parseProgram,
    renderProgram,
    expand,
    representative,

    -- * Search
    typeNode,
    rawSearchSpace,
    reduceFully,
    reductionRounds,
    searchSpace,
    programsIn,
    solutionsOfSize,
    distinctSolutionsOfSize,
    synthesize,

    -- * Generators
    programsOfSize,
    programsOfSizeUpToDepth,
) where

import Control.Monad (guard)
import Data.Bifunctor (first)
import Data.Char (isAlphaNum, isLower, isSpace, isUpper)
import Data.Containers.ListUtils (nubOrd)
import Data.Hashable (Hashable)
import Data.List (intercalate, permutations, subsequences)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Generics (Generic)
import Text.ParserCombinators.ReadP (
    ReadP,
    between,
    char,
    choice,
    many,
    many1,
    munch,
    munch1,
    option,
    satisfy,
    sepBy1,
    (+++),
    (<++),
 )

import Data.CFTA.Equality
import Data.CFTA.Gen.Equality (ECTAGen)
import qualified Data.CFTA.Gen.Equality as ECTAGen
import Data.CFTA.Gen.Synthesis.Internal.Syntax (lexeme, parseWhole, token)
import Data.CFTA.Index (Depth)
import Data.CFTA.Symbol (Symbol (Symbol), symbolText)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- Types

{- | A type: a type variable, a function type, or a type constructor with its
arguments. The constructor @Fun@ with two arguments is a function type too.
-}
data Type
    = TVar Text
    | TFun Type Type
    | TCons Text [Type]
    deriving (Eq, Ord, Show, Read, Generic)

instance Hashable Type

infixr 1 ~>

-- | The function type from the first type to the second.
(~>) :: Type -> Type -> Type
(~>) = TFun

-- | The type variables of a type, each once, in order of occurrence.
typeVariables :: Type -> [Text]
typeVariables = nubOrd . go
  where
    go (TVar name) = [name]
    go (TFun argument result) = go argument <> go result
    go (TCons _ arguments) = concatMap go arguments

{- | Parse a type in Haskell syntax. A lowercase name is a type variable. A
capitalized name with its arguments is a type constructor, as in
@Either a b@. The type @[t]@ is the constructor @List@, @(a, b)@ is @Pair@,
and @()@ is @Unit@. The arrow @->@ is a function type, and it associates to
the right. A class constraint uses the encoding of Hoogle+: @Eq a => t@ is
the function type from the dictionary @\@\@hplusTC\@\@Eq a@ to @t@, and
@(Eq a, Show b) => t@ takes the dictionaries in the written order. A name
can contain \@, so that a dictionary can be a type of its own.
-}
parseType :: Text -> Either String Type
parseType = parseWhole "type" typeParser

{- | The parser of 'parseType', for the parsers of larger syntax, such as the
refinement types of "Data.CFTA.Gen.Synthesis.Liquid".
-}
typeParser :: ReadP Type
typeParser = constrained +++ function
  where
    constrained = do
        dictionaries <- context <* token "=>"
        (\body -> foldr TFun body dictionaries) <$> typeParser
    context = (pure <$> constraint) +++ between (token "(") (token ")") (sepBy1 constraint (token ","))
    constraint = TCons . (classPrefix <>) <$> constructorName <*> many atomic
    function = do
        argument <- applied
        option argument (TFun argument <$> (token "->" *> typeParser))
    applied = (TCons <$> constructorName <*> many1 atomic) +++ atomic
    atomic =
        choice
            [ TVar <$> name isLower
            , (`TCons` []) <$> constructorName
            , TCons "Unit" [] <$ (token "(" *> token ")")
            , (\element -> TCons "List" [element]) <$> between (token "[") (token "]") typeParser
            , between (token "(") (token ")") $ do
                firstType <- typeParser
                option firstType ((\secondType -> TCons "Pair" [firstType, secondType]) <$> (token "," *> typeParser))
            ]
    constructorName = name (\c -> isUpper c || c == '@')
    name isStart = lexeme $ Text.pack <$> ((:) <$> satisfy isStart <*> munch isNameCharacter)
    isNameCharacter c = isAlphaNum c || c `elem` ("_'@" :: String)

{- | A type in the syntax of 'parseType'. 'parseType' reads the result back
to the same type when each name is valid in that syntax.
-}
renderType :: Type -> String
renderType = go 0
  where
    -- The precedence is 0 for any type, 1 for the argument of a function
    -- type, and 2 for the argument of a type constructor.
    go :: Int -> Type -> String
    go precedence typ = case typ of
        TVar name -> Text.unpack name
        TCons "List" [element] -> "[" <> go 0 element <> "]"
        TCons "Pair" [firstType, secondType] -> "(" <> go 0 firstType <> ", " <> go 0 secondType <> ")"
        TCons "Unit" [] -> "()"
        TCons name [] -> Text.unpack name
        TCons name arguments -> parenthesize (precedence > 1) $ applied name arguments
        TFun argument result -> parenthesize (precedence > 0) $ case constraints typ of
            ([], _) -> go 1 argument <> " -> " <> go 0 result
            ([constraint], body) -> constraint <> " => " <> go 0 body
            (several, body) -> "(" <> intercalate ", " several <> ") => " <> go 0 body
    applied name arguments = unwords (Text.unpack name : map (go 2) arguments)
    -- The class constraints at the start of a type, and the rest of the type.
    constraints (TFun (TCons name arguments) result)
        | Just className <- Text.stripPrefix classPrefix name =
            first (applied className arguments :) (constraints result)
    constraints typ = ([], typ)
    parenthesize True text = "(" <> text <> ")"
    parenthesize False text = text

-- | The prefix of the type constructor of a class dictionary in Hoogle+.
classPrefix :: Text
classPrefix = "@@hplusTC@@"

-- Libraries and queries

-- | A component library, grouped by type.
data Library = Library
    { libraryGroups :: [(Text, Type, [Text])]
    -- ^ Each group: its representative, the type, and its members in source order.
    , libraryArgumentOnly :: [(Text, Type)]
    -- ^ Components that only appear as an argument, such as @($)@ and @id@.
    , libraryAvoid :: [([Text], Maybe [Text])]
    {- ^ Pruning rules for terms of size two: a function of the first list is
    not applied to a component of the second list, such as @head@ to @Nil@.
    With 'Nothing', the functions head no term of size two.
    -}
    }
    deriving (Show)

{- | The library of the components, with the components that only appear as
an argument and the pruning rules. Components of one type form one group,
whose representative is @f@ and its index; a pruning rule names members, and
it applies to their groups.
-}
library :: [(Text, Type)] -> [(Text, Type)] -> [([Text], Maybe [Text])] -> Library
library components argumentOnly avoid =
    Library
        { libraryGroups = [(representativeOf index, typ, members) | (index, (typ, members)) <- zip [0 :: Int ..] groups]
        , libraryArgumentOnly = argumentOnly
        , libraryAvoid = [(map toRepresentative functions, map toRepresentative <$> arguments) | (functions, arguments) <- avoid]
        }
  where
    groups = foldr addMember [] (reverse components)
    addMember (name, typ) found = case break ((== typ) . fst) found of
        (before, (_, members) : after) -> before <> ((typ, members <> [name]) : after)
        (before, []) -> before <> [(typ, [name])]
    representativeOf index = "f" <> Text.pack (show index)
    toRepresentative name = fromMaybe name $ Map.lookup name memberToRepresentative
    memberToRepresentative =
        Map.fromList [(member, representativeOf index) | (index, (_, members)) <- zip [0 :: Int ..] groups, member <- members]

-- | A query: the arguments with their types, and the goal type.
data Query = Query
    { queryArguments :: [(Text, Type)]
    , queryGoal :: Type
    }
    deriving (Eq, Show)

-- Programs

-- | A program: a component or an argument, or an application.
data Program
    = Var Text
    | App Program Program
    deriving (Eq, Ord, Show, Read)

-- | A program in Haskell syntax, as in @map f xs@.
renderProgram :: Program -> String
renderProgram = go False
  where
    go _ (Var name) = Text.unpack name
    go nested (App function argument) =
        (if nested then \text -> "(" <> text <> ")" else id) $
            goFunction function <> " " <> go True argument
    goFunction (Var name) = Text.unpack name
    goFunction applied = go False applied

{- | Parse a program in Haskell syntax: names and their applications, as in
@map f (filter p xs)@. Application associates to the left. A name is a run
of characters without spaces and parentheses, such as
@Data.Maybe.fromMaybe@ or @$@. An operator in parentheses is part of a
name, as in @(Data.Bool.&&)@, and the name can continue after the
parenthesis, as in @(Data.Eq.\/=)_Ord@. Other parentheses group.
'parseProgram' reads the result of 'renderProgram' back to the same program.
-}
parseProgram :: Text -> Either String Program
parseProgram = parseWhole "program" programParser

-- | The parser of 'parseProgram'.
programParser :: ReadP Program
programParser = foldl1 App <$> many1 (lexeme atom)
  where
    atom = (Var . Text.pack <$> name) <++ between (char '(') (lexeme (char ')')) programParser
    name = ((<>) <$> parenthesizedOperator <*> munch nameCharacter) +++ munch1 nameCharacter
    parenthesizedOperator = do
        operator <- between (char '(') (char ')') (munch1 nameCharacter)
        guard $ not $ isAlphaNum (last operator) || last operator `elem` ("_'" :: String)
        pure ("(" <> operator <> ")")
    nameCharacter c = not (isSpace c) && c `notElem` ("()" :: String)

-- | Every program that replaces each representative by a member of its group.
expand :: Library -> Program -> [Program]
expand lib = go
  where
    members = Map.fromList [(representativeName, names) | (representativeName, _, names) <- libraryGroups lib]
    go (Var name) = map Var $ fromMaybe [name] $ Map.lookup name members
    go (App function argument) = App <$> go function <*> go argument

-- | The program with each component replaced by the representative of its group.
representative :: Library -> Program -> Program
representative lib = go
  where
    toRepresentative =
        Map.fromList [(member, representativeName) | (representativeName, _, members) <- libraryGroups lib, member <- members]
    go (Var name) = Var $ fromMaybe name $ Map.lookup name toRepresentative
    go (App function argument) = App (go function) (go argument)

-- The encoding

-- | The marker that is the first child of a function type.
arrowMarker :: Node Symbol
arrowMarker = Node [Edge "(->)" []]

-- | The node of a function type.
arrowType :: Node Symbol -> Node Symbol -> Node Symbol
arrowType argument result = Node [Edge "->" [arrowMarker, argument, result]]

{- | The node of a type, with each type variable a rigid leaf. A component
type replaces these leaves by the node of all types ('generalize').
-}
typeNode :: Type -> Node Symbol
typeNode (TVar name) = Node [Edge (variableSymbol name) []]
typeNode (TFun argument result) = arrowType (typeNode argument) (typeNode result)
typeNode (TCons "Fun" [argument, result]) = arrowType (typeNode argument) (typeNode result)
typeNode (TCons name arguments) = Node [Edge (Symbol name) (map typeNode arguments)]

{- | The symbol of a type variable. The paper names the first four variables
@var1@ to @var4@, and the node of all types contains these four.
-}
variableSymbol :: Text -> Symbol
variableSymbol name = Symbol $ fromMaybe ("var_" <> name) $ lookup name [("a", "var1"), ("b", "var2"), ("c", "var3"), ("d", "var4")]

-- | Whether a node is the leaf of a type variable.
isVariable :: Node Symbol -> Bool
isVariable (Node [Edge (Symbol name) []]) = name `elem` ["var1", "var2", "var3", "var4"] || "var_" `Text.isPrefixOf` name
isVariable _ = False

{- | The node of all types: the function types, the four type variables, and
the type constructors of the library and the query with their arities.
-}
allTypes :: [(Text, Int)] -> Node Symbol
allTypes constructors =
    createMu $ \types ->
        union $
            [arrowType types types]
                <> map (\name -> Node [Edge name []]) ["var1", "var2", "var3", "var4"]
                <> [Node [Edge (Symbol name) (replicate arity types)] | (name, arity) <- constructors]

-- | The type constructors of a type with their arities.
constructorsOf :: Type -> [(Text, Int)]
constructorsOf (TVar _) = []
constructorsOf (TFun argument result) = constructorsOf argument <> constructorsOf result
constructorsOf (TCons name arguments) = [(name, length arguments) | name /= "Fun"] <> concatMap constructorsOf arguments

{- | A component type with each type variable replaced by the node of all
types, and equality constraints that tie the occurrences of each variable.
-}
generalize :: Node Symbol -> Node Symbol -> Node Symbol
generalize types typ@(Node [Edge symbol _]) = case mapNodes (\node -> if isVariable node then types else node) typ of
    Node [Edge _ children] -> Node [mkEdge symbol children (equalityConstraint $ mkEqConstraints $ map pathsOf variables)]
    other -> other
  where
    variables = nubOrd $ crush (\node -> [node | isVariable node]) typ
    pathsOf variable = pathsMatching (== variable) typ
generalize _ typ = typ

-- | The application of a function term to an argument term.
application :: Node Symbol -> Node Symbol -> Node Symbol -> Node Symbol
application types function argument =
    Node
        [ mkEdge
            "app"
            [types, arrowMarker, function, argument]
            ( equalityConstraint $
                mkEqConstraints
                    [ [path [1], path [2, 0, 0]]
                    , [path [3, 0], path [2, 0, 1]]
                    , [path [0], path [2, 0, 2]]
                    ]
            )
        ]

-- | Keep the terms of a node whose type child equals the goal type.
ofType :: Node Symbol -> Node Symbol -> Node Symbol
ofType candidates goal =
    Node [mkEdge "filter" [goal, candidates] (equalityConstraint $ mkEqConstraints [[path [0], path [1, 0]]])]

{- | Propagate the constraints and remove the redundant edges until nothing
changes, for at most 'reductionRounds' rounds, as the paper does. At some
sizes the rounds do not converge: on takeNdropM at size 7 the automaton
stays near 3,400 nodes, and the enumeration of the bounded result finds the
solution. Reduction does not change the language, so the bound only stops
earlier.
-}
reduceFully :: Node Symbol -> Node Symbol
reduceFully = go reductionRounds
  where
    go 0 node = node
    go rounds node
        | next == node = node
        | otherwise = go (rounds - 1) next
      where
        next = withoutRedundantEdges (reducePartially node)

-- | The bound of 'reduceFully' on reduction rounds: 30, as in the paper.
reductionRounds :: Int
reductionRounds = 30

{- | The automaton of the programs of a size that use every argument of the
query once and have the goal type, reduced and refolded. A size counts the
components and arguments of a program.
-}
searchSpace :: Library -> Query -> Int -> Node Symbol
searchSpace lib query = refold . reduceFully . rawSearchSpace lib query

-- | The automaton of 'searchSpace' before the reduction.
rawSearchSpace :: Library -> Query -> Int -> Node Symbol
rawSearchSpace lib query size = ofType (relevantOfSize size) (typeNode $ queryGoal query)
  where
    types =
        allTypes
            $ nubOrd
            $ concatMap (\(_, typ, _) -> constructorsOf typ) (libraryGroups lib)
                <> concatMap (constructorsOf . snd) (libraryArgumentOnly lib)
                <> concatMap (constructorsOf . snd) (queryArguments query)
                <> constructorsOf (queryGoal query)
    component name typ = Edge (Symbol name) [generalize types (typeNode typ)]
    components = [(name, component name typ) | (name, typ, _) <- libraryGroups lib]
    anyFunction = Node (map snd components)
    argumentOnly = Node [component name typ | (name, typ) <- libraryArgumentOnly lib]
    argumentEdges = [(name, Edge (Symbol name) [typeNode typ]) | (name, typ) <- queryArguments query]
    anyArgument = Node (map snd argumentEdges)
    without names = Node [edge | (name, edge) <- components, name `notElem` names]
    restricted = concatMap fst (libraryAvoid lib)

    -- The terms of a size that use no argument in particular; the flag
    -- admits the components that only appear as an argument. The table
    -- builds the terms of each flag and size once.
    termsOfSize :: Bool -> Int -> [Node Symbol]
    termsOfSize asArgument size' = termsTable Map.! (asArgument, size')
    termsTable =
        LazyMap.fromList
            [((asArgument, size'), buildTerms asArgument size') | asArgument <- [False, True], size' <- [0 .. size]]
    buildTerms _ 0 = []
    buildTerms asArgument 1 = [anyArgument, anyFunction] <> [argumentOnly | asArgument]
    buildTerms _ 2 =
        [ application
            types
            (Node [edge | (name, edge) <- components, name `elem` functions])
            (union [without arguments, anyArgument, argumentOnly])
        | (functions, Just arguments) <- libraryAvoid lib
        ]
            <> [application types (union [without restricted, anyArgument]) (union $ termsOfSize True 1)]
    buildTerms _ size' =
        [ application types (union $ termsOfSize False left) (union $ termsOfSize True (size' - left))
        | left <- [1 .. size' - 1]
        ]

    -- The terms of a size that use each of the arguments once. The
    -- arguments are an ordered selection of the query's arguments, and the
    -- table builds the terms of each flag, size, and selection once.
    relevant :: Bool -> Int -> [(Text, Edge Symbol)] -> [Node Symbol]
    relevant asArgument size' arguments = relevantTable Map.! (asArgument, size', map fst arguments)
    relevantTable =
        LazyMap.fromList
            [ ((asArgument, size', map fst arguments), buildRelevant asArgument size' arguments)
            | asArgument <- [False, True]
            , size' <- [0 .. size]
            , arguments <- concatMap permutations (subsequences argumentEdges)
            ]
    buildRelevant asArgument size' [] = termsOfSize asArgument size'
    buildRelevant _ 1 [(_, edge)] = [Node [edge]]
    buildRelevant _ size' arguments
        | size' < length arguments = []
        | otherwise =
            [ application types (union $ relevant False left used) (union $ relevant True (size' - left) rest)
            | left <- [1 .. size' - 1]
            , (used, rest) <- map (`splitAt` arguments) [0 .. length arguments]
            ]

    relevantOfSize size' = union $ concatMap (relevant True size') (permutations argumentEdges)

-- | The programs of a term of the search space: the types go.
toProgram :: Term Symbol -> Program
toProgram term = case (Term.rootLabel term, Term.subForest term) of
    ("app", children@(_ : _ : _)) -> App (toProgram $ children !! (length children - 2)) (toProgram $ last children)
    ("filter", children@(_ : _)) -> toProgram $ last children
    (symbol, _) -> Var (symbolText symbol)

-- | The programs of an automaton of the search space, in enumeration order.
programsIn :: Node Symbol -> [Program]
programsIn = map toProgram . terms

-- | The programs of a size that solve the query, with representatives.
solutionsOfSize :: Library -> Query -> Int -> [Program]
solutionsOfSize lib query = programsIn . searchSpace lib query

{- | The programs of a size that solve the query, each once, in the order in
which 'solutionsOfSize' first lists them. 'solutionsOfSize' keeps a set of
the typed terms, and a large size has millions of them; this lists the runs
of the search space and keeps a set of the programs only, which needs much
less memory.
-}
distinctSolutionsOfSize :: Library -> Query -> Int -> [Program]
distinctSolutionsOfSize lib query = nubOrd . map (toProgram . fst) . runs "Mu" . searchSpace lib query

-- | The programs up to a size that solve the query, smallest first.
synthesize :: Library -> Query -> Int -> [Program]
synthesize lib query bound = concatMap (solutionsOfSize lib query) [1 .. bound]

{- | The programs of a size that solve the query, as a generator: an exact
count, a rank for each typed program, sampling, and shrinking. Two typed
terms with the same program are two ranks.

The import counts a recursive automaton only when no edge has a constraint.
A type variable can take any type, so the search space of a polymorphic
query keeps the recursive node of all types under constrained edges, and the
generator gives 'Data.CFTA.Gen.Error.CannotCountConstrainedEdges'. Then use
'programsOfSizeUpToDepth'.
-}
programsOfSize :: Library -> Query -> Int -> ECTAGen Program
programsOfSize lib query size = toProgram <$> ECTAGen.fromAutomaton (searchSpace lib query size)

{- | The programs of a size whose typed terms have at most a depth, as a
generator. The depth bounds the types that the type variables take, so the
count is exact for that bound.
-}
programsOfSizeUpToDepth :: Depth -> Library -> Query -> Int -> ECTAGen Program
programsOfSizeUpToDepth depth lib query size = toProgram <$> ECTAGen.fromAutomatonUpToDepth depth (searchSpace lib query size)
