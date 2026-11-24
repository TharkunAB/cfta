{- | Datatypes and structurally recursive definitions in the formula language.

A 'Theory' declares datatypes and defines functions and predicates. Every
solver reads the same theory. 'theoryInterpretations' gives ground evaluation
("Data.CFTA.Refinement.Ground") the meanings of the names, and
"Data.CFTA.Refinement.SmtLib" writes the theory as SMT-LIB commands.

A datatype gives one named sort its constructors, and each constructor its
typed fields. An application of a constructor is an 'App' of its name, and
the constructors are free. Version 1 declares each datatype for one concrete
sort, such as @List(int)@, and has no sort parameters.

A definition has typed parameters and a body. The body of a function is a
term of its result sort. The body of a predicate is a formula. A body can
also split on a parameter or on a field that an earlier split binds: one
branch for each constructor, which binds the fields of that constructor.

'theory' checks these rules:

1. Constructor and definition names are distinct. A name that a definition
   binds (a parameter, a field of a split, or a quantifier binder) is not a
   global name and does not hide a name that is already bound.
2. Fields, parameters, and results have the sort 'IntSort' or the sort of a
   declared datatype. Ground values have no other sorts.
3. Each body has no free names and has the sort of its definition.
4. A definition calls itself only with a smaller argument in one fixed
   parameter position: a field that a split of that parameter binds,
   directly or through splits of its fields (structural recursion). It calls
   other definitions only when they come earlier in the theory, so the
   definitions have no cycles.

Thus each application of a definition to values stops. A datatype can have no
value, for example when each constructor has a field of its own sort.
'inhabitedDatatypes' finds the datatypes that have a value.

'predicateDefinitions' gives the predicates without a split as predicate
definitions ("Data.CFTA.Refinement.Definition"), so that a solver without
recursive definitions, such as the Z3 entailment through Liquid Fixpoint,
can unfold them.

Division and remainder need a positive divisor in ground evaluation, so a
division by zero or by a negative number is unknown there. The SMT-LIB text
("Data.CFTA.Refinement.SmtLib") leaves division by zero to the solver, and
Z3 does not specify it. A query that divides by zero can thus get 'No' from
Z3 and 'Unknown' from ground evaluation.
-}
module Data.CFTA.Refinement.Theory (
    Theory,
    theoryDatatypes,
    theoryDefinitions,
    Datatype (..),
    Constructor (..),
    TheoryDefinition (..),
    Body (..),
    Branch (..),
    TheoryError (..),
    theory,
    emptyTheory,
    theoryDeclarations,
    inhabitedDatatypes,
    theoryInterpretations,
    predicateDefinitions,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, forM_, guard, unless, when)
import Data.Bifunctor (first)
import Data.Foldable (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.CFTA.Formula (Formula (..), Name, Relation (Eq), Sort (..), Term (..), freeNames)
import Data.CFTA.Refinement.Definition (Definition (..), DefinitionError, Definitions, checkFormula, termSort)
import Data.CFTA.Refinement.Ground (Interpretations (..), Value (..), formulaValue, termValue)

-- | A datatype: a named sort and its constructors.
data Datatype = Datatype
    { datatypeSort :: !Sort
    , datatypeConstructors :: ![Constructor]
    }
    deriving (Eq, Show, Read)

-- | A constructor and its fields, with their sorts.
data Constructor = Constructor
    { constructorName :: !Name
    , constructorFields :: ![(Name, Sort)]
    }
    deriving (Eq, Show, Read)

{- | A function with its parameters, result sort, and body, or a predicate
with its parameters and body.
-}
data TheoryDefinition
    = FunctionDefinition ![(Name, Sort)] !Sort !(Body Term)
    | PredicateDefinition ![(Name, Sort)] !(Body Formula)
    deriving (Eq, Show, Read)

-- | A body: a term or a formula, or a case split on a parameter or a field.
data Body a
    = Expression !a
    | Split !Name ![Branch a]
    deriving (Eq, Show, Read)

-- | One branch of a split: a constructor, names for its fields, and the body of the branch.
data Branch a = Branch
    { branchConstructor :: !Name
    , branchFields :: ![Name]
    , branchBody :: !(Body a)
    }
    deriving (Eq, Show, Read)

-- | A theory that 'theory' accepts. The definitions keep their order.
data Theory = Theory
    { theoryDatatypes :: ![Datatype]
    , theoryDefinitions :: ![(Name, TheoryDefinition)]
    }
    deriving (Eq, Show)

-- | Why 'theory' rejects a theory.
data TheoryError
    = -- | The sort of a datatype is not a named sort.
      NotNamedSort !Sort
    | -- | Two datatypes have the same sort.
      DuplicateDatatype !Sort
    | -- | A constructor or a definition has the name of another one.
      DuplicateName !Name
    | -- | A constructor has two fields with the same name.
      DuplicateField !Name !Name
    | -- | A field, parameter, or result has a sort that is not an integer or a datatype: the owner, then the sort.
      UnsupportedSort !Name !Sort
    | -- | A definition binds a global name or a name that is already bound: the definition, then the name.
      HiddenName !Name !Name
    | -- | A body has a free name: the definition, then the name.
      UnboundName !Name !Name
    | -- | The parts of a body do not fit together.
      IllSortedBody !Name !DefinitionError
    | -- | The body of a function has a sort that is not its result sort: the function, the result sort, and the body sort.
      ResultSort !Name !Sort !Sort
    | -- | A split is not on a parameter or field of a datatype sort: the definition, then the name.
      NotSplittable !Name !Name
    | -- | The branches of a split do not name each constructor once, with one name for each field.
      BadBranches !Name !Name
    | {- | A definition calls a definition that does not come earlier: the
      caller, then the callee. This also rejects each cycle of calls, because
      a definition in a cycle calls a later one.
      -}
      ForwardCall !Name !Name
    | -- | No parameter position gets a smaller argument in every call of a definition to itself.
      NotStructural !Name
    deriving (Eq, Show)

-- | Check datatypes and definitions, in their order, and make a theory.
theory :: [Datatype] -> [(Name, TheoryDefinition)] -> Either TheoryError Theory
theory datatypes definitions = do
    forM_ datatypes $ \datatype -> case datatypeSort datatype of
        NamedSort _ _ -> pure ()
        sort -> Left (NotNamedSort sort)
    firstDuplicate DuplicateDatatype (map datatypeSort datatypes)
    firstDuplicate DuplicateName (map constructorName constructorList <> map fst definitions)
    forM_ constructorList $ \(Constructor name fields) -> do
        firstDuplicate (DuplicateField name) (map fst fields)
        mapM_ (supported name . snd) fields
    mapM_ checkDefinition (zip [0 ..] definitions)
    pure (Theory datatypes definitions)
  where
    constructorList = concatMap datatypeConstructors datatypes
    constructors = Map.fromList [(constructorName c, c) | c <- constructorList]
    datatypeSorts = Set.fromList (map datatypeSort datatypes)
    globalSorts = Map.fromList (declarations datatypes definitions)
    globalNames = Map.keysSet constructors <> Set.fromList (map fst definitions)
    signatures = Map.fromList [(name, map snd parameters) | (name, PredicateDefinition parameters _) <- definitions]
    order = Map.fromList (zip (map fst definitions) [0 :: Int ..])

    supported owner sort = unless (sort == IntSort || sort `Set.member` datatypeSorts) $ Left (UnsupportedSort owner sort)

    checkDefinition (index, (name, definition)) = do
        calls <- case definition of
            FunctionDefinition parameters result body -> do
                supported name result
                checkBody parameters body $ \scope term -> do
                    calls <- checkLeaf scope (termParts term) (freeNames (Atom Eq term term))
                    sort <- first (IllSortedBody name) (termSort signatures (globalSorts <> scope) term)
                    unless (sort == result) $ Left (ResultSort name result sort)
                    pure calls
            PredicateDefinition parameters body ->
                checkBody parameters body $ \scope formula -> do
                    calls <- checkLeaf scope (formulaParts formula) (freeNames formula)
                    first (IllSortedBody name) (checkFormula signatures (globalSorts <> scope) formula)
                    pure calls
        forM_ calls $ \(callee, _, _) -> case Map.lookup callee order of
            Just other | other > index -> Left (ForwardCall name callee)
            _ -> pure ()
        case [decreasing arguments origins | (callee, arguments, origins) <- calls, callee == name] of
            [] -> pure ()
            positions -> when (Set.null (foldr1 Set.intersection positions)) $ Left (NotStructural name)
      where
        -- Check the parameters and the splits. Give each call with the origins of the fields at its place.
        checkBody ::
            [(Name, Sort)] ->
            Body a ->
            (Map Name Sort -> a -> Either TheoryError [(Name, [Term])]) ->
            Either TheoryError [(Name, [Term], Map Name Int)]
        checkBody parameters body leaf = do
            mapM_ (supported name . snd) parameters
            scope <- foldM bind Map.empty parameters
            walk scope Map.empty body
          where
            positions = Map.fromList (zip (map fst parameters) [0 ..])
            walk scope origins current = case current of
                Expression expression -> map (\(callee, arguments) -> (callee, arguments, origins)) <$> leaf scope expression
                Split scrutinee branches -> do
                    let datatype = Map.lookup scrutinee scope >>= \sort -> find ((== sort) . datatypeSort) datatypes
                    expected <- maybe (Left (NotSplittable name scrutinee)) (Right . datatypeConstructors) datatype
                    let shape = Set.fromList [(constructorName c, length (constructorFields c)) | c <- expected]
                        given = [(branchConstructor b, length (branchFields b)) | b <- branches]
                    unless (Set.fromList given == shape && length given == length expected) $ Left (BadBranches name scrutinee)
                    let root = Map.lookup scrutinee positions <|> Map.lookup scrutinee origins
                    fmap concat $ forM branches $ \(Branch constructor fields inner) -> do
                        let sorts = map snd (constructorFields (constructors Map.! constructor))
                        inside <- foldM bind scope (zip fields sorts)
                        walk inside (maybe origins (\position -> Map.fromList [(field, position) | field <- fields] <> origins) root) inner

        bind scope (binder, sort)
            | binder `Map.member` scope || binder `Set.member` globalNames = Left (HiddenName name binder)
            | otherwise = Right (Map.insert binder sort scope)

        -- A leaf has no free names, and its quantifiers do not hide a bound or global name.
        checkLeaf scope (calls, binders) free = do
            forM_ free $ \used ->
                unless (used `Map.member` scope || used `Map.member` globalSorts) $ Left (UnboundName name used)
            forM_ binders $ \binder ->
                when (binder `Map.member` scope || binder `Set.member` globalNames) $ Left (HiddenName name binder)
            pure calls

        -- The parameter positions where a call gets a field of a split of that parameter.
        decreasing arguments origins =
            Set.fromList
                [ position
                | (position, argument) <- zip [0 :: Int ..] arguments
                , Just field <- [nameOf argument]
                , Map.lookup field origins == Just position
                ]

    nameOf (Var field) = Just field
    nameOf (App field []) = Just field
    nameOf _ = Nothing

-- | Report the first value that occurs twice.
firstDuplicate :: (Ord a) => (a -> e) -> [a] -> Either e ()
firstDuplicate failure = go Set.empty
  where
    go _ [] = Right ()
    go seen (x : rest)
        | x `Set.member` seen = Left (failure x)
        | otherwise = go (Set.insert x seen) rest

{- | The applications in a formula with their arguments, and the names that
its quantifiers bind. A name is an application without arguments.
-}
formulaParts :: Formula -> ([(Name, [Term])], [Name])
formulaParts formula = case formula of
    Top -> mempty
    Bottom -> mempty
    And parts -> foldMap formulaParts parts
    Or parts -> foldMap formulaParts parts
    Not inner -> formulaParts inner
    Atom _ left right -> termParts left <> termParts right
    Forall bound inner -> ([], map fst bound) <> formulaParts inner
    Exists bound inner -> ([], map fst bound) <> formulaParts inner
    Predicate name arguments -> ([(name, arguments)], []) <> foldMap termParts arguments

-- | 'formulaParts' for a term.
termParts :: Term -> ([(Name, [Term])], [Name])
termParts term = case term of
    Lit _ -> mempty
    Var name -> ([(name, [])], [])
    App name arguments -> ([(name, arguments)], []) <> foldMap termParts arguments
    Neg inner -> termParts inner
    Add left right -> termParts left <> termParts right
    Sub left right -> termParts left <> termParts right
    Mul left right -> termParts left <> termParts right
    Div left right -> termParts left <> termParts right
    Mod left right -> termParts left <> termParts right
    Ite condition yes no -> formulaParts condition <> termParts yes <> termParts no
    Cast inner _ -> termParts inner

-- | The sorts of the constructors and functions. A name without parameters has its result sort.
declarations :: [Datatype] -> [(Name, TheoryDefinition)] -> [(Name, Sort)]
declarations datatypes definitions =
    [ (constructorName c, signature (map snd (constructorFields c)) (datatypeSort d))
    | d <- datatypes
    , c <- datatypeConstructors d
    ]
        <> [(name, signature (map snd parameters) result) | (name, FunctionDefinition parameters result _) <- definitions]
  where
    signature [] result = result
    signature arguments result = FunctionSort arguments result

-- | The theory without datatypes and definitions.
emptyTheory :: Theory
emptyTheory = Theory [] []

{- | The sorts of the constructors and functions of a theory, for the
declarations of an entailment. Predicates have no declaration.
-}
theoryDeclarations :: Theory -> [(Name, Sort)]
theoryDeclarations (Theory datatypes definitions) = declarations datatypes definitions

{- | The datatype sorts that have a value: the least set that contains a
sort when one of its constructors has only fields of integer sort or of a
sort in the set.
-}
inhabitedDatatypes :: Theory -> Set Sort
inhabitedDatatypes (Theory datatypes _) = go Set.empty
  where
    go known
        | next == known = known
        | otherwise = go next
      where
        next =
            Set.fromList
                [ datatypeSort datatype
                | datatype <- datatypes
                , any (all (has known . snd) . constructorFields) (datatypeConstructors datatype)
                ]
    has known sort = sort == IntSort || sort `Set.member` known

{- | The meanings of the constructors and definitions, for ground evaluation.
A constructor builds a 'DataValue'. A definition evaluates its body with its
arguments in place of its parameters. A split gives 'Nothing' for a value
that is not a constructor of the datatype.

Give 'theoryDeclarations' to the entailment as well, so that its sort check
knows the constructors and functions.
-}
theoryInterpretations :: Theory -> Interpretations
theoryInterpretations current@(Theory datatypes definitions) = interpretations
  where
    interpretations =
        Interpretations
            { interpretedFunctions =
                Map.fromList $
                    [(constructorName c, construct c) | d <- datatypes, c <- datatypeConstructors d]
                        <> [ (name, apply parameters (evaluate (termValue interpretations) body))
                           | (name, FunctionDefinition parameters _ body) <- definitions
                           ]
            , interpretedPredicates =
                Map.fromList
                    [ (name, (map snd parameters, apply parameters (evaluate (formulaValue interpretations) body)))
                    | (name, PredicateDefinition parameters body) <- definitions
                    ]
            , inhabitedSorts = inhabitedDatatypes current
            }
    construct (Constructor name fields) arguments = do
        guard (length arguments == length fields)
        Just (DataValue name arguments)
    apply parameters run arguments = do
        guard (length arguments == length parameters)
        run (Map.fromList (zip (map fst parameters) arguments))

{- | The predicates that unfold to formulas without the names of the theory,
as predicate definitions. Such a predicate has no split, so it does not call
itself: only a split binds a field. Its body applies no constructor and no
function of the theory, and only predicates of the result. The unfolding then
needs no other meaning from the theory, so it is exact for a solver without
datatypes. A solver that treats an unknown function as uninterpreted, such as
the Z3 entailment, would otherwise get a lowering that is not exact.
-}
predicateDefinitions :: Theory -> Definitions
predicateDefinitions (Theory datatypes definitions) = foldl add Map.empty definitions
  where
    globals = Set.fromList (map fst (declarations datatypes definitions) <> map fst definitions)
    add result (name, PredicateDefinition parameters (Expression body))
        | all (`Map.member` result) [callee | (callee, _) <- fst (formulaParts body), callee `Set.member` globals] =
            Map.insert name (Definition parameters body) result
    add result _ = result

-- | Evaluate a body with values for its parameters. A split binds the fields of the constructor of its value.
evaluate :: (Map Name Value -> a -> Maybe b) -> Body a -> Map Name Value -> Maybe b
evaluate leaf body values = case body of
    Expression expression -> leaf values expression
    Split scrutinee branches -> do
        DataValue constructor fields <- Map.lookup scrutinee values
        Branch _ names inner <- find ((== constructor) . branchConstructor) branches
        guard (length names == length fields)
        evaluate leaf inner (Map.fromList (zip names fields) <> values)
