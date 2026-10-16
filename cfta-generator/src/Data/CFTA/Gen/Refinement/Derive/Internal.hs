{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

{- | The level below "Data.CFTA.Gen.Refinement.Derive": the contracts and
the measures of the constructors of a datatype as annotations in the
expression language of "Data.CFTA.Refinement.Expression", by the
'Constructor' of each constructor, as 'Data.CFTA.Generic.datatypeConstructors'
gives it.

This module is exposed for integration: a translation that knows the
constructors and the measures only at run time builds annotations here. It is not part of the
PVP contract. A datatype with a 'Data.CFTA.Gen.Refinement.Derive.HasLTA'
instance needs none of it.

'deriveLTAWith' builds the generator that a person writes with the
combinators of "Data.CFTA.Gen.Refinement". A type with more than one
constructor is a 'oneof' of its constructors, in declaration order. A
constructor without fields is a 'leaf', and its measure, if any, is its
refinement. Another constructor is a 'measured' node when it has a measure,
a 'measuredBy' node when it has named measures, a 'guarded' node when it has
a contract, and a 'node' otherwise. An atomic field gets the generator that
'atom' gives for its type. So the ranks are the ranks of that hand-written
generator. Each member is the 'Term' of a value, as 'encodeTerm' gives it,
and the generator decodes it with 'decodeTerm'.

A conjunct of a contract that names only one atomic field is a condition on
that field, as 'satisfying' puts it where the field is drawn. So the bounds
of an 'every' field can be in the contract, and the generator still counts
them where the field is drawn.

The bound has the meaning of 'recurUpTo'. The types that refer to each other
form one group, and they unfold together: their recursive occurrences nest at
most the bound times. A type that is in no cycle does not use a level.
-}
module Data.CFTA.Gen.Refinement.Derive.Internal (
    -- * Annotations by constructor
    deriveLTAWith,
    deriveLTAOnWith,
    Annotation (..),
    Contract (..),
    Measure (..),
    contract,
    measure,
    measureNamed,
    fieldsContract,
    fieldsMeasure,
    fieldTerms,
    annotationFormulas,

    -- * Atomic fields
    Atoms (..),
    AtomicField (..),
    atom,
    atomicField,

    -- * Errors
    DeriveLTAError (..),
) where

import Control.Monad (unless, zipWithM)
import Data.Containers.ListUtils (nubOrd)
import Data.Graph (SCC (..), stronglyConnComp)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Proxy (Proxy (Proxy))
import qualified Data.Set as Set
import Data.String (fromString)
import Data.Typeable (TypeRep, typeRep)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Formula (Formula (And, Atom, Top), Relation (Eq), conjunction)
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Gen.Error (GenError (EmptyGenerator))
import Data.CFTA.Gen.Internal.Types (pattern Transparent)
import Data.CFTA.Gen.Refinement (LTAGen, guarded, leaf, measured, measuredBy, node, oneof, satisfying)
import Data.CFTA.Generic (Constructor (..), Description (..), Field (..), HasFTA (..))
import Data.CFTA.Index (ArgumentIndex (..), Arity (..), Depth)
import Data.CFTA.Refinement (contractTermName)
import Data.CFTA.Refinement.Expression (
    Expr,
    Literal (toLiteral),
    Refinement,
    freeNames,
    fromExpr,
    substitute,
    toExpr,
    uninterpreted,
    variable,
    (.&&),
    (.==),
 )
import Data.CFTA.Refinement.Guard (ContractBuilder (..), MeasureBuilder (..))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | Failure while deriving a refinement generator.
data DeriveLTAError
    = {- | Constructors with annotations or field atoms that the datatype does
      not reach, by name. The second field lists the names of the constructors
      that it reaches.
      -}
      UnknownConstructors ![String] ![String]
    | -- | An atomic field type that 'atom' gives no generator for.
      MissingAtom !TypeRep
    | {- | An annotation of a constructor takes a different number of terms than
      the constructor has fields. The fields are the constructor name, the
      number of fields, and the number of terms.
      -}
      AnnotationArityMismatch !String !Arity !Arity
    | -- | A constructor has more than one measure.
      SeveralMeasures !String
    | -- | A constructor without fields has a contract.
      ContractWithoutFields !String
    | {- | The node view of a 'Data.CFTA.Gen.Refinement.Derive.HasLTA' instance
      does not fit the datatype. The field gives the constructor, by the name of
      the datatype's constructor, and what differs.
      -}
      NodeMismatch !String !String
    | {- | The datatype reaches more types than the limit. A type that grows its
      argument on each recursion, such as @data T a = L a | N (T (a, a))@,
      reaches infinitely many types.
      -}
      TooManyTypes !Int
    | {- | A contract or a measure of a constructor reads a field whose type
      gives it no integer: the type has no atom, and no constructor of the
      type has a measure. Give the type an atom, as
      @atom \@Color (elements [Red, Black])@, or measures. The fields are the
      constructor name, the position of the field, and its type.
      -}
      UnmeasuredField !String !Int !TypeRep
    | -- | The automaton of 'deriveLTAOnWith' has a cycle.
      CyclicAutomaton
    | {- | A transition of the automaton of 'deriveLTAOnWith' has a constraint.
      The field is the name of its constructor.
      -}
      ConstrainedTransition !String
    | {- | A field atom has a generator of another type than its field. The
      fields are the constructor name, the position of the field, and the type
      of the generator.
      -}
      FieldAtomMismatch !String !Int !TypeRep
    | {- | A pool of 'Data.CFTA.Gen.Refinement.Derive.fieldAtoms' is for a term
      that is not one field of the node view. The field is the constructor
      name.
      -}
      FieldAtomTerm !String
    deriving (Eq, Show)

{- | Generators for atomic fields: by the type of the field ('atom'), and by
a constructor and the position of one of its fields
('Data.CFTA.Gen.Refinement.Derive.fieldAtoms'). A field atom applies before
the atom of the field's type.
-}
data Atoms = Atoms
    { byType :: !(Map.Map TypeRep AtomicField)
    , byField :: !(Map.Map (Constructor, Int) (TypeRep, AtomicField))
    -- ^ The type of the generator, and the generator.
    , atomProblems :: ![DeriveLTAError]
    -- ^ The errors of field atoms that do not fit, which a derivation reports.
    }

-- | The generator of one atomic type, and the integer of a term of that type.
data AtomicField = AtomicField
    { atomGenerator :: LTAGen (Term Constructor)
    , atomInteger :: Term Constructor -> Maybe Integer
    }

-- | When two generators are for one type, or for one field, the rightmost one applies.
instance Semigroup Atoms where
    Atoms types fields problems <> Atoms types' fields' problems' =
        Atoms (Map.union types' types) (Map.union fields' fields) (problems <> problems')

instance Monoid Atoms where
    mempty = Atoms Map.empty Map.empty []

{- | The generator of each field of a type, as in @atom \@Integer every@.

The value of an atomic field stands for one integer, 'toLiteral', which
'Data.CFTA.Gen.Refinement.Derive.holds' and 'Data.CFTA.Gen.Refinement.Derive.measureOf' read. A generator for a type with constructors
replaces the derived one, so a field of that type is drawn from it.
-}
atom :: forall c. (HasFTA c, Literal c) => LTAGen c -> Atoms
atom generator = Atoms (Map.singleton (typeRep $ Proxy @c) (atomicField generator)) Map.empty []

-- | The generator of an atomic type, and the integer of its terms.
atomicField :: forall c. (HasFTA c, Literal c) => LTAGen c -> AtomicField
atomicField generator = AtomicField (encodeTerm <$> generator) (fmap (toLiteral @c) . decodeTerm)

{- | The atom of a type: its own atom, or else a field atom of that type. The
integer of a term depends only on the type, so any field atom of the type
gives it.
-}
atomOfType :: Atoms -> TypeRep -> Maybe AtomicField
atomOfType (Atoms types fields _) typ = case Map.lookup typ types of
    Just field -> Just field
    Nothing -> case [field | (typ', field) <- Map.elems fields, typ' == typ] of
        field : _ -> Just field
        [] -> Nothing

-- | The contracts and the measures of one constructor. Combine them with '<>'.
data Annotation = Annotation
    { annotationContracts :: ![Contract]
    , annotationMeasures :: ![Measure]
    , annotationNamedMeasures :: ![(String, Measure)]
    }

instance Semigroup Annotation where
    Annotation contracts measures named <> Annotation contracts' measures' named' =
        Annotation (contracts <> contracts') (measures <> measures') (named <> named')

instance Monoid Annotation where
    mempty = Annotation [] [] []

{- | A contract: a formula with one term for each field, in order, as for
'guarded'. Each term is the integer of the field: the value of an atomic
field, or the measure of a field with constructors.
-}
contract :: (ContractBuilder builder) => builder -> Annotation
contract builder = Annotation [Contract (contractArity builder) (contractFormulaFrom 0 builder)] [] []

{- | A measure: the integer of a constructed term, with one term for each field,
in order, as for 'measured'. The measure of a constructor without fields is
one term, as in @measure (0 :: Expr)@, and it is the refinement of its leaf.
-}
measure :: (MeasureBuilder builder) => builder -> Annotation
measure builder = Annotation [] [Measure (measureArity builder) (measureTermFrom 0 builder)] []

{- | A named measure: an uninterpreted function of the value, as for
'measuredBy'. A constructor can have several named measures, or one measure of
'measure'. A contract and a named measure read the named measure of a field as
@uninterpreted name [field]@. The named measures of a constructor without
fields are its refinement, as in @measureNamed "bh" (0 :: Expr)@.
-}
measureNamed :: (MeasureBuilder builder) => String -> builder -> Annotation
measureNamed name builder = Annotation [] [] [(name, Measure (measureArity builder) (measureTermFrom 0 builder))]

{- | A contract of a constructor with the given number of fields, as a
function of the list of the terms of the fields. Use it when the number of
fields is known only at run time, as in a translation of another language.
-}
fieldsContract :: Int -> ([Expr] -> Formula) -> Annotation
fieldsContract count formulaOf = Annotation [Contract (Arity count) (formulaOf $ fieldTerms count)] [] []

-- | A measure of a constructor with the given number of fields, as 'fieldsContract' gives a contract.
fieldsMeasure :: Int -> ([Expr] -> Expr) -> Annotation
fieldsMeasure count termOf = Annotation [] [Measure (Arity count) (termOf $ fieldTerms count)] []

-- | The terms of the fields of a constructor, as a contract names them: @contractTermName i@ for field @i@.
fieldTerms :: Int -> [Expr]
fieldTerms count = [variable $ contractTermName $ ArgumentIndex position | position <- [0 .. count - 1]]

{- | The contract formulas, the measure terms, and the named measure terms of
an annotation, in the order of '<>'. A formula names the term of field @i@ as
'contractTermName' @i@. Two annotations with equal formulas and terms give
the same generator.
-}
annotationFormulas :: Annotation -> ([Formula], [Expr], [(String, Expr)])
annotationFormulas (Annotation contracts measures named) =
    ( [formula | Contract _ formula <- contracts]
    , [term | Measure _ term <- measures]
    , [(name, term) | (name, Measure _ term) <- named]
    )

-- | A contract with a known number of terms, which 'guarded' and 'measured' check.
data Contract = Contract !Arity !Formula

instance ContractBuilder Contract where
    contractArity (Contract arity _) = arity
    contractFormulaFrom index (Contract arity formula) = renumber index arity formula

-- | A measure with a known number of terms, which 'measured' checks.
data Measure = Measure !Arity !Expr

instance MeasureBuilder Measure where
    measureArity (Measure arity _) = arity
    measureTermFrom index (Measure arity term) = case renumber index arity (Atom Eq (fromExpr term) (Formula.Lit 0)) of
        Atom Eq renamed _ -> toExpr renamed
        _ -> term

{- | Name the terms of a formula from the given index. The formula names its
terms from zero.
-}
renumber :: ArgumentIndex -> Arity -> Formula -> Formula
renumber (ArgumentIndex 0) _ formula = formula
renumber (ArgumentIndex start) (Arity count) formula =
    substitute
        [ (contractTermName (ArgumentIndex position), variable $ contractTermName (ArgumentIndex $ start + position))
        | position <- [0 .. count - 1]
        ]
        formula

-- | One constructor of the datatype, with the types of its fields.
data Alternative = Alternative !Constructor ![TypeRep]

-- | The largest number of types that a datatype can reach.
typeLimit :: Int
typeLimit = 10000

{- | Derive the refinement generator of a datatype.

The bound is the number of times that the recursive occurrences nest, as for
'recurUpTo'. Each atomic field needs a generator from the 'Atoms': the atom
of its type, or a field atom of the field. Each annotation is for one
'Constructor'. A constructor without annotations has no contract and no
measure.
-}
deriveLTAWith ::
    forall a. (HasFTA a) => Depth -> Atoms -> [(Constructor, Annotation)] -> Either DeriveLTAError (LTAGen a)
deriveLTAWith bound atoms@(Atoms typeMap fieldMap _) named = do
    Derivation derived annotationOf <- derivation @a atoms named
    pure $ decodeValue <$> generatorOf (buildAll derived annotationOf) (typeRep $ Proxy @a)
  where
    generatorOf built typ = Map.findWithDefault (maybe emptyGenerator atomGenerator $ Map.lookup typ typeMap) typ built
    -- The atom of a field of a constructor, when the field has one.
    fieldAtomOf constructor position typ = case Map.lookup (constructor, position) fieldMap of
        Just (typ', field) | typ' == typ -> Just field
        _ -> Nothing

    -- The types that refer to each other unfold together, as 'recurUpTo'
    -- unfolds one type. A group comes after the groups that it refers to.
    buildAll derived annotationOf = foldl buildGroup Map.empty $ stronglyConnComp graph
      where
        graph =
            [ (typ, typ, nubOrd [field | Alternative _ fields <- alternatives, field <- fields, Map.member field derived])
            | (typ, alternatives) <- Map.toList derived
            ]
        buildGroup built (AcyclicSCC typ) = Map.insert typ (step built typ) built
        buildGroup built (CyclicSCC types)
            | bound < 0 = Map.union emptyGroup built
            | otherwise = Map.union (iterate unfold (unfold emptyGroup) !! fromEnum bound) built
          where
            emptyGroup = Map.fromList [(typ, emptyGenerator) | typ <- types]
            unfold previous = Map.fromList [(typ, step (Map.union previous built) typ) | typ <- types]
        step built typ = case Map.findWithDefault [] typ derived of
            [alternative] -> alternativeGenerator built alternative
            alternatives -> oneof $ map (alternativeGenerator built) alternatives
        alternativeGenerator built (Alternative constructor fieldTypes) =
            constructorGenerator
                annotationOf
                constructor
                [isNothing (fieldAtomOf constructor position typ) && Map.member typ derived | (position, typ) <- zip [0 ..] fieldTypes]
                [ maybe (generatorOf built typ) atomGenerator (fieldAtomOf constructor position typ)
                | (position, typ) <- zip [0 ..] fieldTypes
                ]

{- | Derive the refinement generator of the terms of an automaton over the
constructors of a datatype, such as the automaton of
'Data.CFTA.Gen.Typing.typingAutomaton'.

Each state of the automaton is a 'oneof' of its transitions, in order, and
each transition is the generator of its constructor, with the contracts and
the measures of the annotations, over the generators of its child states, as
'deriveLTAWith' builds a constructor over the generators of its field types.
A transition of an atomic type, or of a type that an atom replaces, is a
'leaf' for each of its terms, whose refinement is the integer that the atom
gives the term. So the ranks follow the generators, as for 'deriveLTAWith',
and they are not the ranks of 'Data.CFTA.Gen.Typing.fromConstructorAutomaton'.

The automaton must be acyclic ('CyclicAutomaton'), and its transitions must
have no constraint ('ConstrainedTransition'), because a generator has no place
for an equality between children. The checks of 'deriveLTAWith' on the names,
the atoms, and the annotations apply. A field atom gives no generator here,
because the automaton gives the terms of each field; it gives the integer of
its type when the type has no 'atom'.
-}
deriveLTAOnWith ::
    forall a state.
    (HasFTA a, Ord state) =>
    FTA.FTA state Constructor Constraint ->
    Atoms ->
    [(Constructor, Annotation)] ->
    Either DeriveLTAError (LTAGen a)
deriveLTAOnWith automaton atoms named = do
    Derivation derived annotationOf <- derivation @a atoms named
    unless (Set.null $ FTA.cyclicStates trimmed) $ Left CyclicAutomaton
    case [constructorName symbol | FTA.Transition symbol _ constraint <- concat (Map.elems rows), constraint /= noConstraint] of
        name : _ -> Left $ ConstrainedTransition name
        [] -> pure ()
    -- The automaton is acyclic, so each generator of the lazy map reads only
    -- the generators of states below it.
    let generators = LazyMap.map (stateGenerator derived annotationOf generators) rows
    pure $ decodeValue <$> Map.findWithDefault emptyGenerator (FTA.initialState trimmed) generators
  where
    trimmed = FTA.trim automaton
    rows = FTA.transitionTable trimmed

    stateGenerator derived annotationOf generators transitions = case concatMap transitionGenerators transitions of
        [] -> emptyGenerator
        [generator] -> generator
        alternatives -> oneof alternatives
      where
        transitionGenerators (FTA.Transition constructor children _) = case atomOfType atoms (constructorType constructor) of
            Just field ->
                [ leaf term (fromString $ constructorName constructor) (.== fromInteger (integerOf field term))
                | term <- termsOf (FTA.Transition constructor children noConstraint)
                ]
            Nothing ->
                [ constructorGenerator
                    annotationOf
                    constructor
                    [Map.member (fieldType field) derived | field <- constructorFields constructor]
                    [Map.findWithDefault emptyGenerator child generators | child <- children]
                ]

    integerOf field term =
        fromMaybe
            (error "cfta-generator bug in Data.CFTA.Gen.Refinement.Derive: an atom without the integer of its term")
            (atomInteger field term)

    -- The terms of a transition, finitely many in an acyclic automaton.
    termsOf (FTA.Transition constructor children _) =
        Term.Node constructor <$> traverse (\child -> concatMap termsOf (Map.findWithDefault [] child rows)) children

-- | The checked parts of a derivation: the types with constructors that no atom replaces, and the annotation of each constructor.
data Derivation = Derivation !(Map.Map TypeRep [Alternative]) (Constructor -> Annotation)

{- | Reach the types of a datatype, and check the names of the annotations, the
atoms of the atomic types, and the arity and the parts of each annotation.
-}
derivation :: forall a. (HasFTA a) => Atoms -> [(Constructor, Annotation)] -> Either DeriveLTAError Derivation
derivation (Atoms atoms fieldMap problems) named = do
    reached <- reach Map.empty (describeType $ Proxy @a)
    let derived = Map.filterWithKey (\typ _ -> not $ Map.member typ atoms) $ Map.mapMaybe id reached
        constructors = [constructor | alternatives <- Map.elems derived, Alternative constructor _ <- alternatives]
        known = nubOrd $ map constructorName constructors
        unknown =
            nubOrd
                [ constructorName constructor
                | constructor <- map fst named <> map fst (Map.keys fieldMap)
                , constructor `notElem` constructors
                ]
        -- An atomic type without an atom of its own.
        atomic typ = case Map.lookup typ reached of
            Just Nothing -> not (Map.member typ atoms)
            _ -> False
        root = typeRep $ Proxy @a
    case problems of
        problem : _ -> Left problem
        [] -> pure ()
    unless (null unknown) $ Left $ UnknownConstructors unknown known
    case [ (constructor, position, typ)
         | ((constructor, position), (typ, _)) <- Map.toList fieldMap
         , take 1 (drop position (map fieldType (constructorFields constructor))) /= [typ]
         ] of
        (constructor, position, typ) : _ -> Left $ FieldAtomMismatch (constructorName constructor) position typ
        [] -> pure ()
    -- An atomic type needs an atom where a field of that type has no field
    -- atom, and where it is the datatype itself.
    case [root | atomic root]
        <> [ typ
           | Alternative constructor fieldTypes <- concat (Map.elems derived)
           , (position, typ) <- zip [0 ..] fieldTypes
           , atomic typ
           , not (covered constructor position typ)
           ] of
        typ : _ -> Left $ MissingAtom typ
        [] -> pure ()
    mapM_ checkAnnotation constructors
    sequence_
        [ checkFields derived constructor fields
        | alternatives <- Map.elems derived
        , Alternative constructor fields <- alternatives
        ]
    pure $ Derivation derived annotationOf
  where
    annotations = Map.fromListWith (flip (<>)) named
    annotationOf constructor = Map.findWithDefault mempty constructor annotations

    -- Whether a field atom gives the field of the constructor a generator.
    covered constructor position typ = case Map.lookup (constructor, position) fieldMap of
        Just (typ', _) -> typ' == typ
        Nothing -> False

    -- The reached types: the alternatives of a type with constructors, and
    -- 'Nothing' for an atomic type.
    reach reached description
        | Map.size reached > typeLimit = Left $ TooManyTypes typeLimit
        | Map.member (descriptionType description) reached = Right reached
        | otherwise = case description of
            AtomicType typ -> Right $ Map.insert typ Nothing reached
            AlgebraicType typ alternatives ->
                let entry = [Alternative constructor (map descriptionType children) | (constructor, children) <- alternatives]
                 in foldlM' reach (Map.insert typ (Just entry) reached) (concatMap snd alternatives)

    checkAnnotation constructor = do
        let Annotation contracts measures namedMeasures = annotationOf constructor
            arity = Arity $ length $ constructorFields constructor
            name = constructorName constructor
        mapM_ (\supplied -> unless (supplied == arity) $ Left $ AnnotationArityMismatch name arity supplied) $
            [supplied | Contract supplied _ <- contracts]
                <> [supplied | Measure supplied _ <- measures]
                <> [supplied | (_, Measure supplied _) <- namedMeasures]
        unless
            (length measures + min 1 (length namedMeasures) <= 1 && length (nubOrd $ map fst namedMeasures) == length namedMeasures)
            $ Left
            $ SeveralMeasures name
        unless (null contracts || arity > 0) $ Left $ ContractWithoutFields name

    -- A field that a contract or a measure reads needs an integer: an atom,
    -- or a measure of a constructor of its type.
    checkFields derived constructor fields =
        sequence_
            [ Left $ UnmeasuredField (constructorName constructor) position typ
            | (position, typ) <- zip [0 ..] fields
            , contractTermName (ArgumentIndex position) `elem` readNames
            , not (Map.member typ atoms)
            , not (covered constructor position typ)
            , not (any measuredAlternative (Map.findWithDefault [] typ derived))
            ]
      where
        Annotation contracts measures namedMeasures = annotationOf constructor
        readNames =
            concat $
                [freeNames formula | Contract _ formula <- contracts]
                    <> [freeNames (term .== 0) | Measure _ term <- measures <> map snd namedMeasures]
        measuredAlternative (Alternative alternative _) =
            let Annotation _ measures' named' = annotationOf alternative in not (null measures' && null named')

-- | A generator without members.
emptyGenerator :: LTAGen a
emptyGenerator = Transparent $ Left EmptyGenerator

-- | The value of a term of the datatype.
decodeValue :: (HasFTA a) => Term Constructor -> a
decodeValue term =
    fromMaybe
        (error "cfta-generator bug in Data.CFTA.Gen.Refinement.Derive: the codec rejected a term of its own grammar")
        (decodeTerm term)

{- | The generator of a constructor over the generators of its fields, with its
annotation. The contract conjuncts that name only one atomic field become
conditions on that field. The other conjuncts stay in the contract.
-}
constructorGenerator ::
    (Constructor -> Annotation) -> Constructor -> [Bool] -> [LTAGen (Term Constructor)] -> LTAGen (Term Constructor)
constructorGenerator annotationOf constructor derivedFields generators = case (annotationMeasures annotation, annotationNamedMeasures annotation) of
    _ | null generators -> leaf (Term.Node constructor []) symbol refinement
    ([measureAnnotation], _) -> measured symbol remaining measureAnnotation spine
    (_, namedMeasures@(_ : _)) -> measuredBy symbol remaining namedMeasures spine
    _
        | remainingFormula == Top -> node symbol spine
        | otherwise -> guarded symbol remaining spine
  where
    annotation = annotationOf constructor
    symbol = fromString $ constructorName constructor
    refinement = case (annotationMeasures annotation, annotationNamedMeasures annotation) of
        ([Measure _ term], _) -> (.== term)
        (_, namedMeasures@(_ : _)) -> \value -> foldr1 (.&&) [uninterpreted name [value] .== term | (name, Measure _ term) <- namedMeasures]
        _ -> const Top
    conjuncts = concatMap parts [formula | Contract _ formula <- annotationContracts annotation]
    parts (And formulas) = concatMap parts formulas
    parts Top = []
    parts formula = [formula]
    fieldOf formula = case nubOrd (freeNames formula) of
        [name]
            | (position, False) : _ <-
                [ (position, isDerived)
                | (position, isDerived) <- zip [0 ..] derivedFields
                , contractTermName (ArgumentIndex position) == name
                ] ->
                Just position
        _ -> Nothing
    conditions = Map.fromListWith (flip (<>)) [(position, [formula]) | formula <- conjuncts, Just position <- [fieldOf formula]]
    remainingFormula = conjunction [formula | formula <- conjuncts, Nothing <- [fieldOf formula]]
    remaining = Contract (Arity $ length generators) remainingFormula
    spine = Term.Node constructor <$> zipWithM conditioned [0 ..] generators
    conditioned position generator = case Map.lookup position conditions of
        Nothing -> generator
        Just formulas -> generator `satisfying` fieldRefinement position formulas
    fieldRefinement :: Int -> [Formula] -> Refinement
    fieldRefinement position formulas value =
        substitute [(contractTermName (ArgumentIndex position), value)] (conjunction formulas)

-- | The type that a description describes.
descriptionType :: Description -> TypeRep
descriptionType (AtomicType typ) = typ
descriptionType (AlgebraicType typ _) = typ

-- | A strict left fold in 'Either'.
foldlM' :: (b -> a -> Either e b) -> b -> [a] -> Either e b
foldlM' _ accumulator [] = Right accumulator
foldlM' step accumulator (x : xs) = step accumulator x >>= \next -> next `seq` foldlM' step next xs
