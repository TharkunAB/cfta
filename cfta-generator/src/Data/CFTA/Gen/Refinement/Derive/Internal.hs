{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

{- | The level below "Data.CFTA.Gen.Refinement.Derive": the contracts and
the measures of the constructors of a datatype as annotations in the
expression language of "Data.CFTA.Refinement.Expression", by constructor
name.

This module is exposed for integration: a translation that knows the names of
the constructors and of the measures only at run time, such as one from
Liquid Haskell specifications, builds annotations here. It is not part of the
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
    -- * Annotations by constructor name
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

    -- * Errors
    DeriveLTAError (..),
) where

import Control.Monad (unless, zipWithM)
import Data.Containers.ListUtils (nubOrd)
import Data.Graph (SCC (..), stronglyConnComp)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
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
    = {- | Annotation names that no constructor of the datatype has. The second
      field lists the names of the constructors.
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
    deriving (Eq, Show)

-- | Generators for atomic field types, by type.
newtype Atoms = Atoms (Map.Map TypeRep AtomicField)

-- | The generator of one atomic type, and the integer of a term of that type.
data AtomicField = AtomicField
    { atomGenerator :: LTAGen (Term Constructor)
    , atomInteger :: Term Constructor -> Maybe Integer
    }

-- | When two generators are for one type, the rightmost one applies.
instance Semigroup Atoms where
    Atoms left <> Atoms right = Atoms $ Map.union right left

instance Monoid Atoms where
    mempty = Atoms Map.empty

{- | The generator of each field of a type, as in @atom \@Integer every@.

The value of an atomic field stands for one integer, 'toLiteral', which
'Data.CFTA.Gen.Refinement.Derive.holds' and 'Data.CFTA.Gen.Refinement.Derive.measureOf' read. A generator for a type with constructors
replaces the derived one, so a field of that type is drawn from it.
-}
atom :: forall c. (HasFTA c, Literal c) => LTAGen c -> Atoms
atom generator =
    Atoms $ Map.singleton (typeRep $ Proxy @c) $ AtomicField (encodeTerm <$> generator) (fmap (toLiteral @c) . decodeTerm)

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
'recurUpTo'. Each atomic field type needs a generator from the 'Atoms'. Each
annotation names a constructor. Constructors of different types that have the
same name get the same annotations. A constructor without annotations has no
contract and no measure.
-}
deriveLTAWith :: forall a. (HasFTA a) => Depth -> Atoms -> [(String, Annotation)] -> Either DeriveLTAError (LTAGen a)
deriveLTAWith bound (Atoms atoms) named = do
    Derivation derived annotationOf <- derivation @a (Atoms atoms) named
    pure $ decodeValue <$> generatorOf (buildAll derived annotationOf) (typeRep $ Proxy @a)
  where
    generatorOf built typ = Map.findWithDefault (maybe emptyGenerator atomGenerator $ Map.lookup typ atoms) typ built

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
        alternativeGenerator built (Alternative constructor fields) =
            constructorGenerator annotationOf constructor (map (`Map.member` derived) fields) (map (generatorOf built) fields)

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
the atoms, and the annotations apply.
-}
deriveLTAOnWith ::
    forall a state.
    (HasFTA a, Ord state) =>
    FTA.FTA state Constructor Constraint ->
    Atoms ->
    [(String, Annotation)] ->
    Either DeriveLTAError (LTAGen a)
deriveLTAOnWith automaton (Atoms atoms) named = do
    Derivation derived annotationOf <- derivation @a (Atoms atoms) named
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
        transitionGenerators (FTA.Transition constructor children _) = case Map.lookup (constructorType constructor) atoms of
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
derivation :: forall a. (HasFTA a) => Atoms -> [(String, Annotation)] -> Either DeriveLTAError Derivation
derivation (Atoms atoms) named = do
    reached <- reach Map.empty (describeType $ Proxy @a)
    let derived = Map.filterWithKey (\typ _ -> not $ Map.member typ atoms) $ Map.mapMaybe id reached
        constructors = [constructor | alternatives <- Map.elems derived, Alternative constructor _ <- alternatives]
        known = nubOrd $ map constructorName constructors
        unknown = nubOrd [name | (name, _) <- named, name `notElem` known]
    unless (null unknown) $ Left $ UnknownConstructors unknown known
    case [typ | (typ, Nothing) <- Map.toList reached, not $ Map.member typ atoms] of
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
    annotationOf constructor = Map.findWithDefault mempty (constructorName constructor) annotations

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
