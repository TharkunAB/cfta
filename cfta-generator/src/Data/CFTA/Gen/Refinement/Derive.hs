{-# LANGUAGE PatternSynonyms #-}

{- | Derive a refinement generator from a datatype.

A datatype with a 'HasFTA' instance has a grammar. With an invariant, a
measure and a contract that are Haskell functions, it also has a refinement
generator:

@
data SortedList = Nil | Cons Integer SortedList
    deriving stock (Generic)
    deriving anyclass (HasFTA)

instance HasLTA SortedList where
    invariant = Measured headOf sorted
      where
        headOf Cons{} [x, _] = x
        headOf _ _ = 1000001
        sorted Cons{} [x, restHead] = 0 .<= x .&& x .<= 1000000 .&& x .<= restHead
        sorted _ _ = true

sortedLists :: Either DeriveLTAError (LTAGen SortedList)
sortedLists = deriveLTA \@SortedList 8 (atom \@Integer every)
@

A datatype with several integers for each value, such as the color and the
black height of a red-black tree, has named measures: 'MeasuredBy' gives each
constructor a list of named measures, and its functions read the measures of
the children with 'childMeasure'.

The functions are polymorphic over 'Symbolic'. On 'Expr', they give the
formulas of the generator. On 'Integer', 'holds' and 'measureOf' run them on
values, so the same text checks the values of a test. 'deriveLTAWith' is the
level below: it takes the contracts and the measures of the constructors as
annotations in the expression language of "Data.CFTA.Refinement.Expression",
by constructor name.

The result is the generator that a person writes with the combinators of
"Data.CFTA.Gen.Refinement". A type with more than one constructor is a
'oneof' of its constructors, in declaration order. A constructor without
fields is a 'leaf', and its measure, if any, is its refinement. Another
constructor is a 'measured' node when it has a measure, a 'guarded' node when
it has a contract, and a 'node' otherwise. An atomic field gets the generator
that 'atom' gives for its type. So the ranks are the ranks of that
hand-written generator. Each member is the 'Term' of a value, as
'encodeTerm' gives it, and the generator decodes it with 'decodeTerm'.

A conjunct of a contract that names only one atomic field is a condition on
that field, as 'satisfying' puts it where the field is drawn. So the bounds
of an 'every' field can be in the contract, and the generator still counts
them where the field is drawn.

The bound has the meaning of 'recurUpTo'. The types that refer to each other
form one group, and they unfold together: their recursive occurrences nest at
most the bound times. A type that is in no cycle does not use a level.
-}
module Data.CFTA.Gen.Refinement.Derive (
    -- * Datatypes with an invariant
    HasLTA (..),
    deriveLTA,
    Invariant (..),
    holds,
    measureOf,
    measuresOf,
    Placeholders,

    -- * Atomic fields
    Atoms,
    atom,

    -- * Annotations
    deriveLTAWith,
    deriveLTAFrom,
    invariantAnnotations,
    Annotation,
    contract,
    measure,
    measureNamed,
    fieldsContract,
    fieldsMeasure,
    annotationFormulas,

    -- * Errors
    DeriveLTAError (..),
) where

import Control.Monad (unless, zipWithM)
import Data.Containers.ListUtils (nubOrd)
import Data.Graph (SCC (..), stronglyConnComp)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Typeable (TypeRep, typeRep)
import GHC.Generics (C, D, Generic (Rep, to), K1 (K1), M1 (M1), S, U1 (U1), V1, conName, (:*:) ((:*:)), (:+:) (L1, R1))
import qualified GHC.Generics as Generic

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
import Data.CFTA.Refinement.Symbolic (Boolean (true), Measures (Child), NodeIntegers (..), Symbolic (Truth))
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
    | {- | The datatype reaches more types than the limit. A type that grows its
      argument on each recursion, such as @data T a = L a | N (T (a, a))@,
      reaches infinitely many types.
      -}
      TooManyTypes !Int
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
'holds' and 'measureOf' read. A generator for a type with constructors
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

-- | The terms of the fields of a constructor, as a contract names them.
fieldTerms :: Int -> [Expr]
fieldTerms count = [variable $ contractTermName $ ArgumentIndex position | position <- [0 .. count - 1]]

{- | The contract formulas and the measure terms of an annotation, in the
order of '<>'. A formula names the term of field @i@ as 'contractTermName' @i@.
Two annotations with equal formulas and terms give the same generator.
-}
annotationFormulas :: Annotation -> ([Formula], [Expr])
annotationFormulas (Annotation contracts measures _) =
    ([formula | Contract _ formula <- contracts], [term | Measure _ term <- measures])

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
    pure $ decode <$> generatorOf (buildAll derived) (typeRep $ Proxy @a)
  where
    annotations = Map.fromListWith (flip (<>)) named
    annotationOf constructor = Map.findWithDefault mempty (constructorName constructor) annotations
    empty = Transparent $ Left EmptyGenerator
    generatorOf built typ = Map.findWithDefault (maybe empty atomGenerator $ Map.lookup typ atoms) typ built

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

    -- The types that refer to each other unfold together, as 'recurUpTo'
    -- unfolds one type. A group comes after the groups that it refers to.
    buildAll derived = foldl buildGroup Map.empty $ stronglyConnComp graph
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
            emptyGroup = Map.fromList [(typ, empty) | typ <- types]
            unfold previous = Map.fromList [(typ, step (Map.union previous built) typ) | typ <- types]
        step built typ = case Map.findWithDefault [] typ derived of
            [alternative] -> alternativeGenerator built alternative
            alternatives -> oneof $ map (alternativeGenerator built) alternatives
        alternativeGenerator built (Alternative constructor fields) =
            constructorGenerator constructor (map (`Map.member` derived) fields) (map (generatorOf built) fields)

    -- The contract conjuncts that name only one atomic field become
    -- conditions on that field. The other conjuncts stay in the contract.
    constructorGenerator constructor derivedFields generators = case (annotationMeasures annotation, annotationNamedMeasures annotation) of
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

    decode term =
        fromMaybe
            (error "cfta-generator bug in Data.CFTA.Gen.Refinement.Derive: the codec rejected a term of its own grammar")
            (decodeTerm term)

{- | A measure and a contract of a datatype, written once as Haskell functions
that are polymorphic over 'Symbolic'.

Each function takes a constructor of the datatype and the integers of its
fields, in order: the value of an atomic field, and the measure of a field of
the datatype itself. On 'Expr', the functions give the formulas of
'deriveLTAFrom'. On 'Integer', they give 'holds' and 'measureOf'. Match the
constructor with a pattern that does not read its fields, such as @Black{}@
or @(_ : _)@: the generator calls each function on a placeholder value, whose
fields are errors.

'MeasuredBy' gives each constructor several named measures. Its functions
take the children with the class 'Measures', and read a named measure of a
child with 'childMeasure'. The black height and the color of a red-black
tree:

@
instance HasLTA Tree where
    invariant = MeasuredBy measures balanced
      where
        bh child = childMeasure "bh" child
        col child = childMeasure "col" child
        measures Black{} [left, _] = [("bh", bh left + 1), ("col", 0)]
        measures Red{} [left, _] = [("bh", bh left), ("col", 1)]
        measures _ _ = [("bh", 0), ("col", 0)]
        balanced Black{} [left, right] = bh left .== bh right
        balanced Red{} [left, right] = bh left .== bh right .&& col left .== 0 .&& col right .== 0
        balanced _ _ = true
@

Write @bh@ with its argument: the monomorphism restriction gives
@bh = childMeasure "bh"@ one type of integers, and the invariant uses it on
both 'Expr' and 'Integer'. On 'Expr', the named measures are uninterpreted
functions, as for 'measuredBy'. On 'Integer', 'measuresOf' gives the named
measures of a value.
-}
data Invariant a
    = -- | A measure and a contract.
      Measured (forall e. (Symbolic e) => a -> [e] -> e) (forall e. (Symbolic e) => a -> [e] -> Truth e)
    | -- | A contract without a measure.
      Contracted (forall e. (Symbolic e) => a -> [e] -> Truth e)
    | {- | Named measures and a contract. The functions take the children of a
      constructor, and read their named measures with 'childMeasure' and the
      integers of atomic children with 'childValue'.
      -}
      MeasuredBy
        (forall e. (Measures e) => a -> [Child e] -> [(String, e)])
        (forall e. (Measures e) => a -> [Child e] -> Truth e)

{- | Derive the refinement generator of a datatype from an invariant. This is
'deriveLTAWith' with the annotations that the invariant gives on 'Expr'. A
contract that is 'true' for a constructor is no contract.
-}
deriveLTAFrom ::
    forall a.
    (HasFTA a, Generic a, Placeholders (Rep a)) =>
    Depth ->
    Atoms ->
    Invariant a ->
    Either DeriveLTAError (LTAGen a)
deriveLTAFrom bound atoms rules = deriveLTAWith @a bound atoms (invariantAnnotations rules)

{- | Datatypes with an invariant: the measure and the contract of 'Invariant'.

Derive the class with @deriving anyclass (HasLTA)@ for a datatype without an
invariant, or write an instance with one method:

@
data SortedList = Nil | Cons Integer SortedList
    deriving stock (Generic)
    deriving anyclass (HasFTA)

instance HasLTA SortedList where
    invariant = Measured headOf sorted
      where
        headOf Cons{} [x, _] = x
        headOf _ _ = 1000001
        sorted Cons{} [x, restHead] = 0 .<= x .&& x .<= 1000000 .&& x .<= restHead
        sorted _ _ = true
@

The bound and the atoms are arguments of 'deriveLTA', not methods. They
belong to a use of the datatype, as the domains of
'Data.CFTA.Generic.deriveFTAWith' do: one datatype has generators of
several depths and over several pools.
-}
class (HasFTA a) => HasLTA a where
    -- | The measure and the contract. The default has no measure and a contract that always holds.
    invariant :: Invariant a
    invariant = Contracted (\_ _ -> true)

-- | Derive the refinement generator of a datatype from its 'HasLTA' instance.
deriveLTA :: forall a. (HasLTA a, Generic a, Placeholders (Rep a)) => Depth -> Atoms -> Either DeriveLTAError (LTAGen a)
deriveLTA bound atoms = deriveLTAFrom bound atoms (invariant @a)

{- | The annotations that an invariant gives on 'Expr', one for each
constructor of the datatype, in declaration order.
-}
invariantAnnotations :: forall a. (Generic a, Placeholders (Rep a)) => Invariant a -> [(String, Annotation)]
invariantAnnotations rules =
    [ (name, contractPart <> measurePart)
    | (name, count, placeholder) <- placeholders @a
    , let terms = fieldTerms count
          formula = case rules of
            Measured _ check -> check placeholder terms
            Contracted check -> check placeholder terms
            MeasuredBy _ check -> check placeholder terms
          contractPart
            | formula == Top = mempty
            | otherwise = Annotation [Contract (Arity count) formula] [] []
          measurePart = case rules of
            Measured measureOf' _ -> Annotation [] [Measure (Arity count) (measureOf' placeholder terms)] []
            Contracted _ -> mempty
            MeasuredBy measures _ -> Annotation [] [] [(measureName, Measure (Arity count) term) | (measureName, term) <- measures placeholder terms]
    ]

{- | Whether each node of the value whose type is the datatype satisfies the
contract. The atomic fields are read with the integer that 'atom' gives, and
the fields of the datatype itself with the measure.
-}
holds :: forall a. (HasFTA a, Generic a, Placeholders (Rep a)) => Atoms -> Invariant a -> a -> Bool
holds atoms rules = fst . evaluate atoms rules . encodeTerm

-- | The measure of a value, if the invariant has a measure.
measureOf :: forall a. (HasFTA a, Generic a, Placeholders (Rep a)) => Atoms -> Invariant a -> a -> Maybe Integer
measureOf atoms rules = nodeInteger . snd . evaluate atoms rules . encodeTerm

-- | The named measures of a value, if the invariant has named measures.
measuresOf ::
    forall a. (HasFTA a, Generic a, Placeholders (Rep a)) => Atoms -> Invariant a -> a -> Map.Map String Integer
measuresOf atoms rules = nodeMeasures . snd . evaluate atoms rules . encodeTerm

{- | Evaluate the invariant on a term of the datatype, from the leaves up: the
contracts hold at each node, and the measure of the root.
-}
evaluate ::
    forall a.
    (HasFTA a, Generic a, Placeholders (Rep a)) => Atoms -> Invariant a -> Term Constructor -> (Bool, NodeIntegers)
evaluate (Atoms atoms) rules = go
  where
    datatype = typeRep $ Proxy @a
    table = Map.fromList [(name, placeholder) | (name, _, placeholder) <- placeholders @a]
    go (Term.Node constructor children) =
        ( and [below | (below, _) <- fields] && here
        , NodeIntegers value measures
        )
      where
        placeholder = table Map.! constructorName constructor
        fields = zipWith field (constructorFields constructor) children
        nodes = map snd fields
        -- A field without an integer is an error only if a function reads it.
        integers = [fromMaybe (noInteger constructor position) (nodeInteger child) | (position, child) <- zip [0 :: Int ..] nodes]
        (here, value, measures) = case rules of
            Measured measureOf' check -> (check placeholder integers, Just $ measureOf' placeholder integers, Map.empty)
            Contracted check -> (check placeholder integers, Nothing, Map.empty)
            MeasuredBy named check -> (check placeholder nodes, Nothing, Map.fromList $ named placeholder nodes)
        field Field{fieldType} child
            | Just AtomicField{atomInteger} <- Map.lookup fieldType atoms = (True, NodeIntegers (atomInteger child) Map.empty)
            | fieldType == datatype = go child
            | otherwise = (True, NodeIntegers Nothing Map.empty)
    noInteger constructor position =
        error $
            "Data.CFTA.Gen.Refinement.Derive: field "
                <> show position
                <> " of "
                <> constructorName constructor
                <> " has no integer: it is not atomic, and it is not of the datatype"

{- | The constructors of a 'Generic' type: the name, the number of fields, and
a placeholder value whose fields are errors.
-}
placeholders :: forall a. (Generic a, Placeholders (Rep a)) => [(String, Int, a)]
placeholders = [(name, count, to value) | (name, count, value) <- placeholdersOf]

-- | The constructors of a generic representation, with placeholder values.
class Placeholders f where
    placeholdersOf :: [(String, Int, f p)]

instance (Placeholders f) => Placeholders (M1 D meta f) where
    placeholdersOf = [(name, count, M1 value) | (name, count, value) <- placeholdersOf]

instance (Placeholders left, Placeholders right) => Placeholders (left :+: right) where
    placeholdersOf =
        [(name, count, L1 value) | (name, count, value) <- placeholdersOf]
            <> [(name, count, R1 value) | (name, count, value) <- placeholdersOf]

instance Placeholders V1 where
    placeholdersOf = []

instance (Generic.Constructor meta, Holes fields) => Placeholders (M1 C meta fields) where
    placeholdersOf = [(name, holeCount (Proxy @fields), M1 $ holes name)]
      where
        name = conName (undefined :: M1 C meta fields ())

-- | The fields of a placeholder: errors that name the constructor.
class Holes f where
    holeCount :: Proxy f -> Int
    holes :: String -> f p

instance Holes U1 where
    holeCount _ = 0
    holes _ = U1

instance Holes (K1 index c) where
    holeCount _ = 1
    holes name =
        K1
            $ error
            $ "Data.CFTA.Gen.Refinement.Derive: an invariant reads a field of the placeholder of "
                <> name
                <> ". Read the fields from the list of integers."

instance (Holes f) => Holes (M1 S meta f) where
    holeCount _ = holeCount (Proxy @f)
    holes = M1 . holes

instance (Holes left, Holes right) => Holes (left :*: right) where
    holeCount _ = holeCount (Proxy @left) + holeCount (Proxy @right)
    holes name = holes name :*: holes name

-- | The type that a description describes.
descriptionType :: Description -> TypeRep
descriptionType (AtomicType typ) = typ
descriptionType (AlgebraicType typ _) = typ

-- | A strict left fold in 'Either'.
foldlM' :: (b -> a -> Either e b) -> b -> [a] -> Either e b
foldlM' _ accumulator [] = Right accumulator
foldlM' step accumulator (x : xs) = step accumulator x >>= \next -> next `seq` foldlM' step next xs
