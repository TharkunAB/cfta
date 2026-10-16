{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{- | Derive a refinement generator from a datatype.

A datatype with a 'HasFTA' instance has a grammar. With an invariant, a
measure and a contract that are Haskell functions, it also has a refinement
generator:

@
data SortedList = Nil | Cons Integer SortedList
    deriving stock (Generic)
    deriving anyclass (HasFTA)

-- One node of a sorted list: an element, and the head of the rest.
data SortedListNode e = NilNode | ConsNode e e
    deriving stock (Generic)
    deriving anyclass (NodeView)

instance HasLTA SortedList where
    type Node SortedList = SortedListNode
    type Measures SortedList = Single
    invariant = Measured headOf sorted
      where
        headOf NilNode = 1000001
        headOf (ConsNode x _) = x
        sorted NilNode = true
        sorted (ConsNode x restHead) = 0 .<= x .&& x .<= 1000000 .&& x .<= restHead

sortedLists :: Either DeriveLTAError (LTAGen SortedList)
sortedLists = deriveLTA \@SortedList 8 (atom \@Integer every)
@

The invariant reads a constructor and its children from the node view of the
datatype: a datatype with one constructor for each constructor of the
datatype, in the same order, and one field for each field. An atomic field is
its integer, @e@. A field of the datatype itself is the measures of the
child: @e@ for 'Measured', the one integer of the child, and a record of
measures for 'MeasuredBy'. So GHC checks the number of children of each
constructor, and @-Wincomplete-patterns@ checks that the invariant covers
each constructor. The derivation checks the node view against the datatype
and reports 'NodeMismatch'.

A datatype with several integers for each value, such as the color and the
black height of a red-black tree, has named measures: a record whose
selector names are the names of the measures in the logic. On 'Expr', the
field @bh@ of a child is the uninterpreted function @bh@ of the child; on
'Integer', it is the black height of the child:

@
data TreeMeasures e = TreeMeasures {bh :: e, col :: e}
    deriving stock (Generic)
    deriving anyclass (MeasureRecord)

data TreeNode e = LeafNode | BlackNode (TreeMeasures e) (TreeMeasures e) | RedNode (TreeMeasures e) (TreeMeasures e)
    deriving stock (Generic)
    deriving anyclass (NodeView)

instance HasLTA Tree where
    type Node Tree = TreeNode
    type Measures Tree = TreeMeasures
    invariant = MeasuredBy measures balanced
      where
        measures LeafNode = TreeMeasures 0 0
        measures (BlackNode left _) = TreeMeasures (bh left + 1) 0
        measures (RedNode left _) = TreeMeasures (bh left) 1
        balanced LeafNode = true
        balanced (BlackNode left right) = bh left .== bh right
        balanced (RedNode left right) = bh left .== bh right .&& col left .== 0 .&& col right .== 0
@

The functions are polymorphic over 'Symbolic'. On 'Expr', they give the
formulas of the generator. On 'Integer', 'holds', 'measureOf', and
'measuresOf' run them on values, so the same text checks the values of a
test. 'measuresAt' gives the measures of a value term, for a condition on the
root, as in @col (measuresAt v) .== 0@.

A measure can choose with 'Data.CFTA.Refinement.Symbolic.ite', and
'Data.CFTA.Refinement.Symbolic.smaller' and
'Data.CFTA.Refinement.Symbolic.larger' come from it. The bounds of a binary
search tree with the keys 0 to 3 are its least and its greatest key, with 4
and -1 for an empty tree:

@
bounds TipNode = Bounds 4 (-1)
bounds (BinNode left key right) = Bounds (smaller (lo left) key) (larger (hi right) key)
@

A field that a contract or a measure reads needs an integer: an atom, or a
measure of its type. A field of an enumeration without an atom is the error
'UnmeasuredField'.

A selector of a record of measures is a Haskell function, so it cannot have
the name of another function of the same module, such as a Liquid Haskell
measure @bh :: Tree -> Int@. Put the record in its own module and import it
qualified, or read the fields with @OverloadedRecordDot@.

The derivation is 'Data.CFTA.Gen.Refinement.Derive.Internal.deriveLTAWith'
with the annotations that the invariant gives on 'Expr'; that module
describes the generator that it builds.
-}
module Data.CFTA.Gen.Refinement.Derive (
    -- * Datatypes with an invariant
    HasLTA (..),
    deriveLTA,
    deriveLTAFrom,
    deriveLTARooted,
    deriveLTAFromRooted,
    Invariant (..),
    invariantAnnotations,

    -- * Node views and measures
    NodeView (nodeShape, buildNode),
    FieldKind (..),
    AnyNode (..),
    MeasureRecord (measureNames, measureFields, fromMeasureNames),
    Single (..),
    NoMeasures (..),
    measuresAt,

    -- * Values
    holds,
    holdsRooted,
    measureOf,
    measuresOf,

    -- * Atomic fields
    Atoms,
    atom,

    -- * The logic
    Boolean (..),
    Symbolic (..),
    smaller,
    larger,
    literal,

    -- * Errors
    DeriveLTAError (..),
) where

import Control.Monad (unless, when)
import qualified Data.Kind as Kind
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Typeable (typeRep)
import GHC.Generics (
    C,
    D,
    Generic (Rep, from, to),
    K1 (K1),
    M1 (M1),
    S,
    Selector,
    U1 (U1),
    V1,
    conName,
    selName,
    (:*:) ((:*:)),
    (:+:) (L1, R1),
 )
import qualified GHC.Generics as Generic

import Data.CFTA.Formula (Formula (Top))
import Data.CFTA.Gen.Refinement (LTAGen, satisfying)
import Data.CFTA.Gen.Refinement.Derive.Internal
import Data.CFTA.Generic (Constructor (..), Description (..), Field (..), HasFTA (..))
import Data.CFTA.Index (Arity (..), Depth)
import Data.CFTA.Refinement.Expression (Expr, literal, uninterpreted)
import Data.CFTA.Refinement.Symbolic (Boolean (..), Symbolic (..), larger, smaller)
import qualified Data.CFTA.Refinement.Symbolic.Internal as Children
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- * Measures

{- | Records of named measures: a datatype with one constructor whose fields
all have the type @e@ and have names. The names of the selectors are the
names of the measures in the logic. Derive the class with
@deriving stock (Generic)@ and @deriving anyclass (MeasureRecord)@.
-}
class MeasureRecord (m :: Kind.Type -> Kind.Type) where
    -- | The names of the measures, in the order of the fields.
    measureNames :: Proxy m -> [String]
    default measureNames :: (GRecord (Rep (m ())) ()) => Proxy m -> [String]
    measureNames _ = gNames @(Rep (m ())) @() Proxy

    -- | The measures of a record, in the order of the fields.
    measureFields :: m e -> [e]
    default measureFields :: (Generic (m e), GRecord (Rep (m e)) e) => m e -> [e]
    measureFields = gFields . from

    -- | The record whose field of each name has the value that the function gives for the name.
    fromMeasureNames :: (String -> e) -> m e
    default fromMeasureNames :: (Generic (m e), GRecord (Rep (m e)) e) => (String -> e) -> m e
    fromMeasureNames value = to (gFrom value)

-- | The measures of a 'Measured' invariant: one integer for each value, without a name.
newtype Single e = Single e

-- | The measures of a 'Contracted' invariant: none.
data NoMeasures e = NoMeasures
    deriving stock (Eq, Show, Generic)
    deriving anyclass (MeasureRecord)

-- | The measures of a value term, each the uninterpreted function of its name, for a condition on the root.
measuresAt :: (MeasureRecord m) => Expr -> m Expr
measuresAt value = fromMeasureNames (\name -> uninterpreted name [value])

-- | The names of the measures of a record value.
namesOf :: forall m e. (MeasureRecord m) => m e -> [String]
namesOf _ = measureNames (Proxy @m)

-- | The generic representation of a record of measures.
class GRecord f e where
    gNames :: Proxy f -> [String]
    gFields :: f p -> [e]
    gFrom :: (String -> e) -> f p

instance (GRecord f e) => GRecord (M1 D meta f) e where
    gNames _ = gNames @f @e Proxy
    gFields (M1 x) = gFields x
    gFrom value = M1 (gFrom value)

instance (GRecord f e) => GRecord (M1 C meta f) e where
    gNames _ = gNames @f @e Proxy
    gFields (M1 x) = gFields x
    gFrom value = M1 (gFrom value)

instance (GRecord f e, GRecord g e) => GRecord (f :*: g) e where
    gNames _ = gNames @f @e Proxy <> gNames @g @e Proxy
    gFields (x :*: y) = gFields x <> gFields y
    gFrom value = gFrom value :*: gFrom value

instance GRecord U1 e where
    gNames _ = []
    gFields U1 = []
    gFrom _ = U1

instance (Selector meta) => GRecord (M1 S meta (K1 index e)) e where
    gNames _ = [selName (undefined :: M1 S meta (K1 index e) ())]
    gFields (M1 (K1 x)) = [x]
    gFrom value = M1 (K1 (value (selName (undefined :: M1 S meta (K1 index e) ()))))

-- * Node views

-- | The kind of a field of a node view: an integer, or a record with the names of its measures.
data FieldKind = Scalar | Record [String]
    deriving (Eq, Show)

{- | Node views: a datatype with one constructor for each constructor of a
datatype, in the same order, whose fields are the integers of the fields:
@e@ for an atomic field and for the child of a 'Measured' or 'Contracted'
invariant, and a record of measures for the child of a 'MeasuredBy'
invariant. Derive the class with @deriving stock (Generic)@ and
@deriving anyclass (NodeView)@.
-}
class NodeView (node :: Kind.Type -> Kind.Type) where
    {- | The constructors of the view, in order, with the kinds of their
    fields; 'Nothing' for a view that fits every datatype ('AnyNode').
    -}
    nodeShape :: Proxy node -> Maybe [(String, [FieldKind])]
    default nodeShape :: (GNode (Rep (node Expr)) Expr) => Proxy node -> Maybe [(String, [FieldKind])]
    nodeShape _ = Just (gShape @(Rep (node Expr)) @Expr Proxy)

    -- | The view of the constructor at a position, with its children in order.
    buildNode :: (Children.Measures e) => Int -> [Children.Child e] -> node e
    default buildNode ::
        (Children.Measures e, Generic (node e), GNode (Rep (node e)) e) => Int -> [Children.Child e] -> node e
    buildNode position children = to (gBuild position children)

-- | The node view of a datatype without an invariant: it fits every datatype, and the derivation does not read it.
data AnyNode e = AnyNode

instance NodeView AnyNode where
    nodeShape _ = Nothing
    buildNode _ _ = AnyNode

-- | The generic representation of a node view.
class GNode f e where
    gShape :: Proxy f -> [(String, [FieldKind])]
    gCount :: Proxy f -> Int
    gBuild :: (Children.Measures e) => Int -> [Children.Child e] -> f p

instance (GNode f e) => GNode (M1 D meta f) e where
    gShape _ = gShape @f @e Proxy
    gCount _ = gCount @f @e Proxy
    gBuild position children = M1 (gBuild position children)

instance (GNode f e, GNode g e) => GNode (f :+: g) e where
    gShape _ = gShape @f @e Proxy <> gShape @g @e Proxy
    gCount _ = gCount @f @e Proxy + gCount @g @e Proxy
    gBuild position children
        | position < gCount @f @e Proxy = L1 (gBuild position children)
        | otherwise = R1 (gBuild (position - gCount @f @e Proxy) children)

instance GNode V1 e where
    gShape _ = []
    gCount _ = 0
    gBuild _ _ = error "Data.CFTA.Gen.Refinement.Derive: a node view without constructors"

instance (Generic.Constructor meta, GFields f e) => GNode (M1 C meta f) e where
    gShape _ = [(conName (undefined :: M1 C meta f ()), gKinds @f @e Proxy)]
    gCount _ = 1
    gBuild _ children = M1 (fst (gFill children))

-- | The generic representation of the fields of a constructor of a node view.
class GFields f e where
    gKinds :: Proxy f -> [FieldKind]
    gFill :: (Children.Measures e) => [Children.Child e] -> (f p, [Children.Child e])

instance GFields U1 e where
    gKinds _ = []
    gFill children = (U1, children)

instance (GFields f e, GFields g e) => GFields (f :*: g) e where
    gKinds _ = gKinds @f @e Proxy <> gKinds @g @e Proxy
    gFill children =
        let (x, rest) = gFill children
            (y, rest') = gFill rest
         in (x :*: y, rest')

instance (NodeField e x) => GFields (M1 S meta (K1 index x)) e where
    gKinds _ = [fieldKind @e @x]
    gFill (child : rest) = (M1 (K1 (fillField child)), rest)
    gFill [] = error "Data.CFTA.Gen.Refinement.Derive: a node view has more fields than its constructor"

-- | A field of a node view: an integer @e@, or a record of measures @m e@.
class NodeField e x where
    fieldKind :: FieldKind
    fillField :: (Children.Measures e) => Children.Child e -> x

instance NodeField e e where
    fieldKind = Scalar
    fillField = Children.childValue

instance (MeasureRecord m) => NodeField e (m e) where
    fieldKind = Record (measureNames (Proxy @m))
    fillField child = fromMeasureNames (\name -> Children.childMeasure name child)

-- * Invariants

{- | A measure and a contract of a datatype, written once as Haskell functions
that are polymorphic over 'Symbolic', over the node view @node@, with the
measures @m@.
-}
data Invariant node m where
    -- | One measure, the integer of each value, and a contract.
    Measured ::
        (forall e. (Symbolic e) => node e -> e) ->
        (forall e. (Symbolic e) => node e -> Truth e) ->
        Invariant node Single
    -- | A contract, without a measure.
    Contracted :: (forall e. (Symbolic e) => node e -> Truth e) -> Invariant node NoMeasures
    {- | Named measures, the fields of the record @m@, and a contract. On
    'Expr', a named measure is an uninterpreted function, as for
    'Data.CFTA.Gen.Refinement.measuredBy'.
    -}
    MeasuredBy ::
        (MeasureRecord m) =>
        (forall e. (Symbolic e) => node e -> m e) ->
        (forall e. (Symbolic e) => node e -> Truth e) ->
        Invariant node m

{- | Datatypes with an invariant: the node view, the measures, and the
'Invariant'. Derive the class with @deriving anyclass (HasLTA)@ for a
datatype without an invariant, or write an instance as in the examples above.

The bound and the atoms are arguments of 'deriveLTA', not methods. They
belong to a use of the datatype, as the domains of
'Data.CFTA.Generic.deriveFTAWith' do: one datatype has generators of
several depths and over several pools.
-}
class (HasFTA a, NodeView (Node a)) => HasLTA a where
    -- | The node view of the datatype.
    type Node a :: Kind.Type -> Kind.Type

    type Node a = AnyNode

    -- | The measures of a value: 'Single', 'NoMeasures', or a record of named measures.
    type Measures a :: Kind.Type -> Kind.Type

    type Measures a = NoMeasures

    -- | The invariant. The default has no measure and a contract that always holds.
    invariant :: Invariant (Node a) (Measures a)
    default invariant :: (Node a ~ AnyNode, Measures a ~ NoMeasures) => Invariant (Node a) (Measures a)
    invariant = Contracted (const true)

-- | Derive the refinement generator of a datatype from its 'HasLTA' instance.
deriveLTA :: forall a. (HasLTA a) => Depth -> Atoms -> Either DeriveLTAError (LTAGen a)
deriveLTA bound atoms = deriveLTAFrom bound atoms (invariant @a)

{- | Derive the refinement generator of a datatype from an invariant over a
node view of the datatype. A contract that is 'true' for a constructor is no
contract.
-}
deriveLTAFrom ::
    forall a node m. (HasFTA a, NodeView node) => Depth -> Atoms -> Invariant node m -> Either DeriveLTAError (LTAGen a)
deriveLTAFrom bound atoms rules = do
    annotations <- invariantAnnotations @a rules
    deriveLTAWith @a bound atoms annotations

{- | Derive the refinement generator of a datatype from its 'HasLTA' instance,
with a condition on the measures of the root. The condition is written once,
as the invariant is: 'holdsRooted' runs it on values. For a 'Measured'
invariant, the measures are 'Single'; for a 'Contracted' invariant,
'NoMeasures'.
-}
deriveLTARooted ::
    forall a.
    (HasLTA a) => Depth -> Atoms -> (forall e. (Symbolic e) => Measures a e -> Truth e) -> Either DeriveLTAError (LTAGen a)
deriveLTARooted bound atoms = deriveLTAFromRooted bound atoms (invariant @a)

-- | 'deriveLTAFrom' with a condition on the measures of the root, as for 'deriveLTARooted'.
deriveLTAFromRooted ::
    forall a node m.
    (HasFTA a, NodeView node) =>
    Depth -> Atoms -> Invariant node m -> (forall e. (Symbolic e) => m e -> Truth e) -> Either DeriveLTAError (LTAGen a)
deriveLTAFromRooted bound atoms rules condition =
    (`satisfying` (condition . rootMeasures rules)) <$> deriveLTAFrom bound atoms rules

-- | The measures of a value term, as the invariant names them.
rootMeasures :: Invariant node m -> Expr -> m Expr
rootMeasures rules value = case rules of
    Measured _ _ -> Single value
    Contracted _ -> NoMeasures
    MeasuredBy _ _ -> measuresAt value

-- | The constructors of a datatype in declaration order, with whether each field is of the datatype itself.
datatypeConstructors :: forall a. (HasFTA a) => [(Constructor, [Bool])]
datatypeConstructors = case describeType (Proxy @a) of
    AlgebraicType typ alternatives ->
        [(constructor, [fieldType field == typ | field <- constructorFields constructor]) | (constructor, _) <- alternatives]
    AtomicType _ -> []

-- | Whether a child of the datatype is a record of measures in the node view of an invariant.
childIsRecord :: Invariant node m -> Bool
childIsRecord rules = case rules of
    MeasuredBy _ _ -> True
    _ -> False

{- | Check the node view of an invariant against the datatype: the same
constructors in the same order, the same number of fields in each, an integer
for each atomic field, and for each child an integer, or a record with the
names of the invariant's measures.
-}
checkNodeView :: forall a node m. (HasFTA a, NodeView node) => [String] -> Invariant node m -> Either DeriveLTAError ()
checkNodeView names rules = case nodeShape (Proxy @node) of
    Nothing -> Right ()
    Just shape -> do
        let constructors = datatypeConstructors @a
        unless (length shape == length constructors)
            $ Left
            $ NodeMismatch
                (unwords (map (constructorName . fst) constructors))
                ("the datatype has " <> show (length constructors) <> " constructors, the node view " <> show (length shape))
        sequence_
            [ checkConstructor (constructorName constructor) children kinds
            | ((constructor, children), (_, kinds)) <- zip constructors shape
            ]
        sequence_
            [ Left $ NodeMismatch name ("the node view has " <> viewName <> " in its place, a name that does not start with " <> name)
            | ((constructor, _), (viewName, _)) <- zip constructors shape
            , let name = constructorName constructor
            , not (name `isPrefixOf` viewName)
            ]
  where
    expected isChild
        | isChild && childIsRecord rules = Record names
        | otherwise = Scalar
    checkConstructor name children kinds = do
        unless (length children == length kinds)
            $ Left
            $ NodeMismatch name ("the constructor has " <> show (length children) <> " fields, the node view " <> show (length kinds))
        sequence_
            [ unless (expected isChild == kind)
                $ Left
                $ NodeMismatch
                    name
                    ("field " <> show position <> " is " <> show kind <> " in the node view, not " <> show (expected isChild))
            | (position, (isChild, kind)) <- zip [0 :: Int ..] (zip children kinds)
            ]
        when (any null names)
            $ Left
            $ NodeMismatch name "a record of measures has a field without a name"

-- | The names of the measures of an invariant: the selectors of its record, or none.
invariantNames :: forall m node. Invariant node m -> [String]
invariantNames rules = case rules of
    MeasuredBy _ _ -> measureNames (Proxy @m)
    _ -> []

{- | The annotations that an invariant gives on 'Expr', one for each
constructor of the datatype, in declaration order, as
'Data.CFTA.Gen.Refinement.Derive.Internal.deriveLTAWith' takes them.
-}
invariantAnnotations ::
    forall a node m. (HasFTA a, NodeView node) => Invariant node m -> Either DeriveLTAError [(String, Annotation)]
invariantAnnotations rules = do
    checkNodeView @a (invariantNames rules) rules
    pure
        [ (constructorName constructor, contractPart <> measurePart)
        | (position, (constructor, children)) <- zip [0 ..] (datatypeConstructors @a)
        , let count = length children
              view = buildNode @node @Expr position (fieldTerms count)
              formula = case rules of
                Measured _ check -> check view
                Contracted check -> check view
                MeasuredBy _ check -> check view
              contractPart
                | formula == Top = mempty
                | otherwise = Annotation [Contract (Arity count) formula] [] []
              measurePart = case rules of
                Measured measureOf' _ -> Annotation [] [Measure (Arity count) (measureOf' view)] []
                Contracted _ -> mempty
                MeasuredBy named _ ->
                    let measures = named view
                     in Annotation [] [] [(name, Measure (Arity count) term) | (name, term) <- zip (namesOf measures) (measureFields measures)]
        ]

-- * Values

{- | Whether each node of the value whose type is the datatype satisfies the
contract. The atomic fields are read with the integer that 'atom' gives, and
the fields of the datatype itself with the measures.
-}
holds :: forall a node m. (HasFTA a, NodeView node) => Atoms -> Invariant node m -> a -> Bool
holds atoms rules = fst . evaluate @a atoms rules . encodeTerm

-- | Whether a value satisfies the invariant at each node and the condition on the measures of its root.
holdsRooted ::
    forall a node m.
    (HasFTA a, NodeView node) => Atoms -> Invariant node m -> (forall e. (Symbolic e) => m e -> Truth e) -> a -> Bool
holdsRooted atoms rules condition value = holds atoms rules value && condition rootValues
  where
    rootValues = case rules of
        Measured _ _ -> Single (measureOf atoms rules value)
        Contracted _ -> NoMeasures
        MeasuredBy _ _ -> measuresOf atoms rules value

-- | The measure of a value, for a 'Measured' invariant.
measureOf :: forall a node. (HasFTA a, NodeView node) => Atoms -> Invariant node Single -> a -> Integer
measureOf atoms rules =
    fromMaybe (error "Data.CFTA.Gen.Refinement.Derive: a Measured invariant gave no measure")
        . Children.nodeInteger
        . snd
        . evaluate @a atoms rules
        . encodeTerm

-- | The named measures of a value, as a record.
measuresOf :: forall a node m. (HasFTA a, NodeView node, MeasureRecord m) => Atoms -> Invariant node m -> a -> m Integer
measuresOf atoms rules value = fromMeasureNames (\name -> Map.findWithDefault (missing name) name measures)
  where
    measures = Children.nodeMeasures (snd (evaluate @a atoms rules (encodeTerm value)))
    missing name = error ("Data.CFTA.Gen.Refinement.Derive: the value has no measure " <> name)

{- | Evaluate the invariant on a term of the datatype, from the leaves up:
whether the contracts hold at each node, and the integers of the root. A node
view that does not fit the datatype is an error.
-}
evaluate ::
    forall a node m.
    (HasFTA a, NodeView node) => Atoms -> Invariant node m -> Term Constructor -> (Bool, Children.NodeIntegers)
evaluate (Atoms atoms) rules = either (error . show) (const go) (checkNodeView @a (invariantNames rules) rules)
  where
    datatype = typeRep (Proxy @a)
    positions =
        Map.fromList
            [(constructorName constructor, position) | (position, (constructor, _)) <- zip [0 :: Int ..] (datatypeConstructors @a)]
    go (Term.Node constructor children) = (and [below | (below, _) <- fields] && here, Children.NodeIntegers value measures)
      where
        position = Map.findWithDefault 0 (constructorName constructor) positions
        fields = zipWith field (constructorFields constructor) children
        view = buildNode @node @Integer position (map snd fields)
        (here, value, measures) = case rules of
            Measured measureOf' check -> (check view, Just (measureOf' view), Map.empty)
            Contracted check -> (check view, Nothing, Map.empty)
            MeasuredBy named check ->
                let record = named view
                 in (check view, Nothing, Map.fromList (zip (namesOf record) (measureFields record)))
        field Field{fieldType} child
            | Just AtomicField{atomInteger} <- Map.lookup fieldType atoms =
                (True, Children.NodeIntegers (atomInteger child) Map.empty)
            | fieldType == datatype = go child
            | otherwise = (True, Children.NodeIntegers Nothing Map.empty)
