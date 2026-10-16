{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Typed languages with variables, from typing rules for each constructor.

The language is the terms of a 'HasFTA' datatype that have one of some types,
with a nesting of at most a bound. Each rule gives a type to a constructor of
the datatype, by its name. A variable has a de Bruijn index: the index 0 is
the innermost binder. The environment of a term is the list of the types of
its binders, innermost first.

@
data Ty = TInt | TBool
data Typed = TZero | TTrue | TAdd Typed Typed | TIsZero Typed | TVar !Int !Ty | TLet Typed Typed

typedRules :: [Rule Ty]
typedRules =
    [ rule \"TZero\" [] TInt
    , rule \"TTrue\" [] TBool
    , rule \"TAdd\" [subterm [] TInt, subterm [] TInt] TInt
    , rule \"TIsZero\" [subterm [] TInt] TBool
    , variable \"TVar\" (\\index typ -> [value index, value typ])
    ]
        <> [rule \"TLet\" [subterm [] rhs, subterm [rhs] typ] typ | rhs <- [TInt, TBool], typ <- [TInt, TBool]]

closed :: Either TypingError (Gen Symbol Typed)
closed = fromTypingRules Typing{typingBound = Nesting 3, typingInputs = [], typingRoots = [TInt, TBool], typingRules = typedRules}
@

'typingAutomaton' builds the automaton whose states are an environment, a
type, and the nesting that remains ('TypingState'). Its symbols are the
constructors of the datatype and of the values, so the operations of
"Data.CFTA" and "Data.CFTA.Template" apply to it before it becomes a
generator: 'Data.CFTA.intersectWith' with another automaton over
'Constructor', such as an annotated 'Data.CFTA.Generic.datatypeFTA',
'Data.CFTA.annotate', which can read the environment and the type of a state,
and 'Data.CFTA.Template.excludeAnywhereFTA' or
'Data.CFTA.Template.restrictFTA'. 'fromConstructorAutomaton' reads the result,
and 'fromTypingRules' is the two in one.

The symbols of the generator are the labels of 'Data.CFTA.Gen.fromDatatype',
so a value and its term share one rank, and 'Data.CFTA.Gen.rankOfValue' finds
it. The ranks order the constructors of a node by arity, then in declaration
order, as for 'Data.CFTA.Gen.fromDatatype'. This holds for the constructors of
each type in the automaton. A literal has no declared position, so the
literals of one type follow the order of their labels. For numbers that are
not negative and have at most nine digits, that is the numeric order.
'Data.CFTA.Gen.fromDatatype' orders literals as their domain lists them.

Limits:

* A field that holds a subterm has the type of the datatype. A field of
  another type holds one fixed value. So a family of mutually recursive
  types is not a language here.
* The bound is on the nesting, so the language is finite. The automaton has
  about T^(D + 1) environments for T types and the bound D. A bound on the
  binders ('Binders') and inputs are not implemented yet.
-}
module Data.CFTA.Gen.Typing (
    -- * Rules
    Rule,
    Child,
    rule,
    variable,
    subterm,
    value,

    -- * Languages
    Typing (..),
    Bound (..),
    TypingError (..),
    fromTypingRules,

    -- * The automaton
    TypingState (..),
    typingAutomaton,
    fromConstructorAutomaton,
) where

import Control.Monad (unless, (<=<))
import Data.Containers.ListUtils (nubOrd)
import Data.Either (fromRight)
import Data.Hashable (hash)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (Proxy))
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Data.Text as Text
import Data.Typeable (TypeRep, typeRep)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import Data.CFTA.Gen.Error (GenError (UndecodableConstructor))
import Data.CFTA.Gen.Internal.Automaton (undecodableConstructor)
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Gen.Internal.Types (Gen, pattern Transparent)
import Data.CFTA.Generic (Constructor (..), Description (..), Field (..), HasFTA (..), constructorLabel)
import Data.CFTA.Index (Depth (..))
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | A typing rule of one constructor, by its name.
data Rule ty
    = Rule !String ![Child ty] !ty
    | Variable !String !(Int -> ty -> [Child ty])

-- | One field of a constructor in a rule.
data Child ty
    = Subterm ![ty] !ty
    | Value !(Term Constructor)

{- | @rule name children result@: the constructor has the type @result@ in
each environment when its fields are @children@, one for each field, in
order. A polymorphic rule is one rule for each type. The alternatives of
several rules of one constructor add up.
-}
rule :: String -> [Child ty] -> ty -> Rule ty
rule = Rule

{- | @variable name fields@: a variable of the goal type. For each position
of the environment that holds the goal type, the constructor has the fields
@fields index type@.
-}
variable :: String -> (Int -> ty -> [Child ty]) -> Rule ty
variable = Variable

{- | @subterm binds t@: a field that is a subterm of the type @t@. Its
environment is that of the node with @binds@ in front: the first type of
@binds@ is the variable with the index 0 in the subterm.
-}
subterm :: [ty] -> ty -> Child ty
subterm = Subterm

{- | A field with one value, such as a literal, an index, or a type.
The field must have a type other than the datatype of the language.
Use 'subterm' for a field of that datatype.
-}
value :: (HasFTA v) => v -> Child ty
value = Value . encodeTerm

-- | A typed language: the bound, the environment at the root, the types at the root, and the rules.
data Typing ty = Typing
    { typingBound :: !Bound
    -- ^ The bound on the terms.
    , typingInputs :: ![ty]
    -- ^ The types of the variables in scope at the root, innermost first. Not implemented yet: it must be empty.
    , typingRoots :: ![ty]
    -- ^ The types of the terms of the language.
    , typingRules :: ![Rule ty]
    -- ^ The typing rules.
    }

-- | The bound on the terms of a typed language.
data Bound
    = {- | The nesting of the recursive occurrences, as for
      'Data.CFTA.Gen.Refinement.recurUpTo': a constructor with a subterm
      field uses one level.
      -}
      Nesting !Depth
    | -- | The number of binders around each position. Not implemented yet.
      Binders !Int
    deriving (Eq, Show)

-- | Failure while building a typed language.
data TypingError
    = {- | Rule names that no constructor of the datatype has. The second
      field lists the names of the constructors.
      -}
      UnknownConstructors ![String] ![String]
    | {- | A rule of the constructor does not fit its fields: it has another
      number of fields, a subterm in a field of another type than the
      datatype, a fixed value in a field of the datatype, or a value of
      another type than its field.
      -}
      FieldMismatch !String
    | -- | A part of 'Typing' that is not implemented yet: inputs, or a bound on the binders.
      NotImplemented !String
    deriving (Eq, Show)

{- | A state of the automaton of a typed language: the root, a term of a type
in an environment, or one value. The nesting that remains is 'Just' for a
'Nesting' bound. The root has the transitions of the terms of each root
type, so a transition of the root does not say its type; its children do.
-}
data TypingState ty = Root | Goal ![ty] !ty !(Maybe Int) | Fixed !(Term Constructor)
    deriving (Eq, Ord, Show)

{- | The terms of the datatype that have one of the root types, within the
bound. A constructor without a rule is not in the language.
-}
fromTypingRules :: forall a ty. (HasFTA a, Ord ty) => Typing ty -> Either TypingError (Gen Symbol a)
fromTypingRules typing = fromConstructorAutomaton @a <$> typingAutomaton @a typing

{- | The automaton of a typed language over the constructors of the datatype
@a@ and of the values. Each state has a row, and each constructor has the
arity of its fields.
-}
typingAutomaton ::
    forall a ty. (HasFTA a, Ord ty) => Typing ty -> Either TypingError (FTA.FTA (TypingState ty) Constructor Constraint)
typingAutomaton Typing{typingBound = bound, typingInputs = inputs, typingRoots = roots, typingRules = rules} = do
    let unknown = nubOrd [name | name <- map ruleName rules, Map.notMember name constructors]
    unless (null unknown) $ Left $ UnknownConstructors unknown (map constructorName declared)
    mapM_ checked [(name, children) | Rule name children _ <- rules]
    unless (null inputs) $ Left $ NotImplemented "inputs"
    case bound of
        Nesting _ -> Right ()
        Binders _ -> Left $ NotImplemented "a bound on the binders"
    rows <- close Map.empty [Root]
    pure
        $ fromRight (error "cfta-generator bug in Data.CFTA.Gen.Typing: an invalid automaton")
        $ FTA.mkFTA Root (Map.toList rows)
  where
    declared = constructorsOf (describeType (Proxy @a))
    constructors = Map.fromList [(constructorName constructor, constructor) | constructor <- declared]
    ruleName (Rule name _ _) = name
    ruleName (Variable name _) = name

    -- The nesting at the root.
    nesting = case bound of
        Nesting (Depth depth) -> Just depth
        Binders _ -> Nothing

    close rows [] = Right rows
    close rows (state : pending)
        | Map.member state rows = close rows pending
        | otherwise = do
            transitions <- row state
            close (Map.insert state transitions rows) (concatMap FTA.transitionChildren transitions <> pending)

    row Root = concat <$> traverse (\typ -> row (Goal [] typ nesting)) (nubOrd roots)
    row (Fixed term) = Right [FTA.Transition (Term.rootLabel term) (map Fixed (Term.subForest term)) noConstraint]
    row (Goal env goal remaining) =
        traverse
            transition
            ( [(name, children) | Rule name children result <- rules, result == goal, nests children]
                <> [ (name, children)
                   | Variable name fields <- rules
                   , (index, typ) <- zip [0 ..] env
                   , typ == goal
                   , let children = fields index typ
                   , nests children
                   ]
            )
      where
        nests children = maybe True (> 0) remaining || null [() | Subterm _ _ <- children]
        transition alternative@(_, children) = do
            constructor <- checked alternative
            pure $ FTA.Transition constructor (map child children) noConstraint
        child (Subterm binds typ) = Goal (binds <> env) typ (subtract 1 <$> remaining)
        child (Value term) = Fixed term

    -- The constructor of a rule, when the children fit its fields.
    checked (name, children)
        | length children == length fields && and (zipWith fits fields children) = Right constructor
        | otherwise = Left $ FieldMismatch name
      where
        constructor = constructors Map.! name
        fields = constructorFields constructor
    fits field (Subterm _ _) = fieldType field == typeRep (Proxy @a)
    fits field (Value term) =
        fieldType field /= typeRep (Proxy @a)
            && fieldType field == constructorType (Term.rootLabel term)

{- | Read an automaton over the constructors of the datatype @a@ and of its
field values as a generator of values of @a@, as 'Data.CFTA.Gen.fromAutomaton'
reads an automaton: finite when it is acyclic, and counted by size otherwise.
The ranks order the constructors of a node by arity, then in declaration
order, and atomic literals by their labels.

When the generator is built, it decodes one term for each transition. If the
codec rejects one, the generator fails with 'UndecodableConstructor'.
-}
fromConstructorAutomaton ::
    forall a state. (HasFTA a, Ord state) => FTA.FTA state Constructor Constraint -> Gen Symbol a
fromConstructorAutomaton automaton = case undecodableConstructor (null . decodeTerm @a) automaton of
    Just constructor -> Transparent $ Left $ UndecodableConstructor $ constructorName constructor
    Nothing -> decode <$> Flat.fromAutomaton order (Interned.fromRows (FTA.initialState automaton) (Map.map (map labelled) rows))
  where
    rows = FTA.transitionTable automaton
    symbols = nubOrd [FTA.transitionSymbol transition | transitions <- Map.elems rows, transition <- transitions]
    labelled transition = transition{FTA.transitionSymbol = fromString (constructorLabel (FTA.transitionSymbol transition))}

    -- The key of 'Data.CFTA.Gen.fromDatatype': the declaration position of a
    -- constructor in its type, for the types of the constructors of the
    -- automaton, and the label text. A literal has no declared position.
    positions =
        Map.fromList
            [ (Text.pack (constructorLabel constructor), position)
            | description <- reachable (Set.fromList (map constructorType symbols)) Set.empty [describeType (Proxy @a)]
            , (position, constructor) <- zip [0 :: Int ..] (constructorsOf description)
            ]
    order (Symbol label) = (Map.findWithDefault 0 label positions, label)

    -- A label is found by its hash, then by the identity of the symbol, as
    -- 'Data.CFTA.Gen.Internal.Automaton.datatypeDecoder' does.
    decode = \term -> case decodeLabelled term of
        Just decoded -> decoded
        Nothing -> error "cfta-generator bug in Data.CFTA.Gen.Typing: the codec rejected a term of the language"
      where
        table =
            IntMap.fromListWith
                (<>)
                [ (hash symbol, [(symbol, constructor)])
                | constructor <- symbols
                , let symbol = fromString (constructorLabel constructor) :: Symbol
                ]
        decodeLabelled = decodeTerm @a <=< traverse (\symbol -> lookup symbol =<< IntMap.lookup (hash symbol) table)

{- | The descriptions of the needed types that a description reaches, each
once. A type that is not needed is not read: a field that no rule uses can
have a non-regular type, whose description reaches infinitely many types.
-}
reachable :: Set.Set TypeRep -> Set.Set TypeRep -> [Description] -> [Description]
reachable _ _ [] = []
reachable needed seen (description : rest)
    | Set.notMember typ needed || Set.member typ seen = reachable needed seen rest
    | otherwise = description : reachable needed (Set.insert typ seen) (children <> rest)
  where
    (typ, children) = case description of
        AtomicType atomic -> (atomic, [])
        AlgebraicType algebraic alternatives -> (algebraic, concatMap snd alternatives)

-- | The constructors of a type, in declaration order, and none for an atomic type.
constructorsOf :: Description -> [Constructor]
constructorsOf (AlgebraicType _ alternatives) = map fst alternatives
constructorsOf (AtomicType _) = []
