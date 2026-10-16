{-# LANGUAGE PatternSynonyms #-}

{- | Typed languages with variables, from typing rules for each constructor.

The language is the closed terms of a 'HasFTA' datatype that have one of some
types, with a nesting of at most a bound. Each rule gives a type to a
constructor of the datatype, by its name. A variable has a de Bruijn index:
the index 0 is the innermost binder. The environment of a term is the list
of the types of its binders, innermost first.

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
closed = fromTypingRules 3 [TInt, TBool] typedRules
@

'fromTypingRules' builds the automaton whose states are an environment, a
type, and the nesting that remains, and reads it as 'Data.CFTA.Gen.fromAutomaton'
does. The symbols are the labels of 'Data.CFTA.Gen.fromDatatype', so a value
and its term share one rank, and 'Data.CFTA.Gen.rankOfValue' finds it. The
ranks order the constructors of a node by arity, then in declaration order,
as for 'Data.CFTA.Gen.fromDatatype'. This holds for the constructors of each
type that the datatype reaches. A literal has no declared position, so the
literals of one type follow the order of their labels. For numbers that are
not negative and have at most nine digits, that is the numeric order.
'Data.CFTA.Gen.fromDatatype' orders literals as their domain lists them.

Limits:

* A field that holds a subterm has the type of the datatype. A field of
  another type holds one fixed value. So a family of mutually recursive
  types is not a language here.
* The bound is on the nesting, not on the binders, so the language is
  finite. The automaton has about T^(D + 1) environments for T types and the
  bound D.
-}
module Data.CFTA.Gen.Typing (
    Rule,
    Child,
    rule,
    variable,
    subterm,
    value,
    TypingError (..),
    fromTypingRules,
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
import Data.Typeable (typeRep)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
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
    deriving (Eq, Show)

-- | A state of the automaton: the root, a term of a type in an environment with the nesting that remains, or one value.
data Goal ty = Root | Goal ![ty] !ty !Int | Fixed !(Term Constructor)
    deriving (Eq, Ord)

{- | The closed terms of the datatype that have one of the types, with a
nesting of at most the bound. A constructor with a subterm field uses one
level of the nesting, as for 'Data.CFTA.Gen.Refinement.recurUpTo'. A constructor without
a rule is not in the language.
-}
fromTypingRules :: forall a ty. (HasFTA a, Ord ty) => Depth -> [ty] -> [Rule ty] -> Either TypingError (Gen Symbol a)
fromTypingRules (Depth bound) roots rules = do
    let unknown = nubOrd [name | name <- map ruleName rules, Map.notMember name constructors]
    unless (null unknown) $ Left $ UnknownConstructors unknown (map constructorName declared)
    mapM_ checked [(name, children) | Rule name children _ <- rules]
    rows <- close Map.empty [Root]
    -- Each state has a row, and each label has the arity of its constructor.
    let automaton =
            fromRight (error "cfta-generator bug in Data.CFTA.Gen.Typing: an invalid automaton") $ FTA.mkFTA Root (Map.toList rows)
        symbols = nubOrd [FTA.transitionSymbol transition | transitions <- Map.elems rows, transition <- transitions]
    pure $ case undecodableConstructor (null . decodeTerm @a) automaton of
        Just constructor -> Transparent $ Left $ UndecodableConstructor $ constructorName constructor
        Nothing -> decode symbols <$> Flat.fromAutomaton (order symbols) (Interned.fromRows Root (Map.map (map labelled) rows))
  where
    declared = case describeType (Proxy @a) of
        AlgebraicType _ alternatives -> map fst alternatives
        AtomicType _ -> []
    constructors = Map.fromList [(constructorName constructor, constructor) | constructor <- declared]
    ruleName (Rule name _ _) = name
    ruleName (Variable name _) = name

    close rows [] = Right rows
    close rows (state : pending)
        | Map.member state rows = close rows pending
        | otherwise = do
            transitions <- row state
            close (Map.insert state transitions rows) (concatMap FTA.transitionChildren transitions <> pending)

    row Root = concat <$> traverse (\typ -> row (Goal [] typ bound)) (nubOrd roots)
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
        nests children = remaining > 0 || null [() | Subterm _ _ <- children]
        transition alternative@(_, children) = do
            constructor <- checked alternative
            pure $ FTA.Transition constructor (map child children) noConstraint
        child (Subterm binds typ) = Goal (binds <> env) typ (remaining - 1)
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

    labelled transition = transition{FTA.transitionSymbol = fromString (constructorLabel (FTA.transitionSymbol transition))}

    -- The key of 'Data.CFTA.Gen.fromDatatype': the declaration position of a
    -- constructor in its type, for each type that the datatype reaches, and
    -- the label text. A literal has no declared position.
    order symbols =
        let needed = Set.fromList (map constructorType symbols)
            positions =
                Map.fromList
                    [ (Text.pack (constructorLabel constructor), position)
                    | alternatives <- reachable needed Set.empty [describeType (Proxy @a)]
                    , (position, (constructor, _)) <- zip [0 :: Int ..] alternatives
                    ]
         in \(Symbol label) -> (Map.findWithDefault 0 label positions, label)

    -- The constructors of each algebraic type in the descriptions and their
    -- fields, for the types in the typing rows only. A field that no rule
    -- uses can have a non-regular type, whose description reaches infinitely
    -- many types. The walk keeps the types that it saw.
    reachable _ _ [] = []
    reachable needed seen (AtomicType _ : pending) = reachable needed seen pending
    reachable needed seen (AlgebraicType typ alternatives : pending)
        | Set.notMember typ needed || Set.member typ seen = reachable needed seen pending
        | otherwise = alternatives : reachable needed (Set.insert typ seen) (concatMap snd alternatives <> pending)

    -- A label is found by its hash, then by the identity of the symbol, as
    -- 'Data.CFTA.Gen.Internal.Automaton.datatypeDecoder' does.
    decode symbols = \term -> case decodeLabelled term of
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
