{-# LANGUAGE OverloadedStrings #-}

{- | GHC types as the types of Hectare, with the class contexts erased.

Hectare's automaton ("Data.CFTA.Gen.Synthesis") has first-order types: type
variables, function types, and type constructors with arguments. A GHC type
becomes such a type after these rules:

* The type synonyms are expanded, so @String@ is @[Char]@.
* The foralls and contexts at the top, also the nested ones of a class
  method, are dropped. A bound type variable becomes a Hectare type
  variable, which Hectare instantiates at each use.
* A bound type variable of class @Foldable@ or @Traversable@ becomes the
  list type, as in the Hoogle+ library: @length :: Foldable t => t a -> Int@
  becomes @[a] -> Int@.
* A free type variable (a skolem of the context, or a unification variable)
  becomes a constant type, named by the caller, so that Hectare treats it as
  rigid. Applied to arguments (@f a@, with @f@ of the context), it becomes a
  type constructor of that name with those arguments.
* The list type, the pair type, and the unit type become Hectare's @List@,
  @Pair@, and @Unit@; another type constructor keeps its name, with its
  visible arguments.
* A type with another applied bound type variable (@m a@ in the type of
  @(>>=)@), a tuple of more than two, a nested forall after an arrow, or a
  type-level literal has no Hectare type. "Data.CFTA.GHC.Fits" first
  replaces such a variable by the type heads of the query
  ('higherKinded', 'typeHeads').

In the curried encoding of Hectare ('eraseCurried'), every applied bound
type variable of kind @* -> *@ stays a variable of that kind, as the type
constructor @?Monad t0@ applied to its argument. The text after the @?@
names its classes ('curriedClasses'), so that Hectare can take it at any
type head of the domain of those classes ('eraseHead'): @?Foldable t0@ for
@length@, @?Applicative t1@ and @?Traversable t0@ for @traverse@,
@?Applicative,Foldable t0@ for a variable with both classes, and @? t0@ for
a variable with no class. A bound type variable of kind @Type@ with classes
that the instances decide becomes the type constant @?Ord t1@, by the names
of those classes ('typeClasses'), so that Hectare can take it at any type of
the domain of those classes: @?Num t0@ for the @a@ of @sum@. A variable of
kind @Type@ without such a class stays a Hectare type variable.

The erased types only propose candidates. GHC checks every candidate with
its real type, so an erased type that is too general or too specific costs
time or completeness, never soundness.
-}
module Data.CFTA.GHC.Erase (
    erase,
    eraseCurried,
    eraseHead,
    curriedClasses,
    typeClasses,
    classKey,
    anyResult,
    higherKinded,
    typeHeads,
) where

import Data.List (nub, nubBy, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as Text

import Data.CFTA.Gen.Synthesis (Type (..))
import GHC.Builtin.Types (liftedTypeKind, listTyCon, unitTyCon)
import GHC.Core.Class (Class)
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCon (isBoxedTupleTyCon, tyConArity)
import qualified GHC.Core.Type as GHC
import GHC.Tc.Utils.TcType (tcSplitNestedSigmaTys)
import GHC.Types.Name (getOccString)
import GHC.Types.Var (TyVar, tyVarKind)

{- | A GHC type as a type of Hectare, or 'Nothing' when it has none. The
function names the free type variables; a free type variable that it does
not name gives 'Nothing'.
-}
erase :: (TyVar -> Maybe Text) -> GHC.Type -> Maybe Type
erase = eraseWith Nothing

{- | 'erase' for the curried encoding: an applied bound type variable of kind
@* -> *@ becomes a variable of that kind, the type constructor @?C tN@ with
the names of its classes for @C@ ('curriedClasses'), not the list type. A
bound type variable of kind @Type@ with classes that the first function
decides becomes the type constant @?C tN@ with the names of those classes
for @C@ ('typeClasses').
-}
eraseCurried :: (Class -> Bool) -> (TyVar -> Maybe Text) -> GHC.Type -> Maybe Type
eraseCurried decided = eraseWith (Just decided)

-- | 'erase', or with the decided classes 'eraseCurried'.
eraseWith :: Maybe (Class -> Bool) -> (TyVar -> Maybe Text) -> GHC.Type -> Maybe Type
eraseWith decision rigid typ = go (Map.fromList (zip bound [0 :: Int ..])) body
  where
    (bound, theta, body) = tcSplitNestedSigmaTys (GHC.expandTypeSynonyms typ)
    curried = isJust decision
    -- In the curried encoding, only a bound variable is a variable of kind
    -- \* -> *: a rigid one of the context stays a type constructor.
    containers
        | curried = filter ((`eqType` headKind) . tyVarKind) bound
        | otherwise = listVariables theta
    go :: Map TyVar Int -> GHC.Type -> Maybe Type
    go names t
        | Just variable <- GHC.getTyVar_maybe t =
            case Map.lookup variable names of
                Just index
                    | Just decided <- decision
                    , tyVarKind variable `eqType` liftedTypeKind
                    , classes@(_ : _) <- filter decided (classesOf theta variable) ->
                        Just (TCons ("?" <> classKey classes <> " t" <> Text.pack (show index)) [])
                    | otherwise -> Just (TVar (Text.pack ('t' : show index)))
                Nothing -> (`TCons` []) <$> rigid variable
        | Just (argument, result) <- GHC.splitVisibleFunTy_maybe t = TFun <$> go names argument <*> go names result
        | Just (constructor, arguments) <- GHC.splitTyConApp_maybe t =
            let visible = GHC.filterOutInvisibleTypes constructor arguments
             in case () of
                    _
                        | constructor == listTyCon -> TCons "List" <$> traverse (go names) visible
                        | constructor == unitTyCon -> Just (TCons "Unit" [])
                        | isBoxedTupleTyCon constructor && tyConArity constructor == 2 -> TCons "Pair" <$> traverse (go names) visible
                        | isBoxedTupleTyCon constructor -> Nothing
                        | otherwise -> TCons (Text.pack (getOccString constructor)) <$> traverse (go names) visible
        | Just (function, argument) <- GHC.splitAppTy_maybe t
        , Just variable <- GHC.getTyVar_maybe function
        , variable `elem` containers =
            TCons (if curried then higherName names variable else "List") . pure <$> go names argument
        | (function, arguments@(_ : _)) <- GHC.splitAppTys t
        , Just variable <- GHC.getTyVar_maybe function
        , Map.notMember variable names =
            TCons <$> rigid variable <*> traverse (go names) arguments
        | otherwise = Nothing

    -- The name of a variable of kind * -> * in the curried encoding.
    higherName names variable =
        "?"
            <> classKey (classesOf theta variable)
            <> " t"
            <> Text.pack (show (Map.findWithDefault 0 variable names))

{- | A type of kind @Type -> Type@ as a type of Hectare with one argument less
than its arity: @Maybe@ as @Maybe@, @Either e@ as @Either@ applied to @e@,
and a rigid @f@ of the context as the constant that the function names. A
type variable that the function does not name becomes a Hectare type
variable. A tuple of more than two has no Hectare type. A type constructor
applied to all its arguments, as @Maybe a@ or @()@, is a type of kind @Type@
in the same way.
-}
eraseHead :: (TyVar -> Maybe Text) -> GHC.Type -> Maybe Type
eraseHead rigid head'
    | Just variable <- GHC.getTyVar_maybe head' = (`TCons` []) <$> rigid variable
    | Just (constructor, arguments) <- GHC.splitTyConApp_maybe head' =
        let visible = GHC.filterOutInvisibleTypes constructor arguments
            name
                | constructor == listTyCon = Just "List"
                | constructor == unitTyCon = Just "Unit"
                | isBoxedTupleTyCon constructor && tyConArity constructor == 2 = Just "Pair"
                | isBoxedTupleTyCon constructor = Nothing
                | otherwise = Just (Text.pack (getOccString constructor))
         in TCons <$> name <*> traverse argument (zip [0 :: Int ..] visible)
    | otherwise = Nothing
  where
    argument (index, t)
        | Just variable <- GHC.getTyVar_maybe t, Nothing <- rigid variable = Just (TVar (Text.pack ('x' : show index)))
        | otherwise = erase rigid t

{- | The bound type variables of kind @Type -> Type@ of a type, as
'eraseCurried' names them: the names of their classes, and the classes.
-}
curriedClasses :: GHC.Type -> [(Text, [Class])]
curriedClasses typ =
    [ (classKey classes, classes)
    | variable <- bound
    , tyVarKind variable `eqType` headKind
    , let classes = classesOf theta variable
    ]
  where
    (bound, theta, _) = tcSplitNestedSigmaTys (GHC.expandTypeSynonyms typ)

{- | The bound type variables of kind @Type@ of a type with classes that the
function decides, as 'eraseCurried' names them: the names of those classes,
and the classes.
-}
typeClasses :: (Class -> Bool) -> GHC.Type -> [(Text, [Class])]
typeClasses decided typ =
    [ (classKey classes, classes)
    | variable <- bound
    , tyVarKind variable `eqType` liftedTypeKind
    , classes@(_ : _) <- [filter decided (classesOf theta variable)]
    ]
  where
    (bound, theta, _) = tcSplitNestedSigmaTys (GHC.expandTypeSynonyms typ)

-- | The classes of the constraints on one type variable alone in a context, each once.
classesOf :: [GHC.PredType] -> TyVar -> [Class]
classesOf theta variable =
    nub
        [ cls
        | predicate <- theta
        , Just (cls, [argument]) <- [getClassPredTys_maybe predicate]
        , GHC.getTyVar_maybe argument == Just variable
        ]

-- | The names of classes, sorted and separated by commas.
classKey :: [Class] -> Text
classKey = Text.intercalate "," . sort . map (Text.pack . getOccString)

{- | The type variables of class @Foldable@ or @Traversable@ in a context:
'erase' makes them lists.
-}
listVariables :: [GHC.PredType] -> [TyVar]
listVariables theta =
    [ variable
    | predicate <- theta
    , Just (className, [argument]) <- [getClassPredTys_maybe predicate]
    , getOccString className `elem` ["Foldable", "Traversable"]
    , Just variable <- [GHC.getTyVar_maybe argument]
    ]

{- | The bound type variables of kind @Type -> Type@ of a type that 'erase'
does not make lists: @f@ in the type of @fmap@ and @m@ in the type of
@(>>=)@, not @t@ in the type of @length@.
-}
higherKinded :: GHC.Type -> [TyVar]
higherKinded typ = [variable | variable <- bound, tyVarKind variable `eqType` headKind, variable `notElem` listVariables theta]
  where
    (bound, theta, _) = tcSplitNestedSigmaTys typ

{- | The type heads of kind @Type -> Type@ in types, each once: @Maybe@ in
@Maybe a@, @Either e@ in @Either e a@, @[]@ in @[a]@, and @f@ in @f a@.
-}
typeHeads :: [GHC.Type] -> [GHC.Type]
typeHeads = nubBy eqType . concatMap (heads . GHC.expandTypeSynonyms)
  where
    heads t
        | Just (argument, result) <- GHC.splitVisibleFunTy_maybe t = heads argument <> heads result
        | otherwise = case GHC.splitAppTys t of
            (function, arguments@(_ : _)) ->
                [head' | let head' = GHC.mkAppTys function (init arguments), GHC.typeKind head' `eqType` headKind]
                    <> concatMap heads arguments
            _ -> []

-- | The kind @Type -> Type@.
headKind :: GHC.Kind
headKind = GHC.mkVisFunTyMany liftedTypeKind liftedTypeKind

{- | Whether the result of a type is a type variable that no parameter has, as
in @a@ and @a -> b@. With its class context erased, such a component (as
@mempty@, @read@, or @fromIntegral@) fits every hole, as @undefined@ does,
so the candidates that it makes flood the search. A type constant @?C tN@ of
'eraseCurried' is such a variable too.
-}
anyResult :: Type -> Bool
anyResult typ = case variable (result typ) of
    Just name -> name `notElem` concatMap variables (parameters typ)
    Nothing -> False
  where
    result (TFun _ rest) = result rest
    result other = other
    parameters (TFun parameter rest) = parameter : parameters rest
    parameters _ = []
    variable (TVar name) = Just name
    variable (TCons name []) | "?" `Text.isPrefixOf` name = Just name
    variable _ = Nothing
    variables (TFun argument rest) = variables argument <> variables rest
    variables other@(TCons _ arguments) = maybe (concatMap variables arguments) pure (variable other)
    variables other = maybe [] pure (variable other)
