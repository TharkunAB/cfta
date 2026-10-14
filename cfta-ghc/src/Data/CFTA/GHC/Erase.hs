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

The erased types only propose candidates. GHC checks every candidate with
its real type, so an erased type that is too general or too specific costs
time or completeness, never soundness.
-}
module Data.CFTA.GHC.Erase (
    erase,
    anyResult,
    higherKinded,
    typeHeads,
) where

import Data.List (nubBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text

import Data.CFTA.Gen.Synthesis (Type (..))
import GHC.Builtin.Types (liftedTypeKind, listTyCon, unitTyCon)
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
erase rigid typ = go (Map.fromList (zip bound [0 :: Int ..])) body
  where
    (bound, theta, body) = tcSplitNestedSigmaTys (GHC.expandTypeSynonyms typ)
    containers = listVariables theta
    go :: Map TyVar Int -> GHC.Type -> Maybe Type
    go names t
        | Just variable <- GHC.getTyVar_maybe t =
            case Map.lookup variable names of
                Just index -> Just (TVar (Text.pack ('t' : show index)))
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
            TCons "List" . pure <$> go names argument
        | (function, arguments@(_ : _)) <- GHC.splitAppTys t
        , Just variable <- GHC.getTyVar_maybe function
        , Map.notMember variable names =
            TCons <$> rigid variable <*> traverse (go names) arguments
        | otherwise = Nothing

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
so the candidates that it makes flood the search.
-}
anyResult :: Type -> Bool
anyResult typ = case result typ of
    TVar variable -> variable `notElem` concatMap variables (parameters typ)
    _ -> False
  where
    result (TFun _ rest) = result rest
    result other = other
    parameters (TFun parameter rest) = parameter : parameters rest
    parameters _ = []
    variables (TVar variable) = [variable]
    variables (TFun argument rest) = variables argument <> variables rest
    variables (TCons _ arguments) = concatMap variables arguments
