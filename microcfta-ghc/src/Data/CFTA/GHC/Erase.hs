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
  rigid.
* The list type, the pair type, and the unit type become Hectare's @List@,
  @Pair@, and @Unit@; another type constructor keeps its name, with its
  visible arguments.
* A type with another applied type variable (@m a@, @f b@), a tuple of more
  than two, a nested forall after an arrow, or a type-level literal has no
  Hectare type.

The erased types only propose candidates. GHC checks every candidate with
its real type, so an erased type that is too general or too specific costs
time or completeness, never soundness.
-}
module Data.CFTA.GHC.Erase (
    erase,
    anyResult,
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text

import Data.CFTA.Gen.Synthesis (Type (..))
import GHC.Builtin.Types (listTyCon, unitTyCon)
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Core.TyCon (isBoxedTupleTyCon, tyConArity)
import qualified GHC.Core.Type as GHC
import GHC.Tc.Utils.TcType (tcSplitNestedSigmaTys)
import GHC.Types.Name (getOccString)
import GHC.Types.Var (TyVar)

{- | A GHC type as a type of Hectare, or 'Nothing' when it has none. The
function names the free type variables; a free type variable that it does
not name gives 'Nothing'.
-}
erase :: (TyVar -> Maybe Text) -> GHC.Type -> Maybe Type
erase rigid typ = go (Map.fromList (zip bound [0 :: Int ..])) body
  where
    (bound, theta, body) = tcSplitNestedSigmaTys (GHC.expandTypeSynonyms typ)
    containers =
        [ variable
        | predicate <- theta
        , Just (className, [argument]) <- [getClassPredTys_maybe predicate]
        , getOccString className `elem` ["Foldable", "Traversable"]
        , Just variable <- [GHC.getTyVar_maybe argument]
        ]
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
        | otherwise = Nothing

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
