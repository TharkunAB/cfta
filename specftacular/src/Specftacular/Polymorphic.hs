{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{- | Runtime type instances for parametric signature constants.
Reuse existing type constructors and check every argument kind.
-}
module Specftacular.Polymorphic (applyType, functionType, specialiseDynamic) where

import Data.Dynamic (Dynamic (..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Type.Reflection (SomeTypeRep (..), (:~~:) (HRefl))
import qualified Type.Reflection as TR
import Type.Reflection.Unsafe (mkTrApp)
import Unsafe.Coerce (unsafeCoerce)

{- | Each key is an exact carrier TypeRep. Each value is its verified instance.
Build this map separately for every occurrence of a signature constant.
-}
type Substitution = Map SomeTypeRep SomeTypeRep

{- | Apply an existing type constructor. Check the argument kind first.
This operation does not create a TyCon or infer its kind from its name.
-}
applyType :: SomeTypeRep -> SomeTypeRep -> Either String SomeTypeRep
applyType (SomeTypeRep fun) (SomeTypeRep arg) =
    case TR.typeRepKind fun of
        TR.Fun domainKind resultKind ->
            case TR.eqTypeRep (TR.typeRepKind domainKind) (TR.typeRep @Type) of
                Nothing -> Left "type constructor domain kind is not lifted"
                Just HRefl ->
                    case TR.eqTypeRep (TR.typeRepKind resultKind) (TR.typeRep @Type) of
                        Nothing -> Left "type constructor result kind is not lifted"
                        Just HRefl ->
                            case TR.eqTypeRep domainKind (TR.typeRepKind arg) of
                                Just HRefl -> Right (SomeTypeRep (mkTrApp fun arg))
                                Nothing -> Left "type constructor argument has the wrong kind"
        _ -> Left "type constructor does not have a function kind"

-- | Construct an ordinary lifted function type.
functionType :: SomeTypeRep -> SomeTypeRep -> Either String SomeTypeRep
functionType (SomeTypeRep arg) (SomeTypeRep result) =
    case TR.eqTypeRep (TR.typeRepKind arg) (TR.typeRep @Type) of
        Nothing -> Left "function argument is not a lifted type"
        Just HRefl ->
            case TR.eqTypeRep (TR.typeRepKind result) (TR.typeRep @Type) of
                Nothing -> Left "function result is not a lifted type"
                Just HRefl -> Right (SomeTypeRep (TR.Fun arg result))

{- | Rebuild only applications and arrows. Reuse all other representations.
A carrier replacement must have the same kind as its original carrier.
-}
substitute :: Substitution -> SomeTypeRep -> Either String SomeTypeRep
substitute substitution original@(SomeTypeRep rep)
    | Just replacement@(SomeTypeRep rep') <- Map.lookup original substitution =
        case TR.eqTypeRep (TR.typeRepKind rep) (TR.typeRepKind rep') of
            Just HRefl -> Right replacement
            Nothing -> Left "carrier replacement has the wrong kind"
    | TR.Fun arg result <- rep = do
        arg' <- substitute substitution (SomeTypeRep arg)
        result' <- substitute substitution (SomeTypeRep result)
        functionType arg' result'
    | TR.App fun arg <- rep = do
        fun' <- substitute substitution (SomeTypeRep fun)
        arg' <- substitute substitution (SomeTypeRep arg)
        applyType fun' arg'
    | otherwise = Right original

{- | Apply one consistent carrier substitution to a constant. The caller
must check the signature against its annotation. A to Acc must be abstract
parameters. This operation must not change generated variables or captured
class dictionaries. The cast changes only the parametric value's type tag.
-}
specialiseDynamic :: Substitution -> Dynamic -> Either String Dynamic
specialiseDynamic substitution (Dynamic original value) = do
    actual <- substitute substitution (SomeTypeRep original)
    case actual of
        SomeTypeRep rep ->
            case TR.eqTypeRep (TR.typeRepKind rep) (TR.typeRep @Type) of
                Nothing -> Left "specialised value is not a lifted type"
                Just HRefl -> Right (Dynamic rep (unsafeCoerce value))
