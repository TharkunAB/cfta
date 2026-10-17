{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate the scalar node views used by typing rules and refinements.
module Data.CFTA.TH (deriveNode) where

import Control.Monad (forM, unless, when)
import Data.Char (isUpper)
import Data.Maybe (isJust)
import GHC.Generics (Generic)
import Language.Haskell.TH

import Data.CFTA.Gen.Refinement.Derive (NodeView)

{- | Generate a node view after a source datatype declaration:

@
data Expr = Lit Int | Add Expr Expr
    deriving (Generic)

\$(deriveNode ''Expr)
@

This declares @ExprNode e = LitNode e | AddNode e e@, derives 'Generic',
and declares its 'NodeView' instance. Enable @TemplateHaskell@ and
@DeriveGeneric@ in the module that contains the splice.

Constructor order and field count stay the same. Record fields become
positional fields. Source type parameters and field types are replaced by
the single parameter @e@. The source datatype still needs its usual
@HasFTA@ instance when used with the generator APIs.

This operation accepts ordinary data and newtype declarations. It rejects
name collisions, symbolic names, datatype contexts, existential or
constrained constructors, GADTs, type synonyms, and data families. Write a
manual view for records of measures or for other supported source forms.
-}
deriveNode :: Name -> Q [Dec]
deriveNode source = do
    (context, constructors) <-
        reify source >>= \case
            TyConI (DataD context _ _ _ constructors _) -> pure (context, constructors)
            TyConI (NewtypeD context _ _ _ constructor _) -> pure (context, [constructor])
            _ -> unsupported "type synonyms and data families"
    unless (null context) $ unsupported "datatype contexts"
    view <- generatedName lookupTypeName source
    child <- newName "e"
    alternatives <- forM constructors $ \constructor -> do
        (name, arity) <- case constructor of
            NormalC name fields -> pure (name, length fields)
            RecC name fields -> pure (name, length fields)
            InfixC _ name _ -> pure (name, 2)
            ForallC{} -> unsupported "existential or constrained constructors"
            GadtC{} -> unsupported "GADT constructors"
            RecGadtC{} -> unsupported "GADT constructors"
        name' <- generatedName lookupValueName name
        pure $ NormalC name' $ replicate arity (Bang NoSourceUnpackedness NoSourceStrictness, VarT child)
    pure
        [ DataD [] view [PlainTV child BndrReq] Nothing alternatives [DerivClause Nothing [ConT ''Generic]]
        , InstanceD Nothing [] (AppT (ConT ''NodeView) (ConT view)) []
        ]
  where
    unsupported feature =
        fail $ "deriveNode " <> nameBase source <> ": " <> feature <> " need a manual node view"
    generatedName lookupName name = case nameBase name of
        first : _ | isUpper first -> do
            let generated = nameBase name <> "Node"
            existing <- lookupName generated
            when (isJust existing)
                $ fail
                $ "deriveNode " <> nameBase source <> ": " <> generated <> " is already in scope; hide or rename the existing name"
            pure $ mkName generated
        _ -> unsupported "symbolic names"
