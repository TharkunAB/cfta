-- | Typed interpretations of names in the shared refinement language.
module Data.CFTA.Lean.Theory (
    Theory,
    Definition (..),
) where

import Data.Text (Text)

import Data.CFTA.Formula (Formula, Name, Sort)

{- | A fixed interpretation of global names. Names must be unique.
The theory is part of the language's meaning.
-}
type Theory = [(Name, Definition)]

{- | A signature and its interpretation.

Lean expressions are trusted code supplied by the caller. Use 'Defined' for
a predicate whose body can also be inspected and lowered to another solver.
Native expressions can refer to imported Lean definitions. They cannot refer
to the generated names of other entries.
-}
data Definition
    = -- | A type constructor's arity and Lean expression, such as @List@.
      TypeConstructor Int Text
    | -- | Argument types, result type, and a Lean function expression.
      Function [Sort] Sort Text
    | -- | Argument types and a Lean predicate expression with result @Prop@.
      Predicate [Sort] Text
    | -- | Formal parameters and a predicate body in the shared language.
      Defined [(Name, Sort)] Formula
    deriving (Eq, Show, Read)
