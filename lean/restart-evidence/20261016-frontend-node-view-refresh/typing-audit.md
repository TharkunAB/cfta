# Typing frontend audit

Reviewed at 2026-10-16 13:08 CEST. This is a source and test review.
No Cabal build, Haskell execution, Lake build, network request, or Git mutation
was run for this audit. No Haskell or Lean source file was changed.

## Reviewed revisions

- Current checkout: `9aaffc9574cc63adba23ed168e0aa768f033f0a7`.
- Current source main: `999c04a54e5f27d77d66d2026f117ef3e86d0e51`.
- Previous source baseline: `ccebf0f7`.
- Node-rule change: `9968bd8e2c2f314b9fe0895cd381867fa7d74c37`.
  Main adopted it in PR #61, merge `d8c7ff18169ffc81421bcbe43df987c1e1dce93d`.
- Negative-bound repair: `443e345876ac2628c1affe15a2b3a156371ba178`.
  Main adopted it in PR #62, merge `999c04a5`.

Read-only `git merge-base --is-ancestor` checks confirm that both changes and
the source-main merge are ancestors of the current checkout. The reviewed
Typing and Derive implementation files match source main byte for byte.

## Haskell fix registry material: negative bounds

Failure: a negative `Nesting` or `Binders` bound could retain constructors
without any `Subterm` field. The old filter checked only `Subterm` fields.
For a nullary constructor its list of checks was empty, so `and []` was true.
A constructor with fixed fields only had the same problem. This admitted
leaves instead of rejecting an invalid public bound.

A minimal reproducer uses the node-rule API that was present immediately
before the repair:

```haskell
{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}
import GHC.Generics (Generic)
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Gen.Refinement.Derive (NodeView)
import Data.CFTA.Gen.Typing

data Leaf = Leaf
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (HasFTA)
data LeafNode e = LeafNode
  deriving stock Generic
  deriving anyclass NodeView

failure bound = either Just (const Nothing) $
  fromTypingRules @Leaf (Typing bound [] [()] [rule LeafNode ()])

-- At 443e3458^, both results are Nothing. The generator retains Leaf.
-- At 443e3458 and current main:
-- failure (Nesting (-1)) == Just (NegativeBound (Nesting (-1)))
-- failure (Binders (-1)) == Just (NegativeBound (Binders (-1)))
-- failure (Nesting 0)    == Nothing
```

These expectations follow directly from the source branches. This audit did
not execute the reproducer. The committed Hspec regression supplies the same
three checks with `Arith`: `TypingSpec.hs:464–468`, under the example
`"take a bound that is not negative"`.

The repair adds the two public checks at `Typing.hs:239–242` and the
`NegativeBound !Bound` constructor at `Typing.hs:209–210`. It runs before
`checkNodeShape`, static rule validation, and row construction.
`fromTypingRules` uses `typingAutomaton` at line 227. Thus a negative bound
also takes precedence over a bad node view. Bound zero remains valid.

Exactly three files changed in the fix commit:

1. `cfta-generator/src/Data/CFTA/Gen/Typing.hs`.
2. `cfta-generator/test/Data/CFTA/Gen/TypingSpec.hs`.
3. `cfta-generator/CHANGELOG.md`.

The same commit corrects the size explanation at `Typing.hs:67–70`.
With at most B new binders per field and nesting D, a path can add B * D
binders, in addition to the fixed input environment. No local repair is
needed. The source repair and regression are already upstream.

## Node-rule order and validation

The new `Rule node ty` stores an actual node-view value rather than a string
and a list of fields (`Typing.hs:127–151`). The common arithmetic fixture
preserves its constructors, alternatives, result types, field order, and
variable-index encoding. Its `ArithNode` now serves both typing rules and
refinement invariants. The removed local copy in `TypedLanguageSpec.hs` is
the same constructor sequence.

The generic `nodeFields` implementation preserves declaration position:
the right sum branch adds the number of constructors in the left branch
(`Derive.hs:365–372`). Product fields remain left to right
(`Derive.hs:397–409`). `checkNodeShape` checks constructor counts, field
counts, and name prefixes in declaration order (`Derive.hs:579–620`).
Typing then resolves the actual position and checks every field, including
the arity (`Typing.hs:292–305`). A measure-record field yields `Nothing`
and fails `sequence fields`; it cannot become an unchecked typing child.

The source row schedule remains ordinary alternatives first, then variable
alternatives in rule order and increasing matching environment position
(`Typing.hs:269–287`). The environment is still `binds <> env` and only a
`Subterm` consumes nesting. Root types still use `nubOrd`; fixed trees still
retain their entire encoded subtree.

The complete implementation suffix from `fromConstructorAutomaton ::`
through `constructorsOf` is byte-identical to `ccebf0f7`. This audit checked
that equality directly. The ordering and needed-type discovery regressions
are retained at `TypingSpec.hs:484–497`:

- Helper type `data Letter = Z | A`, supplied rules in order A then Z:
  both the typed generator and `fromDatatype` expect `[Lit Z, Lit A]`.
- An unused field of the non-regular `Nested` type does not stop generation;
  the two used leaf rules expect `[Plain, Other]`.

No new constructor-order or field-order defect was found in the reviewed
generic implementation. This does not establish arbitrary handwritten
`NodeView` instance laws or datatype codec correctness.

## Observable stricter callback validation

There is one validation-order change beyond the new error type.
Before `9968bd8e`, variable alternatives were filtered by `allowed` before
their runtime field validation. The new code checks reached alternatives
first and filters afterward (`Typing.hs:269–277`). Ordinary rules already
had unconditional static validation, so this difference concerns variable
callbacks.

A concrete case, using the existing arithmetic fixture, is:

```haskell
Typing (Nesting 0) [IntType] [IntType]
  [ rule (NumNode (value (0 :: Int))) IntType
  , variable (\_ _ -> NumNode (subterm [] IntType))
  ]
```

The callback puts a `Subterm` in the `Int` field of `Num`. Current main
reports `FieldMismatch "Num"`, even though nesting zero would discard that
alternative. Under the old string API, the corresponding callback
`variable "Num" (\_ _ -> [subterm [] IntType])` was filtered out, and the
valid `Num 0` rule remained. With no matching input/environment position,
the callback is still not invoked. This is stricter reached validation,
not evidence of an incorrect language for valid rules. The existing
callback mismatch regression at `TypingSpec.hs:478–483` checks a reached
bad fixed value, but does not isolate the bound-pruned case above.

The direct fixed-self exclusion is retained at `Typing.hs:303–305`.
Tests at `TypingSpec.hs:472–483` still reject a foreign subterm, a fixed
value of the wrong type, fixed open or deep target-datatype subtrees, and a
bad variable field. No regression of that repair was found.

## Proof scope and validation limits

The existing `SourceTypingRules` component models resolved candidate rows.
It explicitly separates frontend validation and codecs. Its internal
nonpositive nesting behavior is still appropriate for those candidate
rows; it is not the new public `NegativeBound` API behavior. The old
resolved variable schema also fixes its constructor label, whereas the
new Haskell callback returns a node value and can choose its constructor.
A source adapter must resolve that actual returned constructor per reached
index/type before invoking the row semantics. No whole new frontend
correspondence follows from the existing Lean Audit.

Finite total rule lists, callbacks, encoded fixed trees, lawful `NodeView`
instances, codecs, lazy import, ambiguity handling, and concrete label
identity remain separate source assumptions or adapter obligations.
This review found no additional concrete Haskell repair to request.

## Reviewed source hashes

SHA-256 at the reviewed checkout:

```text
9ebe8d3da413fc672a1323352bb34a7f30c89ae90ec245b77fb685ff0f95e749  cfta-generator/src/Data/CFTA/Gen/Typing.hs
380b0c64a1a1196a9a29b6f5f984a838e2d9399ca44ecb21a1a99e2120f7fe12  cfta-generator/test/Data/CFTA/Gen/TypingSpec.hs
a0d5dd82622d307e9a0d18b11ac981cdcf90fe0591d82ec8dc8733e57fa9a901  cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs
df3717bae2462cb0c0d3b6d558ef0506799f65c0c54c6869bc5890cc14c48f60  cfta-generator/src/Data/CFTA/Gen/Refinement/Derive/Internal.hs
```
