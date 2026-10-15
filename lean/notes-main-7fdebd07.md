# Main 7fdebd07: typed derived refinement names

Source main is `7fdebd07322fbd19316f185259c8277d1d24d93d`.
The preserving merge is `a3e68610`. The previous source is `88998669`.
Full library scope remains active. The optimized interned core remains.

## Source interface

`Data.CFTA.Gen.Refinement.Derive` now exports `NodeView`, `FieldKind`,
`AnyNode`, `MeasureRecord`, `Single`, `NoMeasures`, and `measuresAt`.
`HasLTA` has associated `Node` and `Measures` type constructors.
`Invariant node measures` uses typed node views and typed measure records.
`measureOf` returns a single measure. `measuresOf` returns a typed record.

The string-based `Annotation` backend moved to the exposed
`Data.CFTA.Gen.Refinement.Derive.Internal` module. `Measures`, `Child`, and
`NodeIntegers` moved to `Data.CFTA.Refinement.Symbolic.Internal`.
The two Internal modules are outside the stated PVP contract.

The generic measure-record default lists selector names and fields in
left-to-right product order. The generic node-view default selects sum
constructors by position and consumes product children in order.
`checkNodeView` checks constructor count, declaration order, arity, and field
kinds. It does not compare constructor names. `AnyNode` can omit this check.
Only a field whose type equals the root type is a direct self field.
The value evaluator tests atomic interpretation before direct-self recursion.

`invariantAnnotations` validates the view before it builds Expr callbacks
and translates measures and conditions. The value evaluator uses Integer
callbacks. Missing integers and measures retain partial error branches.
A custom instance does not acquire the generic default laws from its type.

## Remaining proof obligations

No existing Lean theorem directly covers the old public Derive translation.
Its interface descriptions are historical. Existing formula, generator,
solver, and Sized component semantics remain valid. They do not prove the
new public pipeline.

The new source bridges must establish:

- Generic measure-name order, field order, and record reconstruction.
  Include empty names, repeated names, and actual zip truncation.
- Generic node-view shape and construction. Include sums, products,
  scalar and record fields, positional selection, and NodeMismatch order.
- Direct-self classification, atomic precedence, and supported mutual or
  foreign recursive fields. Do not infer measures for unsupported fields.
- Agreement of Expr annotations and Integer evaluation for each invariant.
  A rank-polymorphic Symbolic callback alone does not prove this law.
- Named function preparation, sorts, missing measures, and solver contracts.
- Accepted values, counts, ranks, declaration order, depth bounds, and codec
  correspondence through the unchanged annotation backend.

## Validation and preservation

The strict required Nix build passes all components with `-Werror`.
All six suites pass 714 examples plus golden checks. Fourmolu passes the
five changed Haskell files. Cabal-gild passes all four active package files.
Evidence is in `/tmp/mcfta-current-secondary-main-7fde-*`.
The source review records exact field and callback behavior.

The merge changes ten package files and adds two of them. It changes no
Equality, Enumeration, Interned, or Sized implementation. Existing repairs
remain as the constructor changelog entry and the caller reproduction comment.
All older Lean definitions, counterexamples, and marked drafts remain.
