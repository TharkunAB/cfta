# Changelog

## 0.1.0.0 - Unreleased

Initial version, for GHC 9.14 only.

- `Data.CFTA.Concat`: `symbolic` compiles a monomorphic Haskell predicate or
  measure with the concat plugin to the `Formula` or `Expr` of the refinement
  logic, for the contracts, measures, and conditions of the refinement
  generators of `cfta-generator`.
- `Data.CFTA.Concat.FormulaCat`: the category `FormulaCat` and the type family
  `Sym` of the symbolic values: `Expr` for `Integer` and `Int`, `Formula` for
  `Bool`, and pairs and functions of these.
- `Data.CFTA.Concat.Measure`: the uninterpreted measure `len` as a primitive
  of the category, and the orphan instance `OkType [a]` of the plugin's class
  `ConCat.OkType.OkType`.
