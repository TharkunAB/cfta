# Changelog

## 0.1.0.0 - Unreleased

Initial release.

- `Data.CFTA.Liquid`: the translation of Liquid Haskell specifications, as
  Liquid Haskell verifies them, into the annotations of
  `Data.CFTA.Gen.Refinement.Derive`. `deriveLTAFromLiquid` and
  `liquidTranslation` take a target: an alias without parameters, or a
  datatype. The translation reads `data` specifications with abstract
  refinements and the built-in list, `measure` specifications with their
  equations (integers, Booleans, and constructors of enumerations), and
  `type` and `predicate` aliases with parameters. A refinement of the
  elements of a child that is a conjunction of linear order relations gives
  derived measures: the least and the greatest element. A Boolean measure
  that the target requires at the root, and that holds exactly when a
  condition holds at each node, becomes a contract. The functions are pure
  over the text of the specifications, which the parser of
  `liquidhaskell-boot` reads without a GHC session. A part that the
  translation cannot translate exactly gives `Untranslatable` with its
  position and the reason.
- `Data.CFTA.Liquid.TH`: `liquidSpecifications`, the specifications of the
  current module, read and parsed when the module compiles.
