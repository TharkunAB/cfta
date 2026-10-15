# Changelog

## 0.1.0.0 - Unreleased

Initial release.

- `Data.CFTA.Liquid`: the translation of the Liquid Haskell specification of
  a datatype (its `data` specification, one `measure`, and refinement
  aliases) into the annotations of `Data.CFTA.Gen.Refinement.Derive`.
  `liquidAnnotations` and `deriveLTAFromLiquid` are pure over the text of the
  specifications, which the parser of `liquidhaskell-boot` reads without a GHC
  session. A part that the translation cannot translate exactly gives
  `Untranslatable` with its place and the reason.
- `Data.CFTA.Liquid.TH`: `liquidSpecifications`, the specifications of the
  current module, read and parsed when the module compiles.
