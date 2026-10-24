# Generated node views: independent upstream source review

Reviewed at 2026-10-24 03:26:24 CEST. Status: SOURCE REVIEW CLEAR. No concrete implementation defect was found. No repair is proposed. This is an independent implementation/document review, not a compiler run or a proof of Template Haskell or GHC.

The exact comparison is `0db62d26b87e8e55b6c2719f6312ece6f93ed31b` → `c4f7319acf84213fccc8ea389487d4176e4f0b62` (merge of PR113). origin/main resolved to the target at the initial read. All source reads use the fixed target Git object, not a possibly changing working tree. I read the complete73-line implementation,61-line design note,58-line package README, root README,127-line test, package metadata and all10 changed-file diffs. The total diff has426 insertions and2 deletions; SHA256 is `bac8560e68b21614da6b88672101002b6252067b4fec585950197a61d414139f`. No compiler, test, repository edit, merge, Git mutation, network or board operation was performed.

`deriveNode :: Name → Q [Dec]` is an optional-package authoring helper. Its result is a new scalar observation datatype and a default-method `NodeView` instance. It does not derive HasFTA, an original-value decoder, an invariant, a typing relation or a semantic roundtrip theorem. The implementation leaves the existing core and generator bodies unchanged. Only cfta-th has a direct template-haskell dependency in the inspected package metadata; the package is added to cabal.project and the existing CI formatting/lint/metadata/all-package build path.

The exact generated shape agrees with the documentation. TH.hs38–45 accepts reified DataD/NewtypeD and rejects datatype contexts. TH.hs48–57 traverses constructors in their declared list order; NormalC and RecC retain field count, and a named InfixC has two fields. Every source field becomes the same fresh `e`, with no source type parameter, field type, selector, strictness or unpacking annotation copied. A record of parameterized or compound fields therefore still gets one scalar observation for each actual source field. TH.hs58–60 emits a DATA declaration with one parameter, derives Generic and declares NodeView with no overridden methods. A source newtype also produces a data view, as documented. No new user-facing datatype or method is substituted for the existing NodeView API.

The refusal paths are concrete. ForallC, GadtC and RecGadtC fail at the splice, rather than dropping existential/constructor constraints or result-index equations. Other reified forms, including synonyms and families, fail through the fallback. generatedName at TH.hs65–73 requires an uppercase initial name, appends Node, and checks the appropriate type/value namespace for an existing name before emitting it. Symbolic datatype or constructor names are refused. A named backtick constructor such as Together remains an ordinary uppercase name and becomes a positional TogetherNode. The type/constructor namespaces remain distinct, so an ordinary same-name data constructor can generate the usual same-name type/constructor pair. Existing imported or local generated-name collisions are deliberately refused.

The source field types are erased only in the observation view. Existing HasFTA support is still required for actual source values and recursive fields, as the README says. Accepting a source declaration for shape generation does not claim that every field type automatically has a useful generator. Source-specific records of measures remain manual: the generated fields are all Scalar, while the existing measured-record validation requires Record names on relevant recursive fields. An empty view has the expected empty shape; callers must not interpret that as a total buildNode operation for an invalid constructor index. The design note correctly requires EmptyDataDeriving for the generated empty Generic instance.

The relevant existing semantic boundary is explicit in the unchanged generator code:

- Refinement.Derive.hs323–341 obtains nodeShape/buildNode/nodeFields from Generic and GNode. Sum and product instances at353–427 keep constructor position and field order; a scalar e field fills from childValue and reads back Just e. A valid constructor position and exactly its expected children are the context for that observation roundtrip. It is not an isomorphism from the original source datatype to `View e`: source field types and values intentionally differ.
- datatypeConstructors at543–547 reads the original HasFTA description. checkNodeFields at592–625 compares constructor count, order, arity and the required source-name prefix; adding Node preserves that prefix. checkNodeView additionally verifies Scalar/Record field kinds. The splice does not bypass these checks.
- Typing.hs365–379 runs checkNodeShape before processing rules. Its checked rule at436–451 still validates actual nodeFields positions/counts and whether each Value, Drawn or Subterm has the corresponding source field type. Generated e fields do not weaken these source-type checks.
- Existing source encode/decode, annotation interpretation, counting and rank implementations are untouched. Counts/ranks agree with an equivalent manual scalar view through those same APIs; the splice does not prove that arbitrary rules or refinements are valid or sound. A TH-to-Generic-to-HasFTA correspondence proof would still have to establish the emitted shape and observation roundtrip, then connect them to the actual source encoding. Existing lower-level language proofs alone do not discharge that compiler boundary.

The committed tests are meaningful source evidence, but were not run in this review. Spec.hs92–100 compares generated/manual arithmetic values, cardinality, ranks and decode-after-rank for all38 values. Lines102–106 compare scalar-refinement values and unrank results. Lines108–114 check parameterized records, newtypes, named infix constructors, ordinary constructor order, an empty view and scalar field order. Lines116–123 contain FIVE compile-time refusal probes through recover: GADT, existential, symbolic, synonym and type-name clash. The design note's NINE diagnostics, repeated-process checks, README compilation and edit/recompile checks describe additional standalone validation; those claims are not established by the five committed refusal cases alone and were not independently reproduced here. This is a validation boundary, not a source-proven implementation bug.

No new Lean source is part of this diff. A target-tree search under lean/MicroCFTA found no NodeView/deriveNode/Template-Haskell occurrence. This review does not extend the current formal theorem claims to splice execution, GHC Generic metadata, native constructor identity or these new integration tests. The helper is consistent with the existing source-level shape checks and stated manual-view limitations; full formal realization remains open.

Pinned complete files at the target commit:

| Path | Lines | Bytes | SHA256 | Git blob |
| --- | ---: | ---: | --- | --- |
| `.github/workflows/ci.yml` | 153 | 5205 | `ed3ccf93847129ed42222ca2efc8895209129f2168be70e43aee004cda0178f4` | `979d612af21ed05d05eb9d186a072e13807681e9` |
| `README.md` | 206 | 9773 | `30e580d2aae2fbbac217e5d9475bc06fd9d82e48b2d9ca51913ffdf0c5225f5b` | `11f101e682696238cfad51edda64cd8de7505aef` |
| `cabal.project` | 34 | 630 | `74e510696a35b2c624ff7b685a5322e4d2047dacb4d7d6f31ab11d8929469484` | `aae069b681a0d3466f732d30b1a2d6b3b8830476` |
| `cfta-th/CHANGELOG.md` | 5 | 108 | `394dc0d77d0130859edc2a57e6a06f1773e2d605066bd9165b4efedc0711e598` | `15949a9b434b01a7e166d21030df72301a490023` |
| `cfta-th/LICENSE` | 30 | 1527 | `8f2b09582092f71474a655b5e26e28d7c41751504320a8a5e32f5799f552fb57` | `2cd67da8e9ca8130290de740a91ce41941bac77b` |
| `cfta-th/README.md` | 58 | 2245 | `8db48d510ff61b3ba3ce88f2dd413a302519b73e96cb2f54d77eb05de33b10b3` | `e4bce6c1b2873c8761020ea6c5818f957ca2c869` |
| `cfta-th/cfta-th.cabal` | 64 | 1523 | `41d194a56ea881d3fc03e57de3b3ce09c3e1cd5a8948e5c1e749a5a25aa9427d` | `7b9eb93aa8bed9398ac9657be2986b3c5386baf5` |
| `cfta-th/src/Data/CFTA/TH.hs` | 73 | 3196 | `f1c7b9a41f6f897a6ecf1ba7e17afadef4622d94c26c12a02f1d7f5252ac6105` | `18d57769dcfac333de2c3ac6e34e05b9206a02f0` |
| `cfta-th/test/Spec.hs` | 127 | 4906 | `96a56edbb5961629be572af4041a86695f098743a196738f8790486571f0ce5b` | `cb20731e1fdb0f6bd2f010aa164e6dd45dbd0eae` |
| `docs/generated-node-views.md` | 61 | 3176 | `3bfeb6c685417b3a18de781ab0eb6088db6d2632e9afd40e5b9ea90b022fc1c6` | `2b13c4fbfbe815952ae3b5b1f6c92581a73cf706` |
| `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs` | 766 | 32675 | `f5d8170c33b517e778bce00489b3d8a0d5037d0657e496e0f63095112cb6982d` | `ce9ba353af407d4b525387596b1c230a9c36a513` |
| `cfta-generator/src/Data/CFTA/Gen/Typing.hs` | 526 | 24641 | `eba22de1413b3bba9add0b70d81da8195adcfae1cea512c3153e8137297c7138` | `bd2410be5b9fcc40dbd69b828ddc84002017d07c` |

Exact defining/API cuts inspected above, including their original LF bytes:

| Cut | Bytes | SHA256 |
| --- | ---: | --- |
| `cfta-th/src/Data/CFTA/TH.hs:38–60` | 1299 | `2081318120c2325123f3833f17be2ba984f4ecb650d04da362610050a9278439` |
| `cfta-th/src/Data/CFTA/TH.hs:62–73` | 594 | `2d1c0ad7814e73f44ab52868e68e902016f282622ee609812711d5d255277ead` |
| `docs/generated-node-views.md:14–39` | 1523 | `e3f18eb45db8902ee6f8593622555d4e898cd44f31d9b830dba54a417dfedda5` |
| `cfta-th/README.md:36–55` | 1229 | `6cd9ae6321e1e1ba17c7e3160f078286c98f574995c0af979dcc8b9d46ecc300` |
| `cfta-th/test/Spec.hs:92–127` | 2496 | `425ffb53a1badef5dc4f0de7f71091245f1598e6ac938e580d85043e89770532` |
| `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs:323–427` | 4550 | `a464a4c4d7329bfc963be4bdb8449f885032dfe5a62d39d397ed291a4a74cb90` |
| `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs:543–625` | 3946 | `d16b7e1a51bbdc80730fd6f3f189197d37faae7796be0ac40248ee1d1927ae4b` |
| `cfta-generator/src/Data/CFTA/Gen/Typing.hs:365–379` | 845 | `f2dc9de863461005b7dcdee7e04f7f951589855a9322bac1c38ff89e1a940ff1` |
| `cfta-generator/src/Data/CFTA/Gen/Typing.hs:436–451` | 945 | `e98352c12c7ec6721b53c1ba2f2efa06fe1f167ce68d732116f1177149fbc0cb` |
