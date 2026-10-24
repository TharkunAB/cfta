# Generated node views: formal coverage and source contract

Reviewed at 2026-10-24T03:26:02.771005+02:00. Target main: `c4f7319acf84213fccc8ea389487d4176e4f0b62` (PR #113).

The addition is a small declaration producer. It does not generate a datatype decoder, a HasFTA instance, typing rules, or refinement laws. Existing Lean results can be reused after a new generated-scalar-view metadata bridge. They do not already prove Template Haskell generation or the complete typed NodeView frontend. No concrete new runtime defect was identified in this bounded read.

## Exact new source contract

I read all73lines of `cfta-th/src/Data/CFTA/TH.hs`, all61lines of `docs/generated-node-views.md`, and all58lines of `cfta-th/README.md` at the exact target commit. I also read the committed127line test and64line Cabal file. These are source reads, not fresh validation results. The three existing native dependencies identified below are byte-identical between the target commit and the inspected checkout.

`deriveNode` accepts reified DataD/NewtypeD declarations, then checks the datatype context, the proposed type name, and each constructor in source order (TH.hs38–60). NormalC and RecC keep their field count; InfixC keeps two fields. Every field becomes a plain child parameter with no unpacking or strictness annotation. Records lose selectors. Source type parameters and field types are deliberately erased from the view. The output is a DataD with one fresh parameter, deriving Generic, followed by an empty NodeView instance. A source newtype also produces a data view. Empty declarations produce an empty view; use still needs the documented GHC extensions.

Names are `nameBase ++ "Node"`. The first character must satisfy Data.Char.isUpper. Type collisions use lookupTypeName; constructor collisions use lookupValueName (65–73). Reification errors precede the explicit unsupported-form cases. Datatype contexts precede name checks. The view-name check precedes the constructor traversal. Each constructor's unsupported form or generated-name failure occurs in original order. Every ForallC is rejected by its syntactic form, as are GadtC and RecGadtC. The fallback rejects other reified declarations, including synonyms and families. The exact diagnostic strings and name-lookup environment are new obligations; SourceDeriveNodeViewNames models a different, later runtime check.

The generator changes no core typing/refinement/rank code in this merge. Runtime NodeView reads still resolve a view's position to the ORIGINAL HasFTA constructor, rather than emit the generated `...Node` name as a term constructor. This is why positional correspondence is the important bridge. Dropping source strictness is a shape-view operation, not a theorem about native bottom/strictness behavior.

## Existing results that can be reused

| Existing Lean contract | What it already proves | What must still be supplied |
| --- | --- | --- |
| `SourceDeriveNodeViewNames.hasPrefix_exact`, `checkNames_exact`, `afterShape_exact` (23–24,59–64,80–94) | Exact character-prefix validity, first positional name diagnostic, and shape-before-name error precedence. | Reified constructors and generated Generic metadata agree in length/order/arity; generated names are the source base names with suffix Node. The earlier shape result is an input, not derived by this file. |
| `SourceTypingFieldValidation.value_iff`, `recursive_iff`, `foreign_subterm` (20–43) | Resolved runtime-type checks distinguish recursive Subterm fields from fixed fields. | Generated view metadata and `nodeFields` extraction produce those exact resolved candidates and field types. The checks do not establish fixed-tree semantic validity or codec laws. |
| `SourceTypingRulesLanguage.accepts_denotes`, `close_denotes`, `close_root` (219–222,377–407), with `SourceTypingFinite.close_complete` (360–381) | Resolved ordered rows and their computed cold closure describe bounded typing. | The public NodeView/typing translation must produce the same rules/rows; the independent LawfulFixed premise must be justified for the stronger advertised domain. The current model does not cover every newer Drawn/Binder route merely because it covers nesting rows. |
| `Generic.Codec`, `codec_rank_total`, `codec_rank_injective` (383–402) | Total decoding and injectivity on admitted ranked terms from an explicit codec contract. | Actual source HasFTA encode/decode laws and the generated-view-to-original-constructor connection. `deriveNode` supplies no codec. |
| `DatatypeDecoder.find_exact`, `decode_exact`, `decode_labelled`, `ranked_total`, `ranked_injective` (66–68,162–165,289–323) | Hash-bucket lookup and complete restoration preserve the direct constructor codec; collisions need no injective hash. Ranked totality/injectivity follow under explicit label uniqueness, alphabet and Codec premises. | Actual constructor labels/table/codec satisfy those premises. A generated view does not discharge them. |
| `DistinctRank.Index.count_eq`, `decode_translate`, `translate_roundtrip` (99–119) | Equal languages have equal counts and a reversible member-preserving rank translation. | Unchanged NUMERIC ranks need equality of the ordered enumeration/decoder, not language equivalence alone. |

These modules are imported by the current Audit. This review reuses their existing checked contracts; it does not rerun Lean or expand their established premises. No Lean scalar FieldKind/buildNode/nodeFields model was found. Existing IntegerTermViews results concern open integer recipe projections, not typed NodeView extraction, and should not be relabelled as this missing bridge.

## Exact new obligations

1. Define the accepted declaration/constructor descriptor and exact failure ordering, including ambient type/value lookup and name generation. Prove that success emits exactly one ordered scalar-view declaration and its NodeView instance. GHC TH reify/Generic elaboration and fresh-name realization remain an extraction boundary.
2. Connect that output to actual NodeView Generic metadata: same constructor count/order, names with Node suffix, same field counts, and Scalar at every field. Reuse the existing prefix theorem only after this correspondence. The native definitions are Derive.hs323–342,365–422 and597–619.
3. Prove valid-position build/read laws. At a valid constructor position and exact child arity, buildNode consumes children in order and nodeFields returns that position and the scalar child values as Just entries. Do not claim arbitrary-input totality: V1 and missing fields throw errors, and generic constructor building relies on valid positions/arity. Empty views have no valid position.
4. Keep original HasFTA metadata and codecs explicit. A user can supply custom describeType/encodeTerm/decodeTerm; the splice does not validate their laws. Preserve recursive-versus-atomic source field information even though the view fields all have type e. Generated scalar views do not create Record measure fields; recursive MeasuredBy record requirements still need a suitable manual view. The native shape/kind checks are Derive.hs542–619; rule-field checks are Typing.hs433–451.
5. Derive identical translated rules or invariant annotations for corresponding generated/manual view functions, then compose existing row/language/decoder contracts. Scalar metadata alone does not prove arbitrary user measure/contract functions or arbitrary pruning/typing soundness. Native invariant translation at Derive.hs632–653 remains a frontend proof gap.
6. For the advertised unchanged ranks, retain the original constructor identity, field order, rule/annotation interpretation, atomic domains, and exact source ordering key. Typing.hs465–507 uses arity/declaration-position/label order and the original decoder. The new suffix names are shape metadata, not a new rank policy. Generic.hs419–435 already proves why finitely many constructor probes cannot establish totality for every generated term.

The smallest substantive next formalization is the declaration-to-scalar-shape/error contract, followed by the bounded buildNode/nodeFields positional laws. This can discharge the existing name check and expose a precise frontend adapter. It should not start with another generic rank theorem or assume codec validity from the splice.

The committed tests compare38 arithmetic terms and a bounded scalar refinement example with hand-written views, check record/parameter/newtype/named-infix/empty shapes, and recover five invalid declaration cases. The design note reports additional standalone validation. Neither finite examples nor those reported checks replace the obligations above. Root owns fresh merge/build/test validation. No compiler, metaprogram execution, new proof draft, repository edit, Git mutation, or network operation occurred in this review.

## Exact source identities and read scope

Target-commit snapshots are retained under `/tmp/mcfta-generated-views-20261024-review-inputs/`. Hashes below identify complete files; bounded ranges do not claim complete manual proof-body reads.

| Source | Read scope | SHA-256 |
| --- | --- | --- |
| `/tmp/mcfta-generated-views-20261024-review-inputs/cfta-th/src/Data/CFTA/TH.hs` | all73lines | `f1c7b9a41f6f897a6ecf1ba7e17afadef4622d94c26c12a02f1d7f5252ac6105` |
| `/tmp/mcfta-generated-views-20261024-review-inputs/docs/generated-node-views.md` | all61lines | `3bfeb6c685417b3a18de781ab0eb6088db6d2632e9afd40e5b9ea90b022fc1c6` |
| `/tmp/mcfta-generated-views-20261024-review-inputs/cfta-th/README.md` | all58lines | `8db48d510ff61b3ba3ce88f2dd413a302519b73e96cb2f54d77eb05de33b10b3` |
| `/home/tritlo/Code/mcfta/cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs` | 310–427,540–653 | `f5d8170c33b517e778bce00489b3d8a0d5037d0657e496e0f63095112cb6982d` |
| `/home/tritlo/Code/mcfta/cfta-generator/src/Data/CFTA/Gen/Typing.hs` | 366–458,465–515 | `eba22de1413b3bba9add0b70d81da8195adcfae1cea512c3153e8137297c7138` |
| `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Generic.hs` | 84–159,218–266 | `c2eb5dff816434205618d8551b440144acf8a4ef4c27bd1b3411437805196685` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceDeriveNodeViewNames.lean` | complete96lines | `f322435fc4108f5c4632691922901a1906861bfc1d3c0f0f0cf6da19bd327d3b` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceTypingFieldValidation.lean` | complete46lines | `d1a9bcd4d082ed2f8a438fae926b72ee489dc59c0a5e6e06e2a15b9af72b6df3` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceTypingRules.lean` | complete140lines | `883358821462c869be1ed01b284c674b62d5fa6519495661cd89e4bcb305fdc1` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceTypingRulesLanguage.lean` | 1–60,215–231,329–409 | `08f126efca46cd30293974b2b01b6140fc4d7352c1ce3a8c50a50eacd24995b6` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceTypingFinite.lean` | 304–381 and declaration inventory | `3fcaa41fa35b555f65bfba9c2b791edc448b40c0b006d1ff77879f8cfd247c26` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/Generic.lean` | 375–437 | `d4b14c87615b9144a16bcd193c87f736d832310323efc1ada9c43a5ae0eadbb2` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/DatatypeDecoder.lean` | lookup/restore definitions and public contract statements;247–336 | `c59373905889007f0c6f48265c1e501baa701c4e0eeb75707aff84a3ada05387` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/DistinctRank.lean` | 1–138 | `9c3db40ec6f497c5f638d714443919c6325b7e12422dce34b95b3da4d411ab72` |
