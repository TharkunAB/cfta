# Scalar generated node-view public review

Status: CLEAR. Recorded 2026-10-24 03:47:35 CEST. Independent complete public-readback and source review. Root authored the new model and its repairs. This reviewer authored neither the model nor the native Haskell repair; earlier template/observer work is unrelated. No compiler, prepared program, or repository mutation by this reviewer.

Read all 27 public signatures and all 13 complete actual axiom reports in `public-1/raw.log` (10603 bytes; SHA256 `ff247ce0597b34ee58c76c896585596cb6ece139fb1ee85bf754bde30cb68f25`). Read the complete installed 298-line `SourceGeneratedNodeViewShape.lean`, and compared its exact statements with the checked public list and concrete source branch claims. The installed source equals `shape-check-2/checked.lean` byte for byte, SHA256 `bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9`.

## Full public inventory and statement checks

The first 14 signatures are four shape types and ten public definitions. Their complete exported types were checked:

| Declaration | Checked boundary |
|---|---|
| Constructor | Six observed source constructor forms; normal/record field counts, named infix, and three refused forms. |
| Reified | Ordinary data, singleton newtype, and unsupported reification; opaque contexts retain emptiness and constructor order. |
| ScalarShape | Generated base name and one unit per plain scalar field. |
| ViewShape | Generated type base name and ordered scalar constructors. |
| unsupported, collision | Literal source diagnostic strings. |
| upperName | Explicit observed character predicate on the first character, false on empty names. |
| endsInHash | Exact final-character hash test. |
| generatedName | Uppercase gate, then hash refusal, then namespace collision, then Node suffix. |
| ValidName | Independent input tests: upper first character, no trailing hash, generated name absent from the given namespace. |
| generateConstructor | Actual constructor-form classification and value-namespace name check. |
| ValidConstructor | Supported forms with independent ValidName; rejected forms false. |
| scalarShape | Exact name suffix and unit-field count; rejected-form fallback is not returned on accepted execution. |
| derive | Reification error first, then declaration form/context, type name, and ordered constructors, producing an Except scalar shape. |

The remaining 13 signatures are the following exact proof interfaces. No additional desired-result premise, native execution premise, instance, or hidden output certificate appeared in the public readback:

| Theorem | Checked premises and conclusion |
|---|---|
| generatedName_success | No validity premise; success iff independent ValidName and exact suffixed result. |
| constructor_success | No desired-shape premise; success iff independent supported form/name and exact scalarShape. |
| constructors_success | No per-constructor premise assumed on the left; complete ordered traversal succeeds iff every member is valid and the result is the full mapped list. Order and repeated occurrences remain. |
| constructors_first_error | Every earlier constructor is independently valid; the specified bad constructor actually returns the given error. The full earlier/bad/later traversal returns that error, regardless of later forms. |
| derive_data_success | Empty context is explicit in the reified input; success iff type name and all constructors are valid, with the exact complete ordered ViewShape. |
| derive_newtype | Any supplied context and constructor; equality with the same-context singleton data path. This is not an unconditional success theorem. |
| reify_error | Actual input Except.error propagates unchanged before all checks. |
| declaration_error | Unsupported observed declaration returns the literal unsupported-form diagnostic. |
| context_error | Explicit nonempty context returns the context diagnostic before name/constructor checks. |
| type_collision | Requires uppercase source, no trailing hash, and an actual type-namespace collision; derives collision before any constructor checks. |
| generatedName_hash | Requires uppercase name and a trailing hash; derives hash error independently of namespace lookup. |
| type_hash_error | Requires uppercase source and trailing hash; derives type hash refusal before constructors. |
| generated_names_pass | Every literal suffix pair passes the existing positional prefix-name validator. It does not establish compiler identifier legality, shape validity, or the complete downstream node-view checks. |

The printed types match source 13–123 and 129–296. The success characterizations derive shape/ordering from the actual modeled traversal; they do not assume the complete output. The first-error theorem's local failure premise is explicit and limited to that one specified constructor.

## Native-source correspondence and retained boundaries

The executable branch order matches repaired `cfta-th/src/Data/CFTA/TH.hs` 42–76: observed reification failure/unsupported declaration; context refusal; generated type-name check; then source-order constructor form/name checks. Both type and constructor generation reuse the same trailing-hash rejection. Normal and record arities are observed field counts; named infix has two fields. Omitted source type parameters, field types, strictness and selectors are deliberate scalar-shape erasures.

Character classification, type/value namespace lookup results, base-name extraction and reified observations remain explicit native-input boundaries. No theorem executes TH Q, reproduces GHC's fresh-name supply or full AST, proves Generic/NodeView/HasFTA extraction laws, proves codec laws, or establishes all native identifier legality from arbitrary String inputs. `generated_names_pass` proves the older prefix-name phase only; its lack of validity premises is appropriate for that restricted conclusion. Native rejection/control tests remain separate evidence, reviewed in the existing Haskell repair report.

## Actual kernel evidence

All 13 actual axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. This includes the rfl wrapper theorems. There is no axiom-free claim and no extra axiom in these reports. The actual kernel report, rather than the source proof tactic, determines this statement.

The selected strict check passes with an empty raw log, warning-as-error and all linters. Installed focused build passes (4 jobs). Public check passes and contains exactly the 27 ordered #check commands and 13 ordered #print axioms commands from public-declarations.json. Aggregate Audit passes: 3676 jobs and 75963 checked theorem dependencies; the only warning is the replayed older unused-input warning. The retained first shape-check failure remains historical; it is not counted as a clean first attempt. `model-adaptation.json` records an earlier 255-line candidate and is not the final 298-line selected-source identity.

## Exact inspected identities

- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceGeneratedNodeViewShape.lean`: 16951 B; SHA256 `bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9`.
- `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceDeriveNodeViewNames.lean`: 4974 B; SHA256 `f322435fc4108f5c4632691922901a1906861bfc1d3c0f0f0cf6da19bd327d3b`.
- `/home/tritlo/Code/mcfta/cfta-th/src/Data/CFTA/TH.hs`: 3331 B; SHA256 `4e3d0515d27c97743824c3a99cd77b920034116ff17d909d01b12c2f47e60a69`.
- `/tmp/mcfta-derived-scalar-shape-20261024/public-declarations.json`: 2528 B; SHA256 `b4dc39476923ee7206c643fd53de34069ab61e5112372b271bd8b2980c77b21d`.
- `/tmp/mcfta-derived-scalar-shape-20261024/model-adaptation.json`: 425 B; SHA256 `ab75293847f42038fd6857c5dc5025053263de79f79942e37dfdbaed6340188f`.
- `/tmp/mcfta-derived-scalar-shape-20261024/public-1/checked.lean`: 2618 B; SHA256 `be698a5946ef92e07d870eed8676d37979c59c3ffafa5c009ed1ed83e02878bc`.
- `/tmp/mcfta-derived-scalar-shape-20261024/public-1/raw.log`: 10603 B; SHA256 `ff247ce0597b34ee58c76c896585596cb6ece139fb1ee85bf754bde30cb68f25`.
- `/tmp/mcfta-derived-scalar-shape-20261024/public-1/report.json`: 498 B; SHA256 `d2ce2d155e342b28a011071d7a45f5db26dec92b5e972704043062fd417577d7`.
- `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-1/report.json`: 508 B; SHA256 `35f07c51ed7268aa316292bdf1c4676120adad76deea881dd3f67cb1c439d866`.
- `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-2/checked.lean`: 16951 B; SHA256 `bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9`.
- `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-2/report.json`: 504 B; SHA256 `5bd03cd2e5d3a75236143bd4bf6f7661a437ed601fec11b4ac0ec02339bc9f32`.
- `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-2/raw.log`: 0 B; SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/mcfta-derived-scalar-shape-20261024/installed-build-1/report.json`: 323 B; SHA256 `efbf52bfe41de8766a59bea1c84c98b8a910e56795cbf83d6866ee76d6a6af7f`.
- `/tmp/mcfta-derived-scalar-shape-20261024/installed-build-1/raw.log`: 102 B; SHA256 `0208bff27614e7f12d49996be721469eb45646ee65ef3bceba77c9b90ed7e5e1`.
- `/tmp/mcfta-derived-scalar-shape-20261024/audit-1/report.json`: 300 B; SHA256 `2720af7af5a50843b1d7ba23aefae25b82b20600e5da02bb4ba7caff549bcb64`.
- `/tmp/mcfta-derived-scalar-shape-20261024/audit-1/raw.log`: 617 B; SHA256 `7601e55e65ae28bff2303ed6d529e82e1edcc0dd1ea48ceba93dab2cfcea4b94`.
