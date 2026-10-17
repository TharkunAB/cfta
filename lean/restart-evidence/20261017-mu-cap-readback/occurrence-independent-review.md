# Independent source support and occurrence compiler review

Reviewed on 2026-10-17 at 04:08 CEST. No material defect found.

The final reviewed sources are:

- `SourceCurrentConstrainedCapOriginalSupport.lean`: `8b1358c8c027480db80fe6a8b4eb62083295dd9caa7222e0ca6a9fe6e3f3ecc3`.
- `SourceCurrentConstrainedCapNativeOccurrenceCode.lean`: `38d97ef9c86f4b4b908304988eb299bd3aec1b4fd325c59ba62ba9f67e5d814b`.
- `SourceCurrentConstrainedCapNativeOccurrenceCompile.lean`: `6e8a6260d6dc3b6a60b541484176baf8a89733e0cc2e267ccf83b5e9d3e8aa36`.

## Exact source support

`OriginalSupport.closed_inputs` derives original syntax and name coverage from closed, available operands and coherent facts in the same fixed source heap. It does not infer the source from a later result. `extend` retains complete original Mu witnesses for old names and derives the new Mu witnesses from the actual operand bindings. A source cap makes those Mu operands hereditary. `enter` uses the actual domain cache and its validity to identify the literal entered key.

`read` needs current physical facts, source-to-current growth, and issued-history extension. It then reads the same complete source Mu witness by its actual identity. It retains source availability, current availability, annotation, coverage, and original syntax. Ordinary child and union-member projections use the same source records. `rows_input` transfers those facts to both actual joined rows. No result availability, future completion, or guard restriction on unrelated heap records is assumed.

`classified` uses the original input view to show that every original free reference is interned. Its source occurrence weight is therefore zero. The proof also uses actual coherent deep-to-free membership. This establishes both the inclusive free bound and the strict-or-zero deep bound for every natural request bound.

## Budgets and compiler certificates

The row budget is the maximum rank of the actual zipped child pairs. It does not count children outside the literal zip. At positive parent rank, strict ordinary child descent bounds every such pair, so the maximum is strictly smaller. An empty zip has budget zero. At parent rank zero, the explicit zero alternative supplies the deep-classification branch. No equal-arity assumption is added to the literal zip.

`children_certified` checks each original child at `depth - 1`. At zero, the supplied row cap gives hereditary children. At a positive depth, the row cap gives the smaller finite cap directly. The guard premise applies only at zero. It is an input guard fact, not an assumed output cap. `rows_certified` places each returned child's inclusive weight bound below the positive parent rank before the actual node constructor makes those names deep.

Both union certificates project the actual original members and their source coverage. Each request retains the unchanged opposite operand. The nonincreasing union rank is sufficient: `classified_mono` handles the zero-to-positive case using coherent deep-to-free membership and the available returned record. Union normalization requires `Normal` from the explicit representation predicate at the actual returned heap. It does not substitute a source heap for that heap.

`NativeOccurrenceCode.Certified` is a local continuation certificate. Recursive requests supply their exact returned physical value and both conditional cap and occurrence laws. Primitive continuations supply validity, extension, and the chosen representation at their actual returned machine. Bind and walk compose those states and transport only the declared stable facts. This certificate does not prove that recursive requests complete, that primitives produce the representation invariant, or that a returned cache cell already has those laws. The modules make this boundary explicit. There is no hidden completed query, desired result, or finite-execution premise in the local compiler theorems.

## Imported validation

`occurrence-independent-public-1.log` passed 25 full-signature and axiom pairs: eleven support declarations, nine code declarations, and five compiler declarations. No warning, error, truncation, or `sorryAx` occurs.

The no-premise theorem `constructed_source_support_and_certificates` in `occurrence-independent-kernels.lean` passed in `occurrence-independent-kernels-4.log`. It constructs a closed source union from an empty heap. One member is a constrained ordinary prefix above a plain leaf. The other is a hereditary raw recursive Mu. The kernel derives the actual construction return, original source inputs, empty-domain bindings, and depth-one caps from that construction. It proves the positive parent budget is strict for the actual row zip and proves the hereditary leaf row budget is zero. It then constructs the local row and actual union certificates with representation `Normal`. No future request success or returned cap/classifier is a kernel premise.

The kernel constructs source execution. It does not construct native intersection execution. Its final results are local certificates whose recursive request clauses still require the corresponding returned laws. Three failed kernel attempts and their raw source snapshots remain intact.

The canonical root build passed 1096 jobs. Its only warning is the historical unused-variable warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`. This reviewer ran only direct imported checks and wrote evidence files. No production source, canonical build, `.olean`, Haskell source, or Git state changed.

## Scope

These modules close original input support and local ordinary/union occurrence compilation. General actual recursive execution still needs the causal production and retention of the requested cap and occurrence laws. Positive-depth warm Mu guard-cap readback remains a separate obligation. These certificates do not establish general native completion or Haskell runtime correspondence.
