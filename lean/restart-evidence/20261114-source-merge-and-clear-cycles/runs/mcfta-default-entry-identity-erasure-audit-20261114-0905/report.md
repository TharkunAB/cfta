# Default entry configuration and identity erasure

Read-only audit. Created 2026-11-14. All proposed headers are UNCOMPILED. No source or Haskell fix was made.

## Result

The actual `programsIn` path has no UVar preference. Its nontrivial `spaceOrder` controls EDGE order. The current worker erasure theorem already permits an arbitrary edge function. No generalization of its metadata selection order is required for this entry. The current full accepted eager wrappers cannot be substituted directly: they use configured native narrowing and raw `nodeEdges`.

## Exact Haskell path

| Stage | Source | Configuration |
| --- | --- | --- |
| Program listing | `cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:969-970` | `programsIn` calls `runsBy (spaceOrder space) "Mu" (spaceNode space)`, discards obligations, deduplicates typed terms with `nubOrd`, then applies `toProgram`. |
| Default sized space | `Synthesis.hs:774-775,974` | `orderedSearchSpace` uses `reduceWithOrder` on `rawSearchSpace`; `solutionsOfSize` then calls `programsIn`. |
| Edge weight | `Synthesis.hs:724-738` | `spaceOrder` is the negative first reduction round, with a fallback for new edges. It does not inspect oracle metadata or UVar candidates. |
| Per-node edge function | `cfta/src/Data/CFTA/Enumeration.hs:689-718,1253-1256` | `runsBy` calls `runsFrom (canonicalEdgesOf (Just weight))`. The closure captures the same root. It applies stable descending weights over canonical edge order; newly constructed nodes use canonical fallback edges. |
| Initial state | `Enumeration.hs:297-311,1288-1294` | `runsFrom` stores `order root` in `_edgesOf`, allocates raw root UVar zero, then calls `enumerateFully`. The constrained-recursion flag is `reachesConstrainedMu root`. |
| UVar selection and callback | `Enumeration.hs:858-860,913-927` | `enumerateFully` supplies state `()`, `noExpansionPreference`, and the inline oracle that returns `(False,state)`. `enumerateFully'` supplies stop `Nothing`, identity narrowing, and eager `enumerateNode`. |

No `EnumOracle` declaration occurs in the searched current `cfta/src` and `cfta-generator/src` Haskell sources. This default call supplies its callback inline. `runsNarrowedBy` and the curried branches of `programRuns` are separate entries. The direct `programsIn` path does not use them.

## Two order parameters

The Lean `order : Metadata Typing → List Nat → Option Nat` models Haskell `ExpansionOrder`: it chooses a ready UVar. The Haskell default is exactly the constant `Nothing` function. `spaceOrder : Edge Symbol → Double` instead determines `_edgesOf`. Confusing them would give the wrong configuration. The current erasure theorem quantifies `edgesOf : Node → List Edge` without a membership, permutation, completeness, or no-preference condition on that function. A root-dependent weighted edge closure fits that parameter once its source representation is supplied. The same closure must be used on both sides.

## Callback and narrowing boundary

The Lean worker retains `recordTypes` on both sides. With templates `[]`, Right is a pure false result with the same metadata; Left changes only metadata and returns the same Core (`SourcePruningRecordTypes.lean:77-91`). The checked erasure theorem proves that arbitrary such metadata does not affect the other bounded observations when narrowing is identity and UVar preference is absent. It compares two existing `recordTypes` workers. It does not itself prove a Haskell callback implementation theorem.

The full accepted eager wrappers use `SourcePruningOuterNarrow.narrow`, not the identity backend. Taking `fits` and `admits` constantly true does not make that native operation definitionally identity. Non-Mu values outside `metadata.types` still call `narrowAt`, which exposes rows and reconstructs a node, and can return a native failure. In particular a union still uses the fueled exposure path. Therefore an accepted configured outcome must not be renamed as the identity outcome.

## Current Lean wrappers

`SourceSynthesisCurrentAcceptedEagerRootScanOrigin.accepted_initial_root_scan_origin` retains the strongest combined current initializer, stable configured outcome, emitted-output/readback/Program receipts, and initial scan origin. `SourceSynthesisCurrentInitialEagerInvocation.accepted_initial_prefix` retains its initial invocation. Both still use configured narrowing and `InternedEdgeResidency.nodeEdges`. Their configured outcome and witnesses must stay attached to that same invocation.

The strongest directly composable identity input receipt is `SourceSynthesisCurrentInitialIdentityPrefixStable.accepted_initial_identity_prefix_stable`. It supplies one accepted raw initializer, all native build/context/role/cache/handle receipts, the literal startup caller/cache/query memos, the initial decision, and every positive-fuel initial identity-prefix receipt. It does not yet give an identity eager resource theorem or a nonempty result.

The proposed `accepted-current-identity-worker-header.lean.txt` extends that exact initializer/prefix conclusion. Every prior witness and clause is retained verbatim. Inside the same existential scope, it states the current checked eager erasure equality for every fixed edge closure and both arbitrary metadata records. Each output is paired with an actual output of the Unit reference invocation with the same erased record, cache, caller, and queries. Any supplied same-output partial-root and Program witness keeps exactly its read fuel, partial, after-Core, and Program. The header does not assert such a witness or output exists. It does not borrow a configured outcome.

Proof plan: obtain the existing stable initializer receipt once; reassemble it unchanged; append `runEager_identity_metadata_erasure` at its exact caller/startup/query values. Case-split the two existing complete/stopped results to read their emitted lists. Equality of their mapped lists pairs each actual output with a Unit reference output. Projection equality gives the cache/caller/query equalities. Rewrite those equalities to retain each supplied readback receipt and the same Program witness. No provider, worker, adequacy condition, or model premise is needed.

## Remaining source correspondence boundaries

The generic worker law already accepts the weighted edge closure. The full current output/resource wrappers do not. They require a later identity-backend/edge-function port or an exact bridge; this audit adds neither. A weighted canonical edge-membership/order receipt is separate from metadata erasure.

The initializer receipt concerns the raw current build. Default `solutionsOfSize` enumerates a reduced and refolded space. The same source initializer must be connected to that exact transformed space before claiming the complete default program-listing path. The rendered `Term`/obligation pair, `nubOrd`, and final `toProgram` are also observations after the bounded worker result. The erasure theorem retains duplicate output order; it does not silently apply deduplication.

No slot-order generalization is needed for the audited default. For a different metadata-independent UVar preference, the minimal change would add one `preference : List Nat → Option Nat` parameter to the existing two worker erasure laws and use `(fun _ candidates => preference candidates)` on both sides. The public prefix law already supports this. Only the empty-template continuation simplification and the same fuel proof would require adaptation. This is a possible later specialization, not work requested or implemented here.
