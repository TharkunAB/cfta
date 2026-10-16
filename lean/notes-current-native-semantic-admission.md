# Native input admission across actual heap growth

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`f37a8fe5`. Input transport and inventory proofs are in `953f3b1a`.
Cross-view cache transport and the next-query theorem are in `61ce6cff`.
The actual allocated class-entry adapter is in `048d9fce`.
No Haskell implementation or test changes occur. The external Haskell fix
registry remains at the top of root FINDINGS.md.

## Place in the complete proof

The full target is implementation correspondence for the library's stated
semantics. Generation must cover the required terms. Exact queries must
list, count, rank, and unrank the accepted terms. Sampling must have the
specified probabilities. Each transformation must satisfy its own language
contract. The optimized interned core remains in scope.

There is no unrestricted whole-library implementation theorem yet.
The explicit-map Sized algorithms already satisfy their complete query
specification. The present work concerns generated intermediate operands
in the current constrained recursive caller. It does not replace the
separate Sized or other API obligations.

## Why physical scope was insufficient

The contextual node and edge laws have input-admission antecedents.
A law for a request outside an old model can hold without constraining its
result. Enlarging the model then activates an obligation that the old law
did not prove. Good, Scoped, Original, closedness, and residency do not
supply that missing old admission.

Across actual heap growth, arbitrary identities can also gain payloads.
Total equality of the old and new rank families is therefore unsuitable.
The proof uses exact rank agreement only on the old admitted domain.
Captured `domain.seen` pairs need old admitted representatives for both
identities. Current operand admission alone does not cover those pairs.
These are proof obligations. No Haskell behavior defect follows from them.

## New checked results

`SourceCurrentAllocatedNativeInputModelTransport` exposes returned-request
admission independently of conditional contextual laws. It proves safe
same-view transport and retains a kernel example of the excluded-request
obstruction.

`SourceCurrentAllocatedNativeInputGrowthModels` transports each finite
input derivation with exactly the same rank. The proof uses old reference
closure when a reference enters its Mu body. Its lifted finite model keeps
the old valid domain. Actual record growth and issued-map extension derive
the view agreement on old closed-root reachability.

`SourceCurrentAllocatedNativeGrownInventory` derives old-root reachability
in the actual target heap. A larger target root list admits every old valid
input and each newly listed closed resident value. Old input ranks and
languages remain exact. Target Original syntax follows from target
coherence, availability, and closedness. Root order and multiplicity can
change; root inclusion remains explicit.

`SourceCurrentAllocatedNativeContextRebase` derives contextual node and
edge laws across views. It uses old returned-request admission and old
seen-pair coverage. It also retains both coverage certificates for the
same existing cells. Pair soundness and bounded completeness use local
name agreement. No equality on unrelated identities is a premise.

`SourceCurrentAllocatedNativeAdmittedQuery.query_complete` constructs
`oldRoots ++ [left, right]` at the actual current heap. The operands can be
generated after the original source heap. The theorem derives their
Original syntax, current model membership, old-domain rank agreement,
and the transported contextual cache invariant. It then completes the
literal checked query on the same full state. The receipt proves a closed
resident result with exactly the operands' intersection language.
No target model, target contextual law, future return, or desired language
law is supplied.

This is one next-query theorem. Old returned-request and seen-pair coverage
remain explicit. The theorem does not establish coverage of newly returned
internal cells for a later model expansion. It does not complete an
arbitrary generated-query history or the complete seeded class fold.

`SourceCurrentConjunctionAllocatedClassEntry` uses the actual precheck
operation state, `(PartialPrecheckAllocation.run ...).2`. It derives
Scan.Ready, proper original paths, actual child availability, and finite
current class Scan. It retains ordered original records and fourth memo
correctness. It supplies no completed historical Scan premise. Its result
is still physical Scan completion, without original-class rejection soundness.

## Validation and preservation

The pinned full Audit passes 2311 jobs and checks the axiom dependencies of
56189 theorems. Only standard Lean foundations and the old unused-input
warning occur. Public signature and axiom probes, independent reviews,
and kernel integrations have separate repository-local evidence in
`restart-evidence/20261016-semantic-admission/`.

The unchanged Haskell source retains the strict Nix build, 777 examples
plus golden, five-file Fourmolu, and four-package Cabal-gild validation.
Saved failed Lean logs remain in the evidence directory. No test file changes.

Preservation checks cover the 3463-file starting inventory and all 2304
older non-Audit proof sources. Earlier unavailable external draft bytes
are not claimed recovered or reverified.

## Next obligations

1. Derive and preserve returned-request and seen-pair admission from actual
   query execution. Cover each newly returned internal node and edge cell.
2. Iterate actual model growth through the source seeded right fold.
   Derive common-subtree inclusion and the checked class witness.
3. Prove original stopped-class rejection soundness for current Scan.
   Compose the actual allocated precheck state, all gate memo receipts,
   selected required paths, and the general constrained outer caller.
4. Retain the remaining full-library boundaries: current frontend adapters,
   runtime-family wiring, recursive callback completion, concrete containers,
   GHC forcing and publication, atomic operations, allocation order,
   machine ranges, solver IO, random draws, and user codecs.

The full goal remains active. This checkpoint is progress.
