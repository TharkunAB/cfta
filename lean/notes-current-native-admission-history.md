# Causal admission through actual native queries

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`6ba5d18b`. The new proof commits are `f2e119b9`, `4b1d8e25`, and `49184f18`.
No Haskell implementation or test changes occur. The external Haskell fix
registry remains at the top of root FINDINGS.md.

## Gap closed in this checkpoint

The preceding generated-query theorem required admission of old returned
requests and the names in their captured seen pairs. It did not derive
those properties for newly returned internal cells. A caller could not
use that theorem alone to justify another model expansion.

The new query theorem derives causal coverage for every final native cell.
The proof covers suspended, evaluating, and returned phases. Admission
holds when lookup publishes the request. Demand and finish retain the
same original request. A later expanded inventory can transport that
coverage and the contextual result laws on the same tables.

Initial all-cell coverage remains explicit for a general warm cache.
Empty modeled native tables derive it without a request premise.
No Haskell global cache reset is claimed.

## Proof structure

`SourceCurrentAllocatedNativePairAdmission` derives coverage for canonical
seen pairs and literal source domain entry. It derives nonempty admitted
representatives from the successful original operand identities. Actual
cache readback supplies the entered key and its retained pairs.

`SourceCurrentAllocatedNativeRequestAdmission` derives input membership
for exact union members, Mu bodies, hash-joined rows, zipped children,
and later binder reads. Old finite-input closure and actual payload
readback supply membership. A returned child result supplies no input law.

`SourceCurrentAllocatedNativeAdmissionCache` covers every stored request
in both tables, independently of its phase or answer. It proves actual
lookup, demand, finish, and machine-advance preservation. The invariant
derives the weaker returned-only Admitted and SeenAdmitted properties.
Cross-view Agreement transports the same all-phase cells.

`SourceCurrentAllocatedNativeAdmissionExecution` proves preservation for
every finite checked outcome from admission checks at the actual reached
publication instructions. Its RequestsThrough plan is an intermediate
interface. The final query theorem derives coverage through its own trace.

`SourceCurrentAllocatedNativeAdmissionCode` gives local certificates.
Each node or edge instruction carries original source scope and admission
before publication. Recursive continuations receive only physical facts
about resident returned values. Primitive continuations follow actual
returned machines. Protected finish frames retain the certificate.

The separate `AdmissionNodeCertificates` and `AdmissionEdgeCertificates`
modules derive these certificates for the complete literal node compiler
and the actual emitted checked-edge code. Ordered row and union traversals,
Mu entry, grown-heap binder reads, arity mismatch, and rejected sentinels
retain their source branches. Rejected edges generate no child code.
No result-language law or completed recursive callback is supplied.

`SourceCurrentAllocatedNativeAdmissionTrace` follows the actual physical
trace. Current checks derive Good, SemanticReady, fields, and machine
growth after each step. Protected physical keys identify stored requests
at native hits and starts. The actual checked edge prefix retains its
returned equality operations. A busy or absent outcome cannot match a
given yielded trace step; this is not a global busy-impossibility theorem.
The trace induction derives final coverage and the next local certificate.

`SourceCurrentAllocatedNativeCoveredQuery.branches` instantiates both
static branch families from their actual source proofs.
`query_complete` combines them with the exact WarmQuery completion receipt.
It constructs the physical trace, derives all final cell coverage, and
retains exact intersection meaning, closedness, residency, Good, Scoped,
and Idle. No future admission plan, completed trace, target law, or final
cache invariant is a premise of this endpoint.

`generated_complete` constructs the literal target roots
`oldRoots ++ [left, right]` at the actual current heap. It derives the
expanded finite inventory and transports the same warm cells. Its result
exposes the actual root availability and closedness witnesses and the
corresponding finiteInput. It also derives coverage of every newly returned
internal request. A later query can use that concrete source inventory
and the returned coverage. No second admission oracle is needed.

## Scope and validation

The pinned full Audit passes 2320 jobs and checks dependencies of 56321
theorems. Only standard Lean foundations and the old unused-input warning
occur. Focused public axiom reports, complete signatures, kernel
integrations, and independent reviews are in
`restart-evidence/20261016-admission-history/`. Saved failed logs remain.

The starting inventory contains 3538 files. No starting file is removed.
All 2310 older non-Audit proof sources retain identical bytes. Preservation
checks also retain prior frozen sources, stashes, other worktree records,
and the root Haskell repair registry. Only the seven restart documents
and additive Audit imports change among the starting files.
Earlier unavailable external drafts are not claimed recovered or reverified.

The unchanged Haskell source retains the strict Nix build, 777 examples
plus golden, five-file Fourmolu, and four-package Cabal-gild validation.
No implementation or test file changes. Every later Haskell fix must be
added to root FINDINGS.md with its failure case, affected files, commit,
checks, and upstream status.

## Next obligations

1. Carry the concrete expanded inventory and coverage through the entire
   source seeded fold. Projection effects must retain the same native tables.
   Use the actual head-projection, tail-fold, native-query order and the
   source seed rotation `rest ++ [seed]`. Reached FoldRanges supplies the
   machine checks after those actual prefixes. Do not require unrelated
   original forest siblings to be closed; anchored PathSupport supplies
   closedness for the selected operands.
2. Derive common-subtree inclusion and the actual checked class witness.
   Prove original stopped-class rejection soundness for current Scan.
3. Compose the actual allocated precheck state, all gate memo receipts,
   selected required paths, and the general constrained outer caller.

The whole seeded fold and complete constrained caller are not proved by
this checkpoint. Keep every other full-library and separate Sized contract
active. Runtime-family wiring, remaining frontend adapters, concrete
containers, GHC forcing and publication, allocation order, concurrency,
machine ranges, solver IO, random draws, and user codecs retain their
explicit boundaries. The full goal remains active; this checkpoint is progress.
