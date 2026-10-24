# Exact raw results of native edge traversal

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `b9faa1c5a04fd290e9191ffa52f963b538e3702e`.

The existing completion producers derive one actual Success, result and
final state. Success means membership in the raw result list. The two new
source-specific facts prove that this observed result is the complete raw
singleton. They exclude additional successes, duplicate results and errors.
They reuse the same observed result and full final state.

runStaged_exact applies to the actual input map of prepareChild. It does
not accept arbitrary captured child actions or a supplied singleton law.
prepare_exact applies to the action identified by the actual prepare result.
Its observed Success is the one supplied by the existing completion proof.
No new action or duplicate completion packet is added.

The uniqueness facts need no heap-validity, child-closure, realization or
supply-alignment premise. These conditions remain in the completion producers,
where they establish safe native readback and existence of a useful result.
The modeled allocate and raw setValue operations are deterministic. List.set
is total, including in an unaligned state. Uniqueness alone establishes no
semantic validity for such a state and promises no successful execution.

The actual staged traversal preserves the reached state at its first
unsupported child. Earlier child effects remain. A present action returning
none is a successful unsupported result. False inherited arity rejects before
projection and equality allocation. Its raw result list is empty. Absent
projection gives an absent preparation. These outcomes remain distinct.
Only a completed child list constructs the fragment and records its present
residual. The complete source constraint and residual choice remain.

The first three strict inputs failed. The corrections use case syntax, reduce the public staged let, supply the concrete bind states and unfold the actual state/error transformer operations. The fourth strict input passes with a literal empty log under all linters and warnings as errors. All three failed inputs, complete raw outputs and exact successive patches remain. No proof limit changed. The installed build, complete public readback and Audit pass. All 34 public-output lines retain both complete signatures without display omissions. The evidence verifier uses the actual installed-1 path and exact second-line Audit insertion. Both prior verifier inputs and exact corrections remain. No passing build was repeated.
The installed build passes 623 jobs. Audit passes 3698 jobs and
76204 dependency checks, with the unchanged older warning.
runStaged_exact reports propext and Quot.sound. prepare_exact reports propext, Classical.choice and Quot.sound. No project axiom is added.
All frozen contracts, scoped types, independent reviews, exact inputs and
actual raw evidence remain. The preceding checked-row checkpoint's26
post-seal inputs remain. Its prospective assessment was already sealed.
Older failures, diagnostics, owners, proofs, drafts and repairs remain.

Ordered ordinary-node choice and native edge ordering still need their
caller and representation proofs. Terminal native intersection/assimilation,
constrained-recursion emptiness and coupled slot/count/ancestry, all-producer
origins/edits, selector, Graph/ID/index/memo2, extraction/signed bounds,
cutoff language and full typing/pruning/driver/runtime/solver/resources/
convergence remain open. H6 stays strongest combined. H23 and older work
remain. No Haskell source changes. FINDINGS keeps all six imported repair
handoffs first. The optimized core remains. The complete goal stays ACTIVE
and incomplete. This record precedes evidence and push.
