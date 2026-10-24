# Enumeration handle identity and Empty narrowing

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `327d44f068ba11964b2b0b4619abf9eb29e4256a`.

## Exact results

SourcePruningEnumerationIdentity adds two prerequisites for native-model
narrowing. It retains the existing fixed full Symbol alias and generic Guard.
It does not add a new encoding or decoder.

lookup_encode starts with a coherent native-model heap and an actual successful
lookupNode heap handle. It proves that encodeNode of that complete returned
Value is exactly some handle. The proof uses the same issued key, canonical
entry and identity test that the decoder evaluates. Coherent.nodes identifies
the complete stored payload with that entry. Available and closedness are not
premises. The theorem does not derive coherence.

Coherence is necessary over arbitrary model heaps. A malformed positive slot
could store Empty under a canonical winning entry. Its positive lookup would
then succeed, while encodeNode Empty returns zero. This model counterexample
does not establish a Haskell defect.

narrowAt_empty proves that actual SourcePruningNativeView.narrowAt returns
done Empty with the same complete heap at every fuel, including zero. The
actual Empty reader returns no rows. The filter and smart constructor then
return Empty without a cache request. Key and the required EdgeKey equality
instance are scoped to this theorem. It needs no Ready, Available, closedness
or coherence premise.

These results support two steps in the next consumer. A stored successful
lookup now determines its encoding at the same handle. A surviving narrowing
branch can exclude an originally Empty value through the all-fuel equation.

## Validation and retained work

The original identity proof passes strict Lean checking on its first attempt
with an empty log. The additive Empty equation has separate frozen declarations
and independent review. The first extended input fails because rfl does not
reduce the well-founded empty sort. A body-only repair uses existing
simplification lemmas. The theorem statements stay unchanged.
The repaired extended strict input passes with an empty log.
The installed build passes 559 jobs. Audit passes 3683 jobs and
76115 dependency checks. One older warning remains in
InternedFreshOrdinaryClosedCompletion. There is no new-source warning.
Both actual signatures and both actual axiom reports were read.
lookup_encode reports propext and Quot.sound. narrowAt_empty reports
propext, Classical.choice and Quot.sound. Both reports use standard Lean axioms.

The original identity owner has 32 pinned payloads and six exact STRING
contracts. The additive owner has 26 payloads and two new STRING contracts.
The original context, header, local types and earlier frozen plan stay intact.
All compiler inputs, raw outputs, full reviews, resource receipts and source
identities remain. The complete baseline has 128720 tracked files.

## Next proof and boundaries

Compose the actual narrowing run in its final native heap. Derive both handles
from actual complete Values. Retain the Empty rejection, native cache growth,
and unchanged-handle branch. The changed branch must perform the actual second
representative read and use its compression frame before the slot write.
The source checkRepeated call can compress the forest before expansion. Keep
its returned state when the repeated-recursion check is false.
Keep the original selected raw UVar in the typing and holeKey tests.

The raw-slot write theorem does not prove this complete source operation.
Native cached-index maintenance, the native handle/heap connection for
intersection and assimilation, open-hole bounds, ordered observation and
demanded-prefix lazy emptiness still need proofs. Semantic fits/admits laws,
outer narrow, typing, memo2 and typedTypes remain open. Global helper
canonicality, mutation histories, selected-current protection, cached driver
composition, phase 4, semantic pruning, practical width, runtime/solver
correspondence, resource bounds and convergence remain open. H23 stays queued.

H6 constructed_node_calls remains the strongest combined theorem. It supplies
finite modeled node-call traces and exact finite-tree language preservation
for the covered closed constructions with empty inherited payload.
These new component results do not prove the full optimization pipeline.

No Haskell source changes. FINDINGS retains its external repair index first.
All six recorded Haskell fixes are on imported main. Earlier proofs,
counterexamples, repairs, marked drafts and the optimized interned core remain.
The full goal stays ACTIVE and incomplete. This note precedes evidence creation
and the authorized push.
