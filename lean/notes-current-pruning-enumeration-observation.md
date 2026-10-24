# Actual pending-node observations

Updated: 2026-10-24. Baseline: `fe0cfe2a38ba5d7587404d89bd5fa2303f37dea6`.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `aa500886fa742522bf8e8c0fd884c0eaa8c286a1`.

`SourcePruningEnumerationObservation` connects actual enumeration reads to the
computed interned-node decoder. It retains complete Values, full symbols,
refinements, guards, children and metadata. EnumGuard and NativeGuard remain
independent. Raw UVar IDs and model node handles remain separate.

`PendingRealized` applies to every stored unenumerated slot with a present
handle. The actual lookup must return the same available closed native Value.
This includes stored slots that are not representatives. Absent handles,
enumerated slots and eliminated slots impose no condition. A present zero handle
decodes to Empty. An absent optional handle means no pending node.

`initial_realized` assumes Coherent, Available and a closed input Value.
It derives the encoded handle and realization of the actual singleton initial
enumeration state. The handle and its successful lookup are not premises.

`realized_preserved` retains realization through the existing full enumeration
Frame and actual native Keeps growth/history. Frame supplies exact values
equality. Lookup retention and Available.grows preserve each same complete Value.
This theorem does not cover operations that write different slot values.

`observed_realized` starts from incoming realization, actual getUnexpandedNode
success and genuine Total. The two operation inverses identify the actual
representative slot and its optional projection. A present handle derives its
complete available closed Value from that slot. The same read derives full Frame.
Frame retains the counter, values, obligations, both ancestry fields and root/size
reachability. It permits representative compression.

`observation_storage` starts from StorageValid, uv < counter and actual read
success. It derives StorageValid of the exact resulting state. Its separately
reviewed header adds no native heap or realization premise. Frame alone does
not imply the forest support bound required by StorageValid.

`observation_complete` starts from realization, StorageValid and uv < counter.
It derives finite fuel, the actual optional result, the actual resulting state
and full Frame. Every present result derives its actual complete available
closed Value. Storage supplies a path and a representative bound. Alignment
turns that bound into the actual values-list index. The proof constructs the
same representative-updated state and optional projection as the real read.
It assumes no desired observer success, decoded Value or resulting state.

The final module has 122 lines, one definition and five theorems. Strict Lean
4.34.1 checking passes with all linters and warnings as errors. Its raw log is
empty. The installed build passes 562 jobs. Audit passes 3681 jobs
and 76100 theorem dependency checks. Its one warning is the older unused
inputs warning in InternedFreshOrdinaryClosedCompletion. No new-source warning
occurs. All six full signatures and five actual axiom reports were read.
Each theorem reports only propext and Quot.sound. Independent declaration,
body and public reviews clear the component.

The frozen owner retains 58 payload files and six STRING context/header
contracts for the original five declarations. observation_storage has a
separate additive declaration gate. No original header or definition changes.
Five strict attempts fail on local projection elaboration. The sixth combines
local non-generalizing matching with explicit unfolding and constructor cases.
Moving the stored equality and these proof repairs change no theorem statement
or exported algorithm. All failed inputs, diagnostics and reviews remain.
The earlier source-only diagnosis remains distinct from actual compiler results.

The next gap is realization through actual slot-writing producers. Allocation,
intersection/assimilation and narrowed writes require their own proofs. The
current pure Graph.intersect handle needs a link to an actual native operation
and heap. Open-hole metadata also needs allocated raw-variable bounds. Later
composition must sequence every UVar read before the pure emptiness checks.
It must retain only the emptiness calls demanded by lazy or, with their actual
native heap effects. Outer narrow, typing, memo2 and typedTypes remain separate.

H6 remains the strongest combined theorem. Covered closed construction and
valid original guard/cache history derive sufficient mathematical width and
fuel for any finite number of modeled node-call rounds. Empty inherited payload
gives exact finite-tree language equivalence. withoutRedundantEdges and
convergence remain outside that theorem. This observation component adds no
language-preservation result.

Native representation and global-cache extraction, graph/write realization,
global helper canonicality, canonical mutation histories, selected-current
protection, cached-driver composition, semantic pruning, phase 4, resources,
practical width, runtime/solver correspondence and convergence remain open.
H23 stays queued. The full goal remains active and incomplete. Older constructor
and equality targets and the optimized interned core remain preserved.

No Haskell source changes occur. FINDINGS keeps its external repair index first.
All six recorded repairs are on main. No additional patch remains for those six
defects. Earlier counterexamples, repairs, drafts and validation remain.

Evidence is in restart-evidence/20261024-pruning-enumeration-observation.
It retains the frozen declaration package, all attempts and full reviews,
capped resource receipts, exact baseline and previous publication receipts.
Its verifier checks all baseline blobs and modes, nine exact status insertions,
one Audit import, source cuts and the active pinned core API.
