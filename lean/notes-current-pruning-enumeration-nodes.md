# Stored enumeration-node handles

Updated: 2026-10-24. Baseline: `4c856a02c12a6fa2ff67e7780d5afa709a1a86a5`.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `31eaa5af6b65fc4f6a00107607f42d16a3dfef29`.

`SourcePruningEnumerationNodes` adds a computed handle codec for the existing
interned heap. It keeps full symbols, refinements, guards, children and metadata
in the returned Value. It adds no node datatype or caller-supplied decoder.

Empty has handle zero. Reference has no handle. Ordinary, union and Mu records
use their entry identity plus one. This is the existing model-handle convention.
It is not raw native NodeId extraction. Raw UVar IDs remain separate.
The structural encoder does not certify arbitrary forged inputs as canonical.

A positive lookup reads its issued key, canonical table entry, winner identity
and complete node payload, in that order. Missing or pending data returns none.
A losing reservation returns none even when its key has a winning payload.
Zero returns Empty directly. A positive lookup returns its actual stored payload
and never defaults to Empty for missing data.

`available_readback` assumes Coherent, Available and no free references.
It derives a computed handle whose actual lookup returns the SAME complete Value.
Residency supplies its stored payload. Coherence derives its canonical entry
and issued key. Closedness excludes Reference. No Ready, source counter bound,
dense numbering, constructed-run certificate or desired readback is assumed.

`lookupNode_keeps` starts from an actual successful lookup before an operation.
The existing Keeps packet supplies issued-history extension and growth of the
canonical table and payload table. These derive the same successful lookup in
the actual final heap. No final lookup or replacement heap is assumed.

The final module has 76 lines, two definitions and two theorems. Strict Lean
4.34.1 checking passes with all linters and warnings as errors; its raw log is
empty. The installed build passes 558 jobs. Aggregate Audit passes 3680 jobs
and 76095 theorem dependency checks. Its one warning is the older unused inputs
warning in InternedFreshOrdinaryClosedCompletion. No new-source warning occurs.
All four complete public signatures and both actual axiom reports were read.
Both theorems use propext and Quot.sound. No Classical.choice or project axiom
appears in their reports. Independent declaration, model and public reviews pass.

The frozen owner proposal retains 41 payload files and five exact context/header
contracts. The first strict attempt fails on three unclosed Option contradictions
and deprecated conditional lemma names. The second changes only that proof:
it eliminates the contradictions and uses the current conditional equations.
All executable definitions and theorem statements remain unchanged. The failed
source, diagnostics and resource receipts remain available.

This completes the computed heap-readback part of the enumeration-handle bridge.
It does not prove that arbitrary enumeration slots already contain these handles.
Next derive initial slot realization, preserve it through observation frames and
actual cache growth, and connect actual getUnexpandedNode results to complete
available closed Values. Finite reads must derive a stored representative slot
from StorageValid and an allocated raw UVar; Total alone is insufficient.
Actual allocation, intersection and narrowed-slot writes still need producers.

The later typedTypes composition must keep raw hole IDs, typing, outer narrow,
per-call memo2 and full state effects. It must sequence all native UVar reads,
then retain only the pure emptiness calls demanded by lazy or. The existing
plan and separate evaluation caveat remain preserved.

H6 remains the strongest combined theorem: covered closed construction and valid
original guard/cache history derive sufficient mathematical width/fuel for any
finite number of modeled node-call rounds, with exact finite-tree language
equivalence for empty inherited payload. withoutRedundantEdges and convergence
remain outside that theorem. This codec adds no language-preservation result.

Native representation and global-cache extraction, graph/slot-write realization,
global helper canonicality, canonical mutation histories, selected-current
protection, cached-driver composition, semantic pruning, phase 4, resources,
practical width, runtime/solver correspondence and convergence remain open.
H23 stays queued. The full goal remains active and incomplete. Older constructor
and equality targets and the optimized interned core remain preserved.

No Haskell source changes occur. FINDINGS keeps the external repair index first.
All six recorded repairs are on main. No additional patch remains for those six
defects. Earlier counterexamples, repairs, drafts and validation remain.

Evidence is in restart-evidence/20261024-pruning-enumeration-nodes. It retains
the frozen declaration package, all attempts and complete reviews, capped resource
receipts, exact baseline and previous publication receipts. Its verifier checks
all baseline blobs and modes, nine exact status insertions and one Audit import.
