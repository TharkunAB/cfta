# Current incoming-state proof

Checkpoint: 2026-11-01 01:25 CET.
Branch: `formalize`. Proof source: `a08306bcf6a9ae7218222dea1b4ecac8b9f53bf5`.
Main: `bd5a406a6a3f84b7e3ae0906082783911509df83`, refreshed for this checkpoint.

## Strongest statement

In the Lean semantics, the actual conjunction call preserves its full caller and query postcondition
for every budget and every outcome. This includes errors and exhausted calls.
The proof uses the original entry context and the resident closed query.
The theorem is `SourceCurrentConjunctionCallPost.call_post`.
An empty result with the true flag excludes models. A false flag supplies no
positive witness. The theorem does not prove completion or a sufficient budget.

The actual incoming call now has additional state laws. Its literal outer read
preserves the root function, values, and allocation counter for every outcome.
The outer forest preserves root status at every address. With original storage
validity and the original target bound, the outer core preserves storage validity.
These laws retain the original Symbol, Edge, and Node decision data.

The cache-observation law derives the outer read's root facts from entry facts.
It identifies the exact canonical waiting delta when the cache returns `some`.
It gives uniqueness of successful index results at the same actual reached heap
and original target. It does not supply index success or waiting correctness.

The original-target law identifies the first successful representative with the
original target. It requires the original target to be a root. It does not derive
that admission or the success of the root search.

The first-write state law covers a successful raw singleton at a present table
entry `.unenumerated none oldScs`. The `none` is the node handle. The table entry
exists. The law derives encoding success and exact returned caller and query
identity. It identifies the returned core at the original target. The new value
is `.unenumerated (some handle) (scs ++ oldScs)`. The new ancestry is `(expansionAncestry ++ oldTargetAncestry).eraseDups`.
Other entries and the allocation counter satisfy the stated frame laws. The returned core has
roots, storage validity, and pending realization at the actual returned heap.
The law uses original root, storage, bound, coherence, realization, availability,
and combined-constraint-bound assumptions. It does not cover an existing handle.

The full first-write cache law now derives all five fields of `CacheValid` at the
actual returned caller and cache. It starts with original `CacheValid` and the
original admission, allocation, coherence, availability, closedness, stored-slot,
and combined-reference-bound assumptions. It requires an observed raw singleton
success and a present returned cache. It derives roots, storage validity, pending
realization, canonical waiting correctness, and decoded expandable flags.
It assumes no future cache-validity field and gives no guarantee of success.

The general incoming-read law covers every outer `.ok` result. From original
Context, pending realization, available closed input, Fits, Room, and Roots, it
derives Post and pending realization for the literal outer read at the actual
reached heap. It produces an inventory and global memos. The produced query equals
the actual saved query. It does not assert that the saved query equals the entry
query or that the produced inventory and memos equal their entry values.
Its error branch asserts only `True`.

## Checked extension

Eight production modules add 716 lines and eleven named public theorems:

- `SourceCurrentIncomingAdaptObserved`: 82 lines, one combined theorem.
- `SourceCurrentIncomingReadRoots`: 100 lines, two theorems.
- `SourceCurrentIncomingOriginalRoot`: 65 lines, two theorems.
- `SourceCurrentIncomingReadStorage`: 137 lines, two theorems.
- `SourceCurrentIncomingNoHandleFlags`: 112 lines, one theorem.
- `SourceCurrentIncomingWaitingAppend`: 54 lines, one theorem.
- `SourceCurrentIncomingNoHandleCacheValid`: 85 lines, one theorem.
- `SourceCurrentIncomingReachedReadRealized`: 81 lines, one theorem.

There were 30 actual normal Lean commands. All 30 passed. They retained 174 source
snapshots. The strict axiom audit checked 84,050 theorem dependencies. The public
check contains 1,409 checks and 159 definitions. The previous public output is an
exact byte prefix. All eleven explicit theorem statements use standard axioms.
All protected old source bytes and all 835 native records are unchanged.
The earlier board count of six named theorems in the first 247 lines was wrong.
Those three modules contain five named theorems.

The flags law derives the flags invariant for the actual first-write returned
core. It uses the actual returned heap and the original decision data. The waiting
law proves canonical optional-count correctness after append from original
correctness and the original slot. Old and new handles are arbitrary options.
Neither law assumes its required future correctness conclusion.
Its isolated pair has six actual commands: four passes and two retained failures.
It retains 78 input snapshots. Both final strict runs have empty output.
The ordinary output has 57 lines. The explicit output has 317 lines.
The cache-validity and reached-read pair has twelve isolated commands: six passes
and six retained failures. It retains 180 input snapshots. Its final strict runs
have empty output. Ordinary output has 83 lines; explicit output has 503 lines.
Independent source and public review is clear for all eight modules. Each bounded
review packet is retained whole and has a portable metadata verification pass.
The normal 1,797-line explicit output is the exact concatenation of the checked
isolated outputs. The eight sources and all previous protected source bytes are
bound by the normal control vectors.

## Next proof work

The next native branch has an existing node handle. It needs proofs about the
actual reached heap, raw returned core, references, and cache effects. The raw
empty branch and the remaining all-outcome optional-cache laws also need work.
Then compose the native laws with recursive captured-cache and fresh-reference
transport at the actual after-hook caller and query.

Existing producers are genuine. Reuse `SelectedStepCompletion.complete`,
`RecursivePacket.captured_post`, and the five-field fresh-cache and common-resource
results in `SourcePruningEnumerationChildBoundedResources`. They have local scope.
They do not establish the full positive-depth whole-execution induction.

## Full objective

Keep the full objective. Prove sound acceptance and the exact finite ordered
requested prefix with configured stops. Derive sufficient original `D` and common
resources for both native and prepared paths. Finite `D` can currently exhaust.
Use the actual after-hook caller and query and the same captured cache. Retain
original admissions, identities, fit bounds, annotations, and reservations.

Retain Mu, Union, opaque nodes, original Map behavior, domain and map relations,
SCC and history behavior, constructor-sensitive node equality, generic and
default decisions, Map and Set behavior, signed and weighted behavior, aliases,
renewal, and writer behavior. Cover size, node-count, count, table, order, rank,
unrank, prefix, and checkpoint APIs. Prove correspondence with the Haskell program.
The whole-execution resource and coverage proofs and Haskell correspondence are
the largest remaining gaps. Local preservation does not close these gaps.

## Haskell findings

This extension found no Haskell defect. It changes no Haskell source. It runs no
Haskell or native product checks. Preserve all earlier Haskell findings. Record
every later Haskell fix in root `FINDINGS.md` for the external agent.

The 137-line Lean proof needed a namespace correction, a qualified availability
name, removal of an extra `rfl`, and the rewritten encoding equality. The flags
proof needed reduction of the literal returned tuple. The waiting proof needed
existing arithmetic automation in place of unavailable unqualified names. The
cache composition needed a direct namespace import. The reached-read proof needed
a local actual-call match type before result generalization. Its original closed
decision definitions and public declaration stay unchanged. These are Lean proof
repairs. All failed inputs and outputs remain retained.

A rejected reached-read draft specialized public Edge equality and had an
incorrect unchanged-statement flag. That draft failed. Both the draft and the
incorrect record stay retained beside the correction. The final public declaration
is byte exact to the original. The earlier premature public-read completion flag
also remains sealed beside a separate timing correction. Later full reads and
independent review confirmed the statements. They do not change the earlier record.

## Evidence and process limits

Normal control: `/tmp/mcfta-incoming-state-control-20261101`.
Pair feedback: `/tmp/mcfta-incoming-no-handle-indexes-feedback-20261101`.
Cache/read feedback: `/tmp/mcfta-incoming-cache-and-read-feedback-20261101`.
Each feedback packet requires all its whole pinned external public providers.
R28 source and document checks use its immutable source snapshot. R28 archive
publication and fresh reconstruction remain pending. Disk cleanup has a pending
question with two exact targets and sizes. Do not delete either without approval.

The older native-prefix owner read 101 lines of a 160-line third OLD original.
Its 89-line candidate remains uncompiled. Retain the candidate, the failed budget
check, and the later 94-line mathematical repair. That repair does not remove
the older native-owner process failure.

Keep all three permanent source-scope failures visible. The known bounded root
ledger is 153 CFTA lines across five originals. Its complete indirect locator
audit is not claimed. The proof author's boundary remains 262 acquisitions and
4,206 CFTA lines across 94 originals, plus 18 standard-library lines across three
originals. The review boundary remains 464 CFTA lines across 12 originals, with
the same two named whole originals. No owner received an extra old-source budget.
Mathematical checks and byte integrity pass within the stated bounds. They do
not remove the recorded process failures or prove the full objective complete.
