# Root support from retained literal records

Final source: `lean/MicroCFTA/SourceCurrentSelectedRootOrigins.lean`.
SHA-256: `fb5054aff43874c9481e5161fec08190677902a33013afde75cbf7cdf75bc385`.
The source has 98 lines and two public theorem heads.

## Exact public contract

`selected_primary` takes a literal successful `AllocatedRecordScanWorker.scan` equation and membership of one record in its returned retained list. It derives membership of that record in the input list and an actual false primary call for its paths at existential checked states.

`selected_root` adds an original member path `index :: suffix` and a successful lookup of that original forest slot. It derives `ActualRequiredRowOrigins.Root` for the complete value in that slot.

No physical Good, availability, heap semantic invariant, coherent-record predicate, whole-forest closedness, finite Cap, memo correctness, global validity, replay, range, future completed graph, or desired root-support law is a premise. The decidable-equality instances are those of the literal worker.

`Root` is the existing shape predicate. Ordinary nodes and Empty satisfy it directly. Recursive and reference alternatives use the actual unconstrained test. The theorem does not replace Root with a stronger hereditary annotation.

## Literal branch proof

The proof inducts on the input record list. It splits each actual successful bind. The false-primary branch is the only branch that prepends a retained record. A failure in its suffix cannot match successful scan completion. A retained suffix record follows the induction hypothesis.

Primary true followed by secondary true recurses without retaining the head. Primary true followed by secondary false executes the actual query and decision. Decision true returns an empty retained suffix. Decision false follows the actual recursive suffix call. These cases account for every successful literal branch without requiring semantic correctness of the query, decision, or fourth memo.

A small private inversion removes the scan gate wrapper and recovers its literal primary false equation. `PrimaryRootSupport.primary` then supplies Root from the actual selected path and original slot. Scanning always uses the same original value list, even when its heap changes. Root depends only on the value, so no heap transport is required.

Repeated records need no uniqueness premise. The exported extraction returns input membership and an existential actual primary equation. It does not export a separate complete chronological prefix receipt or identify a unique occurrence when records repeat.

## Constructed validation

The fixture builds an ordinary source container with two distinct productive Mu children. One Mu has an extra alternative. It constructs a nonempty class record with paths `[[0],[1]]` and scans two occurrences of that same record.

The actual scan uses primary fuel two and zero secondary, projection, read, native, and conjunction bounds. Both primary calls return false, so both literal records are retained. The theorem is applied to a present original recursive slot. The fixture derives its Root support and an actual false-primary equation. It also checks actual source construction, slot availability, and the recursive constructor tag.

No worker return, future heap, memo invariant, or desired Root is a fixture premise. The source construction and bounded scan are checked in the private witness. The public theorem aliases that proof with the same explicit statement. This fixture exercises the selected branch and repeated records; it does not claim a constructed secondary or query branch.

## Validation and preserved attempts

Selected strict source: `selected-root-direct-4`, terminal zero and an exactly zero-byte log. Selected canonical: `selected-root-canonical-2`, 1788 jobs. The canonical log replays the unchanged warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`; the final owned source has no warning.

Selected exported group: `selected-root-public-1`, two full signature/proof/axiom pairs.
Selected constructed strict group: `selected-root-kernels-2`, terminal zero and an exactly zero-byte log.
Selected constructed group: `selected-root-kernels-public-1`, one full pair.
All probes use the eight required options and `#check @`. Only the three standard axioms are permitted.

Every check executes an immutable numbered source snapshot. The inner worker records effective memory.max and memory.high of 4294967296 bytes and memory.swap.max of zero. Each job has a five-minute limit.

Direct attempt one retains width elaboration failures and unused-instance warnings. Direct attempt two retains an equality-target error. Attempt three and canonical one passed but retain unused private-helper instance warnings, so they are not selected. Attempt four moves those instance binders and is genuinely empty. Fixture attempt one retains the unavailable `Classical.decEq` spelling. Attempt two uses the pinned toolchain's classical instance syntax and passes. All failed and superseded sources and raw logs remain unchanged.

## Remaining boundary

The producer requires actual successful scan completion. It does not prove completion, numeric sufficiency, semantic correctness of retained classes, a post-edit root law, selected child-row lineage, or outer active-key exclusion. Root support concerns original forest slots only. Later Required and class-edit consumers must transport their own actual outputs.
