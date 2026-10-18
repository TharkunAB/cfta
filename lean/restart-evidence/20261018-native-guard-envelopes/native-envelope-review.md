# Initial native raw guard envelopes

Updated: 2026-10-18T04:01:16.348653+00:00.

## Checked result

`SourceCurrentNativeGuardEnvelope` has three public heads.
`advance` iterates GuardLimits.step in the exact extension order of the
finite NativeGuardAlphabet.advance schedule. `alphabet_advance` bounds every
literal guard in that scheduled alphabet from bounds on its initial members.
The proof covers retained guards, source Top and each ordered full source
conjunction. It does not change list order or remove duplicate occurrences.

`complete` takes the initial generated-query support, a finite initial
alphabet, initial heap membership in that alphabet, and Bounds on every
alphabet member. It invokes GeneratedQueryGuardResources.complete to construct
its own actual native query receipt and returned carrier. The pure alphabet
lemma converts that carrier to a flat AnnotationHeap.Heap of raw Bounds.
The guard-limit extension count is the instructionBound computed from the
INITIAL numeric profile. No future query result, Trace, carrier or guard law
is supplied.

The query receipt retains its full original contract, same physical output,
Frame, Fits and source query semantics. Its selected operands are resident
and closed as required by the existing initial query producer. Arbitrary
nested Mu operands remain permitted. The theorem adds no hereditary finite
ordinary domain, finite Cap, global plain edge heap or whole-heap closure.
Its Heap annotation constrains raw stored edge guards. This is distinct from
the causal GuardHeap predicate about recursive payloads.

Initial Frame/Fits/Room, operand availability and closedness, alphabet facts
and global validity remain explicit. Root's separate GuardHeapBounds module
constructs initial alphabet limits. This module does not assume or prove a
whole outer resource schedule, all-failure semantic preservation, owner-key
exclusion, fresh-call bounds or general termination.

## Source audit and next exact obligation

The original read-only question concerned walk_tail semantic transport.
AllocatedPartialActual.lean:209-225 already proves the semantic walk-cons
step from actual Reads and reached Checks. It derives the head's NodeLaw and
Post, then uses that Post as the tail context. Its ordinary node case at
130-138 applies raw reconstruction after the row result. These language laws
have no finiteordinary or Cap premise. NodeTerminalNumeric.complete already
covers empty, explicit union and resident Mu cleanup at the unchanged caller.
RawRebuildNumeric.edge/modify already retain Frame/Fits for available payloads.
The missing initial producer must construct those smaller Reads and Checks
without a future-entry resource callback.

The first assessment suggested an inherited path carrier was needed for
Parent class sizes. That was too strong and is corrected here. GuardOwn's
precheck proof at 73-92 uses the original own payload. Its receipt theorem
and ParentUniformNumbers.receipt_rows need no inherited-size bound. Initial
raw Bounds therefore control actual precheck class/path counts and depths.

A separate exact-syntax issue remains for a majorant of the CURRENT numeric
forecasts. ConstrainedCapEditListNumeric.lean:39-43 uses sizeOf edits. Edits
contains signed indices and callback paths (SourceEqualityEdits.lean:16-18).
Thus path count/depth Bounds do not alone give that syntax-size ceiling.
A family with paths [[0],[k]] retains count/depth while index syntax grows.
A finite alphabet max over its exact own-record forecasts avoids this loss
of information. An explicit initial index bound or a new pruned-trie schedule
would be different solutions. No new proof about that family is claimed here.

Recommended next theorem: from initial Context, Frame/Fits, combined Ready,
available walk inputs and ONE pure fixed-outer-fuel resource reservation,
a literal successful walk should derive its own WalkReads, Post, returned
Frame/Fits and WalkLaw. Prove it by mutual fuel/phase induction. Each rows or
walk cons decreases fuel; same-fuel control changes are acyclic. Parent
semantic alignment supplies each actual edge call. Raw rebuild and terminal
receipts supply the remaining local transitions. The needed resource-envelope
and full mutual producer are not proved by this component. A successful
enclosing node call must not be an input to that prefix theorem.

## Validation and ownership

Production SHA256: `f59271e880b1502fdd97cb81718050c6cc5921ec599dee0c4bff6e3be47d16d9`.
Selected strict native-envelope-direct-1: exit 0, raw log 0 bytes.
Selected canonical native-envelope-canonical-1: terminal 0, 1422 jobs.
The canonical log replays only the unchanged ClosedCompletion warning.
Selected native-envelope-public-1: three complete pairs, all eight settings,
standard axioms only, no omitted proof or printer failure. The definition
advance is included in public coverage. Every selected execution records
4294967296-byte MemoryMax and MemoryHigh, zero swap and a five-minute cap.
The peak log is component-specific. The first strict attempt passed; there
is no failed Lean attempt in this component.

This package counts three public pairs and zero constructed pairs.
The separate native-envelope-kernels prefix is owned by required_memos.
It is excluded from this immutable component manifest. No old source,
evidence, Audit, authority document, Haskell or Git state was changed.
