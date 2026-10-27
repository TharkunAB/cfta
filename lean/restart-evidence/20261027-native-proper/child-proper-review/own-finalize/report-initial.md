# Own allocation and finalization ProperState observers

Recorded 2026-10-27T23:00:31.725588+01:00. OPEN, V1 UNTESTED.
No compiler/runtime, repository/Git, network or board operation by this worker.

New module SourcePruningEnumerationOwnFinalizeProper mirrors exactly the five
existing OwnFinalizeCanonical observer shapes. It adds five theorems and no
new operational definition, predicate, structure, helper declaration or instance.
All original operations and published theorems remain unchanged.

CachedChild.allocate_proper: initial ProperState plus actual allocate=some(uv,after)
identifies the actual allocated core and applies graph-independent allocation_proper.
The native guard and enumeration guard remain independent. No available/closed
node assumption is added because only the stored-bucket property is asserted.

CachedOwn.suspendMany_proper: the actual Option bind/map receipt identifies each
allocation of a node=None slot and the actual suffix cache. Induction applies
allocate_proper once per class in the actual order. Empty input returns the
identical original cache. Tries may be arbitrary here: the stored fresh slots
have empty buckets. This theorem does NOT assert ProperInputs for the returned
suspended list, and does not validate supplied trie contents. Later child
inputs need their own genuine valid/nonempty projection or descent facts.

Finalize.written_proper: the supplied exact slot-write equation identifies the
actual reset+write core. Every member of the written value list is an old proper
value or the new enumerated fragment. The latter has ProperValue=True.
The four-line membership proof requires no additional public pure-set helper.

Finalize.run_proper: the actual run=some after receipt exposes the real old-slot
lookup, candidate classification and both count passes of NativeIndex.write.
Their actual final constructor fixes the after cache. written_proper applies
to that SAME core, including expansionAncestry=[]. No missing-slot success,
count adequacy, endpoint equation or final properness is assumed separately.

SelectedEdge.finish_proper: residual recording changes only obligations. The
ProperState predicate reads only core.values, so the proof is definitional.
It does not claim that the residual is satisfied or that rendering succeeds.

The modules impose no ordinary-only restriction and do not construct a Graph.
These operations preserve empty Mu/Union buckets and enumerated values.
The completed producer resource packets, Safe/index correctness, acceptance,
Discharged, coverage and physical Haskell correspondence are not derived here.
Whole native ProperState preservation still needs actual incoming/terminal/
child/traversal/selected/captured composition. Those are separate producers.

V1 path and SHA are in draft-identity.json. Exact original source copies and
literal focused cuts are in the shared source-index.json. The source review
found no semantic blocker. The remaining current validation risk is Lean
reduction of actual reset+write to written_proper's exact displayed record;
Root will compile it. No fabricated final endpoint is introduced.
