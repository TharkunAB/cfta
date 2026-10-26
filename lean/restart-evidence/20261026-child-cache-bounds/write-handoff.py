from pathlib import Path
import json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-child-cache-bounds-20261026')
commits=json.loads((area/'source-commits.json').read_text());summary=json.loads((area/'verified-checks.json').read_text())
block=f'''## Actual child cache growth now follows from original inputs

Scalar components: `{commits[0]['commit'][:9]}`. Complete child: `{commits[1]['commit'][:9]}`.
The goal stays ACTIVE. H6 remains the strongest end-to-end language theorem.
Main `6c080537a` remains imported. All earlier Haskell repairs remain merged.

The full child resource producer now retains its entire earlier result and
adds numeric bounds on the SAME actual returned cache. Its counter grows
by at most one. Its total suspended mass grows by at most bucket.length.
The producer uses the original Packet facts and reservation. It calls the
earlier child producer once. No future cache bound, successful suffix or
range is an initial premise. Valid rejection still supplies no Safe claim.

Actual dispatch singletons, all outer fold result tags and attached fold
caches preserve counter and suspended mass exactly. The terminal prefix
changes only the forest. Incoming outer reads preserve values and counter.
An attached incoming cache adds exactly incomingScs.length, including the
reconstructed Empty write. Ordinary children add the whole incoming bucket.
Mu and union children allocate an empty bucket. Empty retains the input.
The universal child mass statement is therefore an upper bound.

Seven new proof modules and Audit pass strict checks. Aggregate Audit passes
3857 jobs and checks 77543 theorem dependencies. Installed readback covers
18 declarations and 11 full worker definitions. Only the permitted axioms
occur. H6, earlier APIs, runtime workers and Haskell remain unchanged.
No new Haskell defect or repair was established. FINDINGS records this status.

Next lift the actual child bounds through complete and rejected child
traversals. Derive edge counter and mass bounds from the original outer
cache, including own-class allocation and final target writes. Then reserve
full recursive subtree work before each next sibling and thread the actual
post-subtree caller and full memos. General finite recursive capacity,
whole-enumerator language and Haskell correspondence remain open. Details:
`lean/notes-current-pruning-child-cache-bounds.md`.

'''
findings='''### Actual child cache bounds and external Haskell status

The formal child producer now adds at most one slot and at most the original
bucket length in suspended mass. It retains its entire earlier certificate
and its actual returned cache. Raw rejection does not imply safety.

Source inspection distinguishes ordinary allocation from Mu and union
allocation. The latter store an empty bucket. The universal mass statement
uses an upper bound. No Haskell runtime defect follows from this distinction.
No Haskell source changed. No new repair or external patch is proposed.
All six earlier runtime or documentation repairs remain merged. The Sized
documentation repair is also merged in PR #178. Keep all historical evidence.
Details: `lean/notes-current-pruning-child-cache-bounds.md`.

'''
note=f'''# Actual child cache bounds from original inputs

Published base: {(area/'base.txt').read_text().strip()}.
Imported main: {(area/'main.txt').read_text().strip()}.
Scalar components: {commits[0]['commit']}.
Complete child: {commits[1]['commit']}.
The full formalization goal stays ACTIVE. This checkpoint is incomplete.
Keep the optimized interned core. Keep earlier constructor and equality work
as secondary targets. Earlier restart records and counterexamples remain valid.

## Strongest current statement

H6 remains the strongest end-to-end language theorem. Covered closed
construction and valid constraint allocation derive one mathematical width,
sufficient fuels and an actual finite trace for any prescribed finite number
of modeled node-processing rounds. The final value has exactly the original
finite-tree language under the formal Formula and Entailment interpretation.
The inherited payload is empty. The theorem does not assert convergence.

The actual recursive pruning driver has a depth-one resource theorem.
It includes stop, done, stuck, parked, Empty, ordinary and fallback routes.
Every output retains its own full Post, memos, Packet and resources.
A rendered callback also executes the actual depth-one driver at one common
work bound. Its reservation comes from the callback-input cache. This does
not yet establish a complete depth-two scan from the outer input cache.

This checkpoint derives original numeric bounds for each complete child.
For original counter C, suspended mass B and input bucket length L, its same
returned cache satisfies C <= counter <= C + 1 and mass <= B + L.
The earlier producer supplies the lower counter bound and all earlier facts.
Rejected raw [] results retain the actual cache without a new Safe claim.

## Public proof components

`SourcePruningEnumerationFoldCacheBounds.lean` adds:

- `Fold.dispatch_counter_mass`: actual singleton dispatch preserves counter
  and suspended mass. `DispatchShape.singleton` gives its exact two cases.
- `Fold.singleton_core`: the actual raw singleton core equals the outer core.
- `Fold.observed_counter_mass`: all outer fold tags preserve both scalars.
- `CachedFold.observed_cache_bounds`: every attached cache preserves both
  scalars, including raw rejection. No Context, range or Safe premise is used.
- `CachedFold.observed_bounds`: the exact full observation retains the bounds
  on both its outer core and its attached cache.

`SourcePruningEnumerationTerminalPrefixBounds.lean` adds `success_frame`
and `observed_counter_mass`. Successful representative scans and unions
change only the forest. These are direct observers of the actual prefix.

`SourcePruningEnumerationIncomingMass.lean` adds `IncomingNode.run_mass`,
`IncomingCacheAdapter.observed_cache_bounds` and `CachedIncoming.written_mass`.
Outer reads preserve values and counter at all result tags. Successful raw
singletons and attached caches retain exact mass B + incomingScs.length.
The Empty adapter reconstructs the post-write cache. It does not return the
outer read core. These numerical facts assert no native Post or safety.

`SourcePruningEnumerationNonterminalCacheBounds.lean` adds exact allocation
mass, exact singleton counter and shape-specific mass, the uniform singleton
upper bound, and the exact Empty cache equation. The original alignment
counter = values.length is required for the ordinary fresh-slot equation.
Ordinary nodes add L. Mu and union nodes add zero. Each singleton adds one
slot. Empty rejects before allocation.

`SourcePruningEnumerationTerminalCacheBounds.lean` composes actual prefix,
fold and incoming observations. Attached terminal caches keep the original
counter and add at most the incoming descendant bucket length.

`SourcePruningEnumerationChildCacheBounds.lean` composes all child routes.
It needs only original alignment and the actual attached-cache equation.
It adds at most one slot and at most the complete original bucket length.
It keeps read, raw, outer and attached cores distinct.

`SourcePruningEnumerationChildBoundedResources.lean` adds
`ChildCompletion.complete_with_fragments_cache_bounds`. Its inputs are the
unchanged inputs of `complete_with_fragments_resources`. Its output retains
EVERY earlier field, then adds the two scalar upper bounds. It calls the
old producer once and observes that same derived execution at canonical fuel.
The full output-prefix and single-call check is in contract-retention.json.

## Verification and evidence

Lean 4.34.1 checks all eight changed sources with warningAsError and all
linters. Aggregate Audit passes 3857 jobs and checks 77543 theorem
dependencies. Only propext, Classical.choice and Quot.sound are permitted.
Installed public readback covers 18 declarations and 11 complete definitions.
Its output has {summary['public_lines']} lines and {summary['public_bytes']} bytes.
SHA256: {summary['public_sha256']}.
Every heavy check ran serially under memory.max = memory.high = 4294967296
and memory.swap.max = 0. Exact commands, limits and output hashes are retained.
The unchanged dependency warning in InternedFreshOrdinaryClosedCompletion
at line 24 remains outside the changed strict sources.

H6 SHA256 remains
e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5.
All earlier runtime and completion source bytes remain unchanged.
No Haskell source changed. No Haskell test or formatter rerun was needed.
All earlier merged Haskell repairs and evidence remain in FINDINGS.

Evidence: `lean/restart-evidence/20261026-child-cache-bounds`.
Live check area: `/tmp/mcfta-child-cache-bounds-20261026`.
The manifest records every payload length and SHA256. Raw logs are compressed
losslessly. Their decoded lengths and hashes match their original reports.
Strict snapshots include the failed attempts. Original proposals remain
marked drafts. The proof patch reconstructs all final proof changes.

## Approaches and corrections

A universal exact mass increment is false for the intended source cases.
Mu and union allocation stores no incoming bucket. The final theorem uses
an upper bound and preserves the separate exact shape equations.

Fold numeric conservation does not need native completion admission.
The actual dispatch shape theorem and structural fold induction suffice.
This avoids a second call to the native completion producer.

Incoming proof splitting first duplicated the runtime match across scalar
projections. The final proof splits one exact observation tuple. It reduces
native phase bindings only after ordinary case splitting stops. A private
helper originally fixed Fault : Type. The actual native error sum has type
Type 1. Fault : Type _ fixes that mismatch. Explicit runtime projections in
the public statement satisfy the strict DecidableEq linter. No heartbeat
limit, resource premise or safety conclusion was weakened.

## Next proof obligation

Lift the child bounds through each actual child traversal. Include complete
results and first valid rejection. Retain the entire earlier traversal
producer result and every own fragment and cache receipt. Prove intermediate
alignment from existing storage receipts rather than a future assumption.

For an original edge, pay own projected-class allocations and all children.
The intended bounds are counter <= C + tries.length + children.length and
mass <= B + children.length * (inherited.length + tries.length).
These edge formulas are NEXT TARGETS. They are not theorems in this checkpoint.
Include the final target write and count all repeated suspended entries.

Use the resulting original edge forecast to reserve complete recursive
subtrees before later siblings. Resume from the actual post-subtree caller
and full memos. Restore only the captured sibling enumeration cache and
metadata. Do not equate independently run native heaps or memo histories.
Do not reuse the old edge-only cost for recursive subtree work.

Full depth-two scans, arbitrary finite recursive capacity, whole-enumerator
language, terminal outer fallback semantics, native Graph correspondence,
physical containers and machine integers, extraction, arbitrary lazy demand,
and practical resource bounds remain open. Mathematical width admission
is not a concrete memory bound. Keep these boundaries in the top-level claim.
'''
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
marker='## Main is current and callbacks now execute one recursive expansion'
for rel in docs:
 p=root/rel;s=p.read_text();assert s.count(marker)==1 and block.splitlines()[0] not in s,rel
 p.write_text(s.replace(marker,block+marker,1))
p=root/'FINDINGS.md';s=p.read_text();marker='### Main template memo and positive recursive callbacks';assert s.count(marker)==1
p.write_text(s.replace(marker,findings+marker,1))
rel='lean/notes-current-pruning-child-cache-bounds.md';assert not (root/rel).exists();(root/rel).write_text(note)
(area/'handoff-content.json').write_text(json.dumps({'block':block,'findings':findings,'note':note,'docs':docs,'note_path':rel},indent=2)+'\n')
print('Updated nine current status records, FINDINGS and the detailed restart note.')
