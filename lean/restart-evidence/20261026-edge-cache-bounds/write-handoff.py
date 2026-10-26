from pathlib import Path
import json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-edge-cache-bounds-20261026')
commits=json.loads((area/'source-commits.json').read_text());checked=json.loads((area/'verified-checks.json').read_text())
block=f'''## Original cache bounds now cover actual traversals and captured edges

Traversal: `{commits[0]['commit'][:9]}`. Edge and final write: `{commits[1]['commit'][:9]}`.
The goal stays ACTIVE. H6 remains the strongest end-to-end language theorem.
Main `6c080537a` remains imported. All earlier Haskell repairs remain merged.

The actual traversal and edge bounds now come from the original outer cache.
For counter C, suspended mass B, own-class count T, child count A and inherited
bucket length L, the returned captured-edge cache has counter <= C + T + A
and mass <= B + A * (L + T). Complete and actual stopped caches are covered.
The final captured-slot write keeps the counter and cannot add pending mass.
Missing caches and unhandled results remain explicit.

The child upper bound no longer needs alignment. Nonnegative slot replacement
adds at most the incoming bucket length. This permits direct structural
traversal observers without Safe, range or completion premises. The full
traversal, selected-edge and captured-edge resource producers each retain
EVERY earlier conclusion. Each old producer runs once. The bounds apply to
that same derived result. Rejection still supplies no Safe claim.

All eleven new proof modules and Audit pass strict checks. Aggregate Audit
passes 3868 jobs and checks 77590 theorem dependencies. Installed readback
covers 21 declarations and 12 full worker definitions. Only the permitted
axioms occur. H6, earlier APIs, runtime workers and Haskell remain unchanged.
FINDINGS records that no new Haskell defect or repair was established.

Next derive a conservative recursive reservation from the original outer
seed and these actual edge bounds. Pay the complete callback subtree before
each next sibling. Thread its actual reached native caller and full memos.
Restore only the captured enumeration cache and metadata. The earlier
edge-only cost does not pay recursive subtree work. Complete depth-two scans,
general finite recursive capacity, whole-enumerator language and Haskell
correspondence remain open. Details:
`lean/notes-current-pruning-edge-cache-bounds.md`.

'''
findings='''### Traversal and captured-edge cache bounds

The formal cache bound now covers actual child traversals, selected edges
and the final captured-slot write. It counts every original child and every
repeated suspended entry. Direct scalar observers need no safety premise.
The full resource producers retain their earlier native and cache contracts.
Rejected caches receive no new Safe conclusion.

No Haskell source changed. No runtime defect or new repair was established.
External action: no additional patch. Keep all six earlier merged repairs
and the merged Sized documentation repair in PR #178. Keep their evidence.
Details: `lean/notes-current-pruning-edge-cache-bounds.md`.

'''
note=f'''# Original cache bounds through captured edges

Published base: {(area/'base.txt').read_text().strip()}.
Imported main: {(area/'main.txt').read_text().strip()}.
Traversal commit: {commits[0]['commit']}.
Edge commit: {commits[1]['commit']}.
The full formalization goal stays ACTIVE and incomplete.
Keep the optimized interned core. Earlier constructor and equality work
remain secondary targets. All earlier counterexamples and restart records
remain available. The earlier child checkpoint is in
`lean/notes-current-pruning-child-cache-bounds.md`.

## Current claim and boundary

H6 remains the strongest end-to-end language theorem. Covered closed
construction and valid constraint allocation derive sufficient fuels and
one mathematical width for any prescribed finite number of modeled
node-processing rounds. The final finite-tree language equals the original
language under formal Formula and Entailment. The inherited payload is empty.
This is not a convergence or concrete Haskell correspondence theorem.

The actual recursive driver has a depth-one resource theorem. Its callback
can also execute a depth-one driver. A complete depth-two outer scan remains
open because its full subtree work is not yet reserved before later siblings.

This checkpoint closes the original child and edge scalar accounting step.
For an actual attached child cache, counter grows by at most one and mass
by at most the incoming bucket length. This upper bound needs no alignment.
The older exact ordinary mass theorem retains its alignment premise.

For a traversal with original inputs, counter grows by at most inputs.length.
Mass grows by at most the sum of their original bucket lengths. A stopped
result bounds its actual optional cache. An absent cache stays absent.
The theorem does not assert execution of the remaining children.

For a selected or captured edge, let C and B be the original counter and
suspended mass. Let T be projected tries.length, A be edge.children.length,
and L be inherited scs.length. Each actual returned cache satisfies:

- counter <= C + T + A;
- suspended mass <= B + A * (L + T).

Own-class allocation adds T slots and no mass. The exact actual own payload
supplies the ordered child buckets. Descent can only remove suspended entries.
Residual recording preserves both scalars. Final target recording preserves
the counter and can only remove suspended mass. Every repeated entry counts.

## Installed APIs

- `CachedPrepare.singleton_counter_mass_bound` adds the direct nonterminal
  upper bound without alignment. It uses a nonnegative List.set inequality.
- `ChildDispatch.observed_scalar_bounds` covers all actual child cacheSome
  returns without alignment, Safe, native Context or range premises.
- `ChildTraversal.observed_scalar_bounds` covers actual complete results and
  stopped candidates at every fixed fuel. It threads the actual reached cache,
  caller and query state into the next child.
- `CostBounds.bucket_sum_le`, `child_bucket_le` and `children_bucket_sum_le`
  bound the original complete sum and count every child position.
- `CachedOwn.suspendMany_core`, `suspendedState_scalars`, `suspendMany_scalars`
  and `prepare_scalars` give actual own-prefix core and scalar receipts.
- `CachedOwn.suspendMany_vars` and `prepare_inputs` give the exact original
  suspended variables and the complete prepared child payload.
- `SelectedEdge.finish_scalars` preserves counter and mass at residual recording.
- `Finalize.enumerated_mass_le` and `run_scalars` bound actual finalization.
- `SelectedEdge.observed_scalar_bounds` and `CapturedEdge.observed_scalar_bounds`
  give the original edge formulas for actual complete and stopped caches.
  Unhandled results and missing caches remain explicit.
- `TraversalCompletion.complete_with_fragments_cache_bounds`,
  `SelectedEdge.complete_with_fragments_cache_bounds` and
  `CapturedEdge.complete_with_history_cache_bounds` retain their ENTIRE earlier
  input and output contracts, then append the two scalar bounds. Each calls
  its old resource producer once and observes that same base-fuel result.

All numerical observers are separate from safety and native semantic claims.
All earlier Post, memos, query equality, stable fuel equations, cache witnesses,
roots, counts, flags, origin, protection, references, history, fragment facts,
Fits and guard-carrier conclusions remain in the three full producers.
The rejected arm has no added Safe fact. The original admissions remain.

## Verification

Lean 4.34.1 checks all twelve changed sources with warningAsError and all
linters. Aggregate Audit passes 3868 jobs and checks 77590 theorem dependencies.
Only propext, Classical.choice and Quot.sound are permitted.
Installed readback covers 21 declarations and 12 full definitions.
It has {checked['public_lines']} lines and {checked['public_bytes']} bytes.
SHA256: {checked['public_sha256']}.
All heavy checks ran serially with memory.max = memory.high = 4294967296
and memory.swap.max = 0. Exact commands and cgroup limits are retained.
The old dependency warning in InternedFreshOrdinaryClosedCompletion at line
24 remains outside the changed strict sources.

The H6 source remains byte-identical. Its SHA256 is
e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5.
All earlier runtime and completion source bytes remain unchanged.
No Haskell source changed. No Haskell tests or formatters needed a rerun.
FINDINGS retains all earlier repairs and records no new Haskell repair.

Evidence: `lean/restart-evidence/20261026-edge-cache-bounds`.
Live area: `/tmp/mcfta-edge-cache-bounds-20261026`.
The manifest records payload lengths and SHA256 values. Raw logs are compressed
losslessly. Reports record their decoded lengths and hashes. Final source
snapshots, installed readback, the full raw patch, failed strict attempts,
marked original proposals, source review and contract comparisons are retained.

## Approaches and corrections

A separate alignment proof through every worker was considered. It would
repeat the fold, incoming, terminal and child case analyses. The nonnegative
slot replacement inequality instead removes alignment from the upper bound.
The direct traversal observer then needs no additional admission or completion.
The three full wrappers each keep one original producer call.

The generic replacement proof required an explicit weight function and a
change to the exact weighted sum goal. Selected-edge action erasure required
local match reduction before the existing list-map identity. Captured-edge
finalization required reduction of its selected-result match. Redundant simp
and dsimp steps were removed for strict linters. The local binder protected
was renamed because Lean reserves that word. No heartbeat limit or premise
was weakened. All failed checks remain in the evidence.

## Next proof obligation

Apply the captured-edge bounds to each actual head receipt from
`NativeBranchCompletion.head_complete_resources`. Use the original finite
guard carrier and native profile to bound the projected tries and child count.
Derive the callback-input suspended mass from the original captured cache.

Define a conservative reservation for recursive depth and the remaining
ordered siblings. The reservation must pay the complete reached callback
subtree before the next sibling. Use the actual subtree Post, returned caller
and full memos. Restore the captured sibling enumeration cache and metadata.
Do not identify independently run heaps or shared memo histories.

Use the current callback-one producer and subtree-effects transport to build
the complete depth-two scan from original outer inputs. Then generalize the
reservation and execution proof to arbitrary finite recursive depth. Retain
all explicit unsupported, exhausted, rejected and nested-stop results.
The old edge-only cost is insufficient for this step.

Whole-enumerator language, terminal outer fallback semantics, native Graph
correspondence, physical containers and machine integers, extraction,
arbitrary lazy demand, convergence and practical resource bounds remain open.
Mathematical width admission does not establish a physical memory bound.
'''
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
marker='## Actual child cache growth now follows from original inputs'
for rel in docs:
 p=root/rel;s=p.read_text();assert s.count(marker)==1 and block.splitlines()[0] not in s,rel
 p.write_text(s.replace(marker,block+marker,1))
p=root/'FINDINGS.md';s=p.read_text();marker='### Actual child cache bounds and external Haskell status';assert s.count(marker)==1
p.write_text(s.replace(marker,findings+marker,1))
rel='lean/notes-current-pruning-edge-cache-bounds.md';assert not (root/rel).exists();(root/rel).write_text(note)
(area/'handoff-content.json').write_text(json.dumps({'block':block,'findings':findings,'note':note,'docs':docs,'note_path':rel},indent=2)+'\n')
print('Updated current proof status, external Haskell status and detailed restart note.')
