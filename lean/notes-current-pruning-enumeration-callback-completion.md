# Finite completion of the concrete fragment callback

## Current result

Partial rendering and parked matches: `4880eef42`.
Concrete callback and Audit import: `32ceddf6c`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The concrete modeled Left callback now derives an actual finite execution
from Safe storage, allocated fragment holes, allocated parked IDs and the
existing Stratified dependency levels. The proof supplies rendering and
every pending-group read. It assumes no successful render, resume or callback.
The result retains the actual cache endpoint, its full compression frame,
safe storage and the same dependency levels. Callback rejection remains
a completed result. No acceptance or pruning-language theorem is added.

## Partial rendering

EnumerationPartialCompletion.getValue_complete constructs an actual bounded
slot read. Totality supplies a root path. Forest bounds keep the root allocated.
Supply alignment supplies its stored slot. The actual findRoot execution
then produces getValue and its RenderStable receipt.

expandPartial_complete uses EnumerationOrder.Stratified. Equivalent variables
have the same level. Every stored enumerated fragment refers only to holes
at strictly higher levels. Each expanded root has a level below the frontier.
Following an enumerated fragment therefore decreases frontier minus level.
Structural recursion handles concrete fragment children. All finite child
traversals share a derived sufficient fuel bound.

Pending slots stop as holes. An unconstrained recursive boundary produces
the existing truncation marker. Other pending slots retain the original raw
hole ID. No Finished, CompleteGraph, graph-bearing value, empty template
catalog or hole-free fragment premise is needed.

The full Frame comes from the actual rendering execution. RenderStable comes
from bounded compression reads. stratified_read retains the same levels.
The input Stratified invariant is genuine. Safe storage and bounded holes
alone do not exclude a stored fragment that refers to its own class.

## Parked matches and the concrete oracle

SourcePruningResume.resume_complete constructs finite representative reads
for each parked entry from UnionFind.Total. Pure matching produces either
a pending result or none. A none result does not omit later state reads.
mapM_terminates and existing moreFuel theorems supply a common bound.
The successful resume retains the complete compression Frame.

resume_read separately proves RenderStable from Safe and allocated parked
IDs. The actual representative_read receipt preserves the allocation counter,
so each later parked reference keeps its bound. Frame alone never supplies
Safe. A missing raw ID outside the allocation domain can have a finite
representative lookup that inserts an out-of-range forest root. This is
a proof admission boundary, not an established reachable Haskell defect.

oracle_inl_complete preserves early rejection and the idle fast path. The
observe branch renders once, then resumes every pending group in source order.
It combines pure results only after all those reads. The proof raises render
and group fuels to one common bound without changing terms, results or the
actual final state. A rejected match remains a completed callback result.

recordTypes_inl_complete retains the empty-catalog pure branch. Other calls
use that same concrete oracle witness and endpoint. The final metadata has
the exact updatedTypes result. openHoles and typing stay unchanged.
The older inr theorem still supplies the pure pre-expansion event.

## Verification and evidence

All five changed modules pass Lean 4.34.1 with all linters and warnings as
errors. Eight strict attempts contain three retained failures: the first
partial proof refers to a helper outside its imports; the second leaves
a term witness unresolved; the first callback proof has a record-layout
parse error. The corrected final five module checks pass. No runtime worker
or older theorem declaration changes.

Two installed helper builds pass. The aggregate Audit passes with 3760 jobs
and 76754 checked dependencies. Installed public readback checks six new
declarations and the unchanged H6 declaration. Its full output has
142 lines and 10280 bytes. Its SHA-256 is
`fd00704c8b1ae991af3731314a84824af8d78ccb4f3b219959cc198e2cfb60ab`.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The old unused inputs warning remains unchanged. All twelve checks run
serially under 4 GiB heavy-management caps with no swap.

Source review confirms the strict rank decrease, bounded-read safety, all
pending groups and actual callback endpoint. Existing runtime and theorem
text in Resume and Oracle remains byte-identical apart from the one new
import and appended proofs. Audit adds one import. H6, native workers and
all Haskell sources stay unchanged. No Haskell suite is repeated.
Full attempted inputs, logs, reports, final source snapshots, proof patch,
cap records and preservation checks are in
restart-evidence/20261025-partial-completion.
Root FINDINGS keeps the external Haskell handoff first. No new Haskell
runtime defect or repair is identified.

## Remaining work and strongest claim

The theorem does not export allocated IDs for returned metadata.pending.
Prove bounds for resumed representatives and newly parked holes in the
actual partial term. Then preserve those bounds through repeated callbacks.

Native traversal, merges and final fragment writes still need to establish
and preserve Stratified. Reuse the existing traversal_stratified and
write_stratified design. PendingReferences tracks suspended equality
references. It does not establish acyclic stored-fragment dependencies.
Derive pending targets for returned fragment holes at each actual endpoint.

Callback integration must use each successful branch receipt's own Caller,
memos, queries and cache. The serial scan's final Caller cannot replace that
endpoint. Native-heap/Graph correspondence, callback and recursive-loop
interleaving, arbitrary Haskell forcing, scheduler restart and whole-driver
language semantics remain open. Initial-only numeric admission still needs
the quantitative scheduler forecast described in the selected-ordinary note.
This checkpoint proves no whole-loop progress, termination or convergence.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache, original allocation history and any
prescribed finite budget and modeled node-call rounds derive sufficient
finite bounds and one mathematical width chosen after construction. With
empty inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.
Concrete solver and physical runtime correspondence remain outside that claim.
