# Current library proof status and complete initial mixed editor

This checkpoint starts at published 0c76ba40. Proof commits are c7c3b4e8
and 65cf78ee. Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of contracts. Specify the intended behavior first. Then
prove that the current Haskell implementation has that behavior. Initial
support and resources must not assume a later successful call or result.
Documented errors and validation order are observable results.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts. Passing builds do not give a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and rank/unrank inverses. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, including nested Mu and unions, with physical stores and causal payload bounds. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive reads | Initial resources construct closed recursive collection and row exposure with exact heaps, literal row widths, and stable replay. | Remaining callers and public correspondence. |
| Comparison and selection | Initial counters and causal mass construct repaired worker success with exact histories, heaps, and stable replay. | Remaining callers and independent language-law hypotheses. |
| General memo-aware Merge | Initial resources compute sufficient work and selection fuel. Full allocated replay retains equality state, heap, memo, and winner. | Remaining callers and Haskell runtime correspondence. |
| Recursive intersection | Supported closed operands construct stable semantic execution at initial computable fuel. | General constrained callers and public correspondence. |
| Native query programs | Initial forecasts construct supported finite indexed query sequences with language, stores, origins, globals, and resources. | Adaptive caller control flow and concrete capacity. |
| Selected Operand | Initial forest, signed path, counters, and causal mass construct projection then Merge, with exact full worker return, receipts, Profile, and Frame. | Remaining caller composition and concrete capacity. |
| Interleaved Target | Initial profiles and reservations construct the actual head Operand, recursive tail, and query sequence with complete receipts, states, and common-fuel worker result. | All-root cap and selected-domain assumptions remain explicit. Runtime correspondence remains open. |
| Shared Force and Leaf | Initial class facts, valid slot laws, and numeric reservations construct miss or hit Force, then Leaf's checked query at its actual return. Both preserve full shared state, receipts, Frames, profiles, caps, inventories, and global memos. | ClassPass composition and runtime correspondence. |
| Mixed editor | Initial finite trie, selected Safe domains, caps, Frame, stores, and numeric reservation construct complete node, forest, and compiled signed edits. Exact worker results retain every shared state field. | ClassPass composition and source runtime correspondence. |
| Class pass | Actual reads and source class order preserve stores and finite syntax depth. | Initial complete class fold and its resource forecast. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver proofs remain preserved. The Lean
definitions are handwritten. These component proofs do not yet establish
complete correspondence with compiled Haskell.

## Complete initial mixed editor

Eight additive modules extend the initial Force and Leaf producers.
Target and shared monotonicity let the all-miss schedule bound both actual
slot branches. Constructor and recursive Head bridges retain the complete
query Frame, numeric Fits, current inventory, Merge table, and target slots.
Receipt alignment retains historical slot inventories separately from the
current returned Frame inventory.

EditForecast.stageProfile bounds Head, raw constructor work, and every
possible class leaf. Its stageFuel bounds the corresponding worker fuels.
A finite syntax level determines planProfile. Each level fixes its row and
child limits from the scalar of its initial stage profile. The plan scans
those fixed limits before the final constructor stage. Profile monotonicity
and inflation retain every selected entry and return. One Room condition
on the complete initial forecast supplies every reached leaf reservation.
These are numeric ceilings. Size-based levels and fuels are noncomputable
logical definitions. They do not establish executable Haskell budgets or
count cumulative host instructions.

EditScans constructs ordered children and raw rows from the smaller-trie
induction hypothesis. A selected child passes its actual returned state,
Frame, inventory, stores, and global memos into the suffix. An unselected
child makes no node call. It only widens the scheduled numeric bound.
Row reconstruction retains the original symbol and full guard. The actual
child graph proves equal arity before raw makeEdge executes.

EditNumeric.node_complete proves the induction hypothesis for every finite
supported trie. It takes sizeOf edits at most the initial level. A leaf
constructs its actual Force and checked query. An ordinary node derives
original row and child widths from its initial stored payload mass. A
recursive node constructs Head first, then resumes the same trie at its
actual ordinary return. It does not execute an extra Head for an ordinary
input. Populated, HasLeaf, Allowed, selected Safe domains, input caps, and
captured-root caps remain explicit.

The same return retains an actual node graph and reads, complete physical
receipt, Frame, forecast Fits, target-slot and Merge certificates, and exact
worker result. Syntax fuel is 2 * level + 2. The five other worker fuels
use stageFuel at the complete initial profile. Existing replay gives every
larger tuple. MixedEdit.node derives the output cap from these same reads.

EditListNumeric.complete handles whole forests. An ignored root callback
returns the identical values and shared state at zero fuel. A below trie
uses the original forest length to fix the outer scan. The final fuel is
the maximum of syntax fuel and stageFuel at the initial finalProfile.
It covers all six worker arguments with one ceiling. The returned actual
list graph and reads retain the complete receipt, Frame, Profile, stores,
output caps, and exact common-fuel worker equation.

EditListNumeric.compiled uses the literal signed source build. The source
right fold supplies its populated trie and callback membership. The same
trie determines Safe, reservation, forecast, output cap, and editAll worker
execution. No NodeRanges, ChildrenRanges, RowsRanges, ListRanges, supplied
completed graph, successful future worker, reached heap bound, or resource
callback is an input to either complete editor endpoint.

## Constructed integration and source comparison

The concrete node and compiled-forest checks construct their own physical
class record, captured forest, checked state, query Frame, and valid equality
descent record. They build a parent with a nonempty equality guard and
children left, right, and an open recursion reference. The parent is proved
open and outside Cap 0. It has a genuine finite constrained ordinary prefix.
The selected left child is closed. The unselected open sibling remains in
the original input. No whole-parent closure or hereditary placement is used.

Each check chooses its own finite width from the pure initial final profile.
It constructs its actual graph, reads, full receipt, returned Frame, Fits,
slot and Merge laws, output cap, and exact worker return. The final equality
descent record remains present and valid. The compiled check runs the
literal source pair [([0,0],[0])] on the singleton parent forest.

The root review compares Haskell editAll and setChildren with these modeled
branches. Same-arity setChildren retains its raw guard. Negative indexes
are ignored by adjustAt. The comparison does not prove Haskell demand,
hash-consing, or memo publication. Read source-editor-comparison.md in the
evidence directory.

## Exact support and contract boundaries

Selected ForestClosed domains permit unrelated open ordinary roots and
siblings. A separate cap premise bounds every original captured root.
It can exclude an unrelated nonhereditary Mu body. General source support
must discharge or replace that stronger premise separately.

The Target receipt retains one-way inclusion for nonempty proper selected
paths. Merge can overapproximate its input. The whole Target language is
not proved equal to the intersection. Each checked native query retains
its exact intersection law. Leaf retains narrowing and preservation under
the existing explicit class-satisfaction contract. This checkpoint adds
no editor-wide path-mask theorem.

Initial MixedShared.Stored includes valid laws for every warm target slot.
Historical receipts refer to the immutable captured base and forest.
They are separate from the current checked inventory. The new execution
preserves both. It does not assume a newly successful Force as a premise.

Numeric bounds control constructor counters, domain counters, and causal
constructor payload mass. Full allocated equality and target-slot states
remain exact. Equality-table size and instruction counts, concrete bytes,
solver work, wall time, concurrency, Haskell lazy demand, and memo
publication remain separate obligations.

## Next caller: ClassPass

The class wrapper clears the class-local target table and captures the
current forest. Its existing actual-read verification supplies physical,
selected-domain, and class-satisfying language laws. Its finite producer
still requires ClassRanges. ClassPass still requires the corresponding
range law at the actual preceding class return.

Use the complete compiled editor to construct one class from its initial
Frame, selected domains, physical and semantic Merge laws, input caps,
and numeric reservation. Retain the returned Frame, profile, inventory,
Merge table, globals, caps, and arbitrary path-domain transport. Then
forecast the literal class fold. Each class captures its actual input
forest. A later class must not assume a future result, bound, or callback.

## Remaining library work

1. Construct the class wrapper and complete ClassPass from initial resources.
2. Complete active and stored outer descent, arbitrary constrained Mu,
   and the full source gate. Separate selected domains from all-root caps.
3. Prove repeated reduction convergence and remaining recursive callers.
4. Complete current typing, refinement, drawn-field, symbolic-measure,
   observable-error, validation-order, and generator-rank adapters.
5. Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling correctness.

The complete library goal stays active.

## Haskell repair handoff

No Haskell patch or new behavior defect is added. Root FINDINGS keeps the
external repair registry first. Repair b9219b9e is merged in source
c0cc8a05. Derivation validation rejects a field pool for the datatype itself.
The retained Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone `holds` still treats pool
descendants as opaque. Reuse the unchanged strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence. Record each
later repair in FINDINGS with its failure, executable reproducer, affected
paths, commit, checks, and upstream status.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2947 jobs and 65152 dependency checks.
All eight final production strict logs are empty. Every canonical target
passes. All 127 full signature and axiom pairs pass in 13 groups: 116 public
declarations and 11 constructed checks. Eight component manifests verify
234 entries. Only propext, Classical.choice, and Quot.sound occur. Read
checkpoint-validation.json in
lean/restart-evidence/20261017-initial-editor-resources/ for hashes and
successful logs.

Preservation retains 14484 starting files, 2936 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, two stashes, and three
other worktrees. All 89 frozen module manifests retain 702 entries.
Older proofs, counterexamples, repairs, and marked drafts retain their bytes.

A filename collision overwrote one new concrete fixture's original attempt
1 source and raw log. Attempts 2 through 8 remained intact. A reconstructed
attempt 1 source has explicit provenance. The original raw log is unavailable.
Foreign generic attempts 9 and 10 do not validate the concrete proof.
New concrete checks execute their immutable source snapshots directly.
The final concrete success is re-established independently. Read
edit-numeric-evidence-recovery.md for the exact affected files and final
validation metadata. This gap affects new failure diagnostics, not production
proofs, old checkpoints, or final independently checked source and results.
