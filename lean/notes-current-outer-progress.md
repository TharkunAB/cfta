# Current proof and the general outer progress boundary

Starting checkpoint: 76dcdddc. Proof commits: 2d63272f and a68b3c9b.
Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Whole-library target

For each public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Specify the intended behavior first. Then establish correspondence with the
current implementation. Support must depend on initial data and resources.
It must not assume a future successful worker or its returned result.
Errors and validation order are part of each public contract.

The target includes exact accepted terms, counts by size, enumeration order,
rank/unrank inverses, transformation language relations, generation, and
sampling laws. Terms, accepting runs, and generator members differ.
Exactness, inclusion, and representative restriction have separate contracts.
Theorem totals do not measure completion.

## Current proof map

The exact Sized model has term classes, counts, explicit row order,
enumeration, and inverse laws. Construction models retain nested Mu,
unions, physical stores, and causal payload bounds. Initial resources
construct supported readers, comparison, selection, Merge, recursive
intersection, Target, Force, Leaf, editors, class passes, local reduction,
parent edges, and edge memo calls. Their exact scope remains in the
earlier proof notes. The optimized interned core remains included.

Outer results cover ready hits, terminal node bodies and calls, inherited
prefixes and descents, reconstruction, and descendants that stop on
contradiction or have no children. Finite-ordinary mutual completion has
its separate shape and returned-height conditions. General nonempty live
walks, rows, ordinary nodes, and mutual completion remain open.

## New facts for the general progress proof

| Module | Checked result | Boundary |
| --- | --- | --- |
| GatePlainRegion | The actual visited gate derives hereditary plain annotations from Coherent and Available. Every reached ordinary guard has an empty physical own payload. Closed input derives the existing caller Region. | No whole-heap annotation or closure premise is added. This is not a decreasing call rank. |
| RequiredGuardOrigins | Actual ordinary Required returns copy full root guards, symbols, and arities from original rows. Accepted plain unfolding, Head, and Required retain empty own fields at their exact returned heaps. | These are actual-read preservation laws. They do not construct general outer recursion. Causal Mu body/probe observations remain explicit. |
| PrimaryEndpointCap | Initial endpoint reachability exclusion derives a finite Cap at the input's payload mass. Actual false primary endpoint traces supply that exclusion. | The bound belongs to the selected value. It is not a Cap on every forest root. Secondary endpoint refusal checks permit constrained Mu and do not imply this result. |
| OuterParentHeightGrowth | A source-built admitted parent executes the literal allocated worker and raises edge height from 2 to 3. A returned child has the original parent node's height, 3. | This refutes strict ordinary-height descent for that transition. It proves no cycle, divergence, or Haskell defect. |

The source gate visits stored Mu bodies and skips repeated physical
identities. Coherence connects those visits to complete available records.
Both Mu probes remain outside the annotation predicate. Plain means empty
effective equalities and supported positive guard syntax. It does not mean
that the stored residual syntax is absent.

The selected endpoint Cap is a derived fact. No input Cap, whole-forest
closure, or desired future result is its premise. Coherent cached depth
justifies the endpoint check's zero-depth shortcut. Ordinary and union
children use the actual complete payload-mass bound. Plain Mu uses the
actual gate-to-annotation theorem. A finite Cap does not establish a
decreasing rank for the whole outer call.

## Actual copying and the missing measure

The new parent witness starts with a constrained finite node B and a plain
productive recursive tree tau. B is pair(leaf,leaf) with class [0]=[1].
Tau accepts leaf and pair(tau,tau). The parent class is [0]=[1,0].
Its actual primary gate returns false. Required and native edits expose
tau and reuse B at a greater ordinary depth. The literal return retains
the original outer raw guard and both child slots.

The returned second child has a plain pair row. Its first child has B's
exact physical reference and B's constrained raw guard. The original
edge height is 2. The returned edge height is 3. The returned second child
has height 3, equal to the original parent node. Initial source construction,
allocation history, Ready, availability, and closure are derived in the
witness. No future graph or callback is a premise.
The nested copy conclusion is physical reference equality and raw guard
retention. Full nested-payload equality is not a separate conclusion.

The separate constructed outer execution completes on this same fixture.
It returns a node of height 4. At its actual returned caller, the B request
is ready with B and retains that exact caller. This checks post-return
memo reuse. The internal copied-B hit event is not separately isolated.
This is not a nontermination example.
The historical OuterCallerCycle input remains repaired by the endpoint gate.

The next theorem needs causal progress for actual returned children and
captured memo owners. Constraint occurrences and owner activations matter.
Physical raw guards remain present after their local work runs. Equal guard
payloads can occur at different original positions. A finite guard alphabet
does not identify those positions or order their work.

InheritedGrowthBoundary already proves that source combine and descent can
increase inherited path length and leave literal/Top/conjunction closure.
Its recurrence is not a reached infinite outer execution. It rules out
using that guard closure or maximum original local path length as the
whole inherited-state invariant. Unequal-length edits also move constrained
finite values deeper. A proposed occurrence and path measure still needs
preservation across actual native products, parent returns, and warm hits.
The present resource majorants supply no such decreasing measure.

The certificate must also respect actual memo keys. Keys retain inherited
canonical trie identity and the complete node or edge identity. They do
not retain historical occurrence labels. A provenance-dependent rank
must agree across same-key captured-owner reuse, or the proof must derive
key-disjointness by another method. Strict descent of ghost labels alone
does not exclude a busy physical cell.

After that producer, complete live child walks, ordered rows, ordinary
node bodies, and the full mutual pass. Derive busy exclusion while ancestor
owners remain active. Do not replace this work with a future returned-child
rank premise or a globally idle table assumption. Repeated-pass convergence
remains a separate obligation after one-pass completion.

## Validation and Haskell handoff

All four final source strict logs are empty. All four canonical targets
pass. Full Audit passes 3035 jobs and 66550 dependency checks under
4 GiB MemoryMax, 4 GiB MemoryHigh, zero swap, and 361 MiB peak memory.
Successful public and constructed probes permit only propext,
Classical.choice, and Quot.sound. Failed source and output attempts retain
their bytes. Read restart-evidence/20261017-outer-progress/README.md and
checkpoint-validation.json for exact final probe and manifest counts.

No Haskell change or new Haskell behavior defect is added. Field-pool
repair b9219b9e is merged and validated in unchanged source c0cc8a05.
The Chain example returns Left (FieldAtomOnDatatype "Next" 0). Standalone
holds retains opaque-pool evaluation. FINDINGS keeps the current repair
registry before historical failure reports. Every later repair must retain
its failure, executable reproducer, affected files, commit, checks, and
upstream status there.

Current frontend and error adapters, lazy forcing, memo publication,
concrete memo events, host capacity, public pipeline composition, and full
Haskell correspondence remain open. All earlier proofs, counterexamples,
repairs, marked drafts, stashes, and other worktrees remain preserved.
The whole-library goal remains active.
