# Current library proof status and complete initial Target execution

This checkpoint starts at published c0cccd79. Proof commit is adf8c036.
Source main remains c0cc8a05, merged at 896b0a1c. The complete public
Haskell theorem remains open.

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
| Interleaved Target | Initial profiles and reservations construct the actual head Operand, recursive tail, and query sequence. The same return has a complete receipt, Frame, inventory, memos, cap, resource Profile, and common-fuel worker equation. | All-root cap and selected-domain assumptions remain explicit. General Force and runtime correspondence remain open. |
| Mixed editor and class pass | Actual reads and source class order preserve stores and finite syntax depth. | Initial Force, Edit, and ClassPass execution and forecasts. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver proofs remain preserved. The Lean
definitions are handwritten. These component proofs do not yet establish
complete correspondence with compiled Haskell.

## Complete initial Target producer

`SourceCurrentConstrainedCapTargetOperand.complete` converts the initial
query Profile to a scalar constructor-heap bound. It constructs selected
projection followed by the full allocated Merge at the actual returned
state. The full Merge worker executes at the same computed fuels as its
constructor-heap erasure. The returned equality state and completed first
winner remain exact. The endpoint returns the same full query Frame and
the next numeric Profile. Projection and Merge preserve the domain counter.
One computed ceiling covers all four Operand worker fuel arguments.
The endpoint does not need an original-root cap premise. Its separate
`mixed_complete` endpoint also derives the output cap and semantic Merge
store from the original-root cap and semantic memo laws.

`SourceCurrentConstrainedCapTargetNumeric.fold_complete` constructs the
literal Fold by induction on its original path list. A base Fold executes
only its original seed Operand. A cons Fold executes its head Operand
first, its recursive tail second, and the checked intersection last.
Each stage derives its Frame, resource Profile, global memos, physical
Merge store, and cap at the exact returned state. The final query computes
its own next inventory and retains the recursive tail's Merge memo.

Initial `Reserved` tests contain only finite numeric Room conditions over
profiles computed from the original input. The proof uses each test at
its scheduled query entry. It derives the actual state bound from the
preceding stage. It does not assume a future returned heap or callback
law. `foldFuel` covers each literal stage with one maximum. Existing
worker stability lifts the head, tail, and query to that shared ceiling.
This ceiling bounds each worker fuel argument. It is not a bound on the
sum of all Target instructions.

`SourceCurrentConstrainedCapTargetNumeric.complete` handles empty and
nonempty Targets. The empty Target returns Empty at the identical checked
state and Merge table, with zero fuel. A nonempty Target constructs its
own actual Fold and retained TargetReads. The same endpoint returns the
full existing Target receipt, final inventory, complete Frame, forecast
Profile, semantic Merge store, exact cap, and full five-fuel worker result.
Existing Target worker stability gives exact replay at larger fuels.

The constructed integrations include an initial two-path Target and an
initial three-path Target followed by a second two-path Target at its
actual returned state. They derive a sufficient finite word width from
one composed initial forecast. They retain an open unselected sibling,
valid populated equality operations, full receipts, Frames, resource
bounds, cap laws, and exact common-fuel worker equations. The second
Target uses the actual returned Merge and global memos. These checks do
not claim that repeated Target execution leaves its full state unchanged.

No completed Target, FoldRanges, TargetRanges, successful future fuel,
intermediate heap bound, or per-callback resource premise is an input.
The actual graph and every reached receipt are outputs of the construction.

## Exact support and contract boundaries

Selected `ForestClosed` path domains remain explicit. They permit open
unselected ordinary roots and siblings. The separate cap premise bounds
every original captured root. It does not admit every unrelated
nonhereditary Mu body. General source support must discharge or replace
that stronger cap premise separately.

The full Target receipt retains the existing one-way inclusion law for
nonempty proper selected paths. Merge can overapproximate its input.
Do not describe the whole Target language as the exact intersection.
Each checked native query retains its own exact intersection law.

Numeric bounds control constructor counters, domain counters, and causal
constructor payload mass. Full allocated equality state remains exact.
The proof does not count equality-table instructions or establish their
size, concrete machine bytes, solver work, wall time, or concurrency.
The serial graph does not prove Haskell lazy demand or memo publication.

## Next caller: Force and Leaf

`SourceCurrentAllocatedSharedTargetForce.complete` still requires
`ForceRanges`. Its miss branch calls the earlier class Target endpoint.
Replace that dependency with the new initial Target reservation for
`operandPaths record.paths path`. Derive selected domains with
`SourceCurrentTargetPathComplete.operand_domains`. Derive selected language
inclusion with `SourceCurrentAllocatedClassTarget.receipt_included`.
Use the same actual graph, reads, and receipt when storing the new slot.

Keep the complete shared state. Preserve its historical slot receipts,
current Merge memo, global memos, and computed inventory. A hit retains
the identical state and needs no Target work. A miss must return the new
Frame, Profile, and semantic Merge laws for the next caller. Warm slot
caps need explicit initial validity or a derivation from their historical
construction. A new successful future Force cannot be an input.

Then compose `SharedTargetLeaf` in actual Force-then-query order. Its
query must use the produced target and actual Force return. Derive the
query reservation from one initial schedule. The current shared Ready
record does not itself contain every joint Frame and cap invariant.
Carry and preserve those additional laws explicitly.

## Remaining library work

1. Construct complete Force, Leaf, mixed Edit, and ClassPass from initial
   resources and valid warm slot laws.
2. Complete active and stored outer descent, arbitrary constrained Mu
   bodies, and the full source gate. Separate selected domains from
   stronger all-root cap assumptions.
3. Prove repeated reduction convergence and remaining recursive callers.
   One complete modeled pass does not prove convergence.
4. Complete current typing, refinement, drawn-field, symbolic-measure,
   observable-error, validation-order, and generator-rank adapters.
5. Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
6. Compose the complete public construction, transformation, graph
   conversion, exact query, generation, and sampling pipelines.

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

The pinned Lean 4.34.1 Audit passes 2936 jobs and 64988 dependency checks.
Both final production strict logs are empty. All eight complete signature
and axiom pairs pass in four groups: four public declarations and four
constructed checks. Only propext, Classical.choice, and Quot.sound occur. Read
checkpoint-validation.json in the evidence directory for exact counts,
hashes, and manifests. Four component manifests verify 92 entries.

Preservation retains 14320 starting files, 2931 older non-Audit proof
sources, all 239 Haskell files, all 206 active-package files, two stashes,
and three other worktrees. All 87 frozen module manifests retain 691
entries. Older proofs, counterexamples, repairs, and marked drafts retain
their bytes. Failed strict sources and raw logs remain in the evidence.
