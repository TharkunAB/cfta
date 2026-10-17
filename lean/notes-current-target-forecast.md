# Current proof target and remaining library work

The complete public Haskell theorem remains open. This checkpoint starts
at published f7494679. Proof commit is a52aeb5f. Source main is c0cc8a05,
merged at 896b0a1c.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of contracts. There is no completed universal library
theorem. First specify the intended behavior. Then prove that the current
Haskell implementation has that behavior. Support conditions must concern
the initial input and resources. They must not assume a later successful
call or the required result. Documented errors and validation order are
observable results.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts.

## Established components

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes, counts, original explicit row order, size-major enumeration, and rank/unrank inverses. | Current adapters and full public composition. |
| Interned construction | Repaired modeled construction, including nested Mu and unions, with physical stores and causal payload bounds. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive reads | Initial resources construct closed recursive collection and row exposure with exact heaps, row widths, and stable replay. | Remaining callers and public correspondence. |
| Comparison and selection | Initial counters and causal mass construct repaired worker success with exact histories, returned heaps, and stable replay. | Remaining caller composition and independent language-law hypotheses. |
| General memo-aware Merge | Initial resources compute sufficient work and selection fuel. Full allocated replay retains the exact equality state, returned heap, memo, and winner. | Complete callers and Haskell runtime correspondence. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at an initial computable fuel ceiling. | General constrained callers and public correspondence. |
| Native query programs | Initial forecasts construct supported finite indexed query sequences with exact language, stores, origins, globals, and resources. | Interleaved caller construction, adaptive control flow, and concrete capacity. |
| Selected Operand | Initial forest, signed path, counters, and causal mass construct projection then Merge, with full receipts and returned query Frame. | Composition with recursive Target and concrete capacity. |
| Target prerequisites | A pure profile and fuel schedule follows head Operand, recursive tail, then query order. Actual component receipts compose into full Target receipts. | A theorem that constructs the complete nonempty Target from that initial schedule. |
| Mixed editor and class pass | Actual reads and source class order preserve stores and finite syntax depth. | General first Target and Force misses and complete execution. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and store laws. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver proofs remain preserved. A passing build
does not give a completion percentage. The Lean definitions are handwritten.
Their proofs do not yet establish full correspondence with compiled Haskell.

## This checkpoint

`SourceCurrentAllocatedMergeNumericReplay` proves fuel-by-fuel observation
erasure for both instructions and recursive calls. A successful erased call
executes the allocated worker at the same fuels. Stable actual graphs
identify the complete returned equality state and memo. Its complete
endpoint constructs its own actual allocated call from initial readiness,
availability, stored memo laws, and scalar resources. It retains physical
effects, closedness, causal heap bounds, output mass, and larger-fuel replay.
The scalar bounds the constructor heap. It does not count equality-state
instructions or establish a concrete machine capacity bound.

`SourceCurrentConstrainedCapTargetForecast` defines pure Operand, Fold,
and Target profiles. It follows the actual head Operand, recursive tail,
then checked query order. Initial reservations name the profile at each
query entry. The shared computed ceiling covers projection, recursive
reads, Merge, selection, and native-query fuels. Inflation, decomposition,
reservation, and fuel-lowering laws are proved. This module defines and
proves properties of the schedule. It does not construct a full Target
execution or prove that reached states fit every scheduled profile.

`SourceCurrentConstrainedCapTargetReceiptComposition` exposes receipt
composition without future range assumptions. Singleton, cons, and empty
helpers retain exact states, inventories, physical effects, global memos,
Merge tables, original values, and language inclusion. Actual retained
FoldReads and TargetReads determine full final receipts. These helpers
consume actual component receipts. They do not establish their existence
for every initial reserved Target.

Constructed checks include initial singleton and empty Target executions.
The two-component receipt check consumes actual component receipts. It
checks source order and receipt composition. It is not an initial-only
construction of a general multi-path Target.

## Immediate missing theorem

Construct the actual complete Target and its worker return from the initial
Frame, available captured forest, selected path support, memo laws, causal
resources, cap bounds, and pure initial reservations.

First convert the initial query Profile to the Operand scalar bound. Run
the actual projection and full allocated Merge. Derive the next Profile
from their returned bounds and preserved domain counter. Carry the exact
Frame, inventory, Merge table, global memos, and caps into the recursive
tail. Run the checked intersection at the tail return. Use its actual
receipt to derive the final Profile and Frame. Compose the full receipt
with the new helpers. Lift all five literal worker fuels to the computed
shared ceiling.

The theorem must construct its own actual graph and retained reads. It
must not accept FoldRanges, TargetRanges, a future completed callback,
a future heap bound, or a successful worker fuel as an input. Preserve
selected paths that permit unrelated open ordinary roots and siblings.

## Remaining library work

1. Complete general Target and Force from initial resource schedules.
2. Complete mixed Edit and ClassPass, active and stored outer descent,
   arbitrary constrained Mu bodies, and the complete source gate. Separate
   broader source support from stronger all-root cap assumptions.
3. Prove repeated reduction convergence and remaining recursive callers.
   One complete pass does not prove convergence.
4. Complete current typing, refinement, and drawn-field adapters, symbolic
   measures, observable errors, validation order, and generator rank order.
5. Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
6. Compose the complete public construction, transformation, graph
   conversion, exact query, generation, and sampling pipelines.

The complete library goal stays active.

## Haskell repair handoff

Root FINDINGS keeps the current repair registry before historical failures.
Repair b9219b9e is merged in source c0cc8a05. Current derivation validation
rejects a field pool for the datatype itself. The retained Chain reproducer
returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone `holds` still treats
supplied pool descendants as opaque. The repair prevents the invalid
derivation configuration; it does not change that evaluator.

No Haskell patch or new behavior defect is added in this checkpoint.
The unchanged source retains strict Nix all-component validation,
798 examples plus golden, Fourmolu, and Cabal-gild evidence. Record every
later repair in FINDINGS with the failure, executable reproducer, affected
paths, commit, checks, and upstream status.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2934 jobs and 64980 dependency checks.
All three final production strict logs are empty. All 64 complete signature
and axiom pairs pass in six groups: 55 public declarations and nine
constructed checks. Only propext, Classical.choice, and Quot.sound occur.
Read checkpoint-validation.json in the evidence directory for source hashes,
successful logs, and component manifests.

Preservation retains 14247 starting files, 2928 older non-Audit proof
sources, all 239 Haskell files, all 206 active-package files, two stashes,
and three other worktrees. All 86 frozen module manifests retain 689
entries. Older proofs, counterexamples, repairs, and marked drafts retain
their bytes. Strict attempt sources and raw logs remain in the evidence.
