# Physical checked execution and actual branch meaning

Source main is `8f85ddb6`, merged at `7dccd588`.
The source comparison is in notes-main-8f85ddb6.md.
Proof commits are `3ca57b91` and `7d9d433b`.
The full-library goal remains active.

## Physical cache and execution

SourceCurrentAllocatedNativePhysicalCache.Valid contains kernel validity,
complete original requests, exact checked keys, fresh handles, and returned
value availability or edge residency. Lifecycle proofs require no NodeProduced,
EdgeProduced, or result-language law. Actual warm lookup and demand recover
the exact requested operands and result residency.

SourceCurrentAllocatedNativePhysicalExecution preserves that invariant,
machine Extension, and heap Keeps through every actual checked outcome.
The reached Inputs checks refer only to current operands, current key bounds,
and the evaluating handle and resident result at finish. A node with no packed
key bypasses the range check. Code operands and conditional Words derive the
current checks. The reached checks are still an explicit finite plan.

SourceCurrentAllocatedNativePhysicalCompletion adds operation validity and
loaded-field closure without semantic completion receipts. Actual node and
edge request steps yield from independent requiredFuel bounds and ActiveAbove.
Loaded fields derive the actual checked edge prefix and its child code with
Safe, Operands, and Below. Pure cache misses derive actual finite completion,
current checks, and available output. General recursive body completion is open.

## Local and actual branch laws

SourceCurrentAllocatedNativeNodeBranches derives local laws for empty,
repeated-reference, self, swap, reset, and both union directions. Closed self
reuse reads the original input copy laws and actual coherent identity.
Union laws use exactly the original ordered members and actual makeUnion.
InputMeaning and RankedInput remain fixed across output heap effects.

SourceCurrentAllocatedNativeEdgeMeaning handles all three checked edge bodies.
Arity mismatch and checked rejection derive empty-child sentinel laws and
actual completion without child demand. Accepted bodies use an indexed Walk
of actual ordered zipped child calls with only their local NodeLaw, Keeps,
and Available facts. The final makeEdge derives the parent EdgeLaw.
Matching symbols come from the actual parent hash join. Edge bodies do not
independently test symbol equality.

SourceCurrentAllocatedNativeUnionMeaning executes both selected source union
branches from the ordered child Walk and actual final constructor. It derives
the parent NodeLaw, exact returned state, Keeps, and Available.
SourceCurrentAllocatedNativeNodeRowsMeaning does the same for the actual
ordered hash-join row walk and makeNode. It derives child EdgeInputs from
original node inputs and proves that every common row pair occurs in the join.

The accepted edge body uses child-step sum plus three execution units.
Union and ordinary-node bodies use child-step sum plus two. These are bounds
for those bodies. They do not include outer request publication or finish.
The returned states preserve actual operation caches, native tables, and domain
caches. Constructor effects change only the actual heap. These branch theorems
do not return CostHeap or assert full contextual cache validity.

## Remaining induction

Derive protected-frame actual traces and their physical Inputs through bind.
Use strong independent request descent to derive both node and edge bodies.
Restore enclosing active bounds at the actual finish instructions. Derive the
local child semantic laws from that same recursive execution and compose Mu,
reference, union, and row branches. Warm contextual-cache admission, runtime
word ranges, and complete original allocation histories remain obligations.

The existing query theorem remains conditional: FinishThrough includes the
root finish law. This checkpoint does not independently prove root semantics.
After the paired induction, compose the new current class Scan and the actual
constrained outer caller. Keep all other public API and separate Sized targets.
Do not use old eager execution or historical Scan as current source execution.

## Validation and preservation

The full pinned audit passes 2272 build jobs and 55698 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. The old unused-input warning
is unchanged. Focused checks cover 81 public axiom reports, 47 signatures,
53 examples, and one additional named kernel theorem. Independent read-only
reviews found no material defect and retain the local-child/recursive boundary.

The strict Nix all-component build and six Haskell suites pass: 777 examples
plus the golden check. Five Haskell files pass Fourmolu. Four packages pass
Cabal-gild. Root FINDINGS.md records each current Haskell fix for external work.

New root evidence is in restart-evidence/20261016-physical/. Agent evidence
is in restart-evidence/20261016-recursive/ under physical-cache, physical-execution,
physical-completion, edge-meaning, and node-rows-meaning file names.
Frozen source copies and hashes are saved. The starting tracked baseline has
3052 files; preservation validation records every intentional change.

An earlier environment reset removed temporary snapshots and nineteen external
draft files. Their bytes remain unavailable. This checkpoint does not recover
or reverify those bytes. It retains the repository proofs and recorded limit.
New evidence and draft snapshots stay inside the repository.
