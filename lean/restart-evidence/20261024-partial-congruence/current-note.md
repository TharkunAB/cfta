# Partial observations under path compression

Updated: 2026-10-24. Start: `51505458d39a58890f837393a338855a5523de57`.
Partial-render proof: `68a06da88d5793fe12c49dc7770b498d3c744dfe`.
Root composition: `29776e8b6fcff0fecc34061775933646da576a70`.

## Checked result

Successful partial observations now agree across the complete compression frame.
The frame preserves the allocation counter, stored values, obligations, both
ancestry fields, and every root path with its exact representative ID and size.
The forests can have different parent paths. The caller supplies totality of
the left forest. The frame derives totality of the right forest.

`EnumerationPartialCongruence.lean` compares two actual successful expandPartial
executions on the same graph and fragment. Their bounds can differ. The terms
are equal, and their actual final states retain the complete frame. The proof
retains symbols, child order, original hole IDs and recursive truncation only
when the suspended-constraint list is empty.

`EnumerationPartialTransport.lean` constructs a finite matching right render
from one actual successful left render. A successful right render is not a
premise. The proof constructs the actual intermediate states in source order.
It combines finite read and child bounds by addition. Successful fuel extension
retains those exact intermediate and final states.

`EnumerationRootObservation.lean` covers the existing rootFragment action.
It proves success inversion, frame preservation, paired agreement, finite
transport and exact-state fuel extension. The action reads variable zero at
its existing bound plus one. It returns the stored enumerated fragment or the
original root hole. Transport retains that read-bound convention.

`EnumerationPartialRoot.lean` composes the literal existing rootFragment and
expandPartial actions. Each execution uses one common bound for both actions.
It proves the complete frame, paired output equality, successful fuel extension
and finite transport of the complete sequence. The constructed right bound
is the sum of its root-read and render bounds. Both actual actions retain the
same intermediate state when raised to this common bound.

This is the post-driver sequence used by the modeled partialRunsUntil path.
The Haskell rootTermFrag and expandPartialTermFrag have the same branches.
The source uses their sequence in eager, partial and ordered rendering.
The new modules add no alternative renderer or observation language.

## Premises and remaining work

No Safe, Finished, accepted completion, desired-output certificate or additional
readable-slot premise is required. The supplied successful observation gives
the actual readable slots and finite unfolding. Totality alone does not ensure
rendering terminates. An enumerated slot can refer to itself indefinitely.

The result does not equate raw forests, same-bound errors, native missing-slot
exceptions, or complete enumeration result streams. It does not prove the
preceding driver equivalent. Native container and node representation, integer
bounds, branch order and multiplicity of the complete driver remain separate.
The recursive graph view still needs its actual Mu and InternedUnion realization.

The next source target is Specftacular.Pruning.resume, followed by templateOracle.
Its callbacks use representative reads, partial rendering and unexpanded-node
reads. These operations can compress the forest. The old exact-state
ReadOnlyOracle premise does not cover these callbacks in general. Prove their
actual output agreement and complete-frame behavior. Keep typing and pruning
soundness separate from observational agreement. Full canonical mutation
histories and the cached-driver bridge also remain open.

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
combined finite-execution and exact finite-tree language theorem under its
existing covered-construction, valid-history and formal-guard premises.
Full-pipeline composition, resources, practical machine width, Haskell and
solver correspondence, phase-4 correctness and convergence remain open.
H23 counter composition remains queued. The full goal is active and incomplete.

## Validation and preservation

Pinned Lean 4.34.1 checked all four final sources with warnings as errors and
all linters. The installed combined build and Audit passed: 3671 jobs and
75775 theorem dependency checks. Audit replayed one older unused-variable
warning in InternedFreshOrdinaryClosedCompletion. No new-source warning occurs.
All 11 public signatures and 11 axiom reports were read. Each theorem report
lists only propext and Quot.sound. No new axiom or proof-limit override is added.

The first paired-render check lacked the local List monad-law instance. The
existing proof of those laws repaired it. The first transport check referred
to two state names removed by equality elimination. It also had ambiguous
constructor notation. The next two attempts fixed those elaboration errors
without changing a theorem statement or bound calculation. All three failed
attempts, original drafts, repairs and successful checks remain in the evidence.

The fresh pull passed. Imported main remains a5fbb66eec and is already an
ancestor. No Haskell source changes or new Haskell repair is claimed. The
external repair index stays first in FINDINGS. Both LPO defects remain open.
Checks of unchanged Haskell source were not repeated.

All earlier proof bodies, drafts, counterexamples and sealed evidence remain.
Audit adds only one import. New restart status blocks retain prior document
contents exactly. Evidence is in restart-evidence/20261024-partial-congruence.
It includes the baseline, source reviews, all eleven Lean attempts, public
readback, callback source inventory and preceding publication receipts.
This record precedes the evidence commit and its authorized push to formalize.
