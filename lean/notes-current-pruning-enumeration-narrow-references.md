# Native narrowing and pending-reference history

## Current result

Compression and replacement: `0ab9d22a9`.
Native producer integration: `111c8d8fb`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The actual native narrowing producer now retains incoming-reference and
global pending-reference history. It returns these as conditional outputs
on its existing entry and changed-handle final-state witnesses.
No producer input, numeric admission or runtime worker body changes.

## Compression and replacement

EnumerationPendingReplacement has four theorems and no new definitions.
frame_incoming uses the actual compression frame's values and root paths.
frame_pending also transports each old enumerated-slot equation.
Neither theorem requires Safe. The producer previously required only a total
forest, so a new safety premise would needlessly weaken its public contract.

setValue_incoming uses the actual stored pending-slot equation and the actual
write. The replacement keeps exactly the old suspended bucket. Every fixed
allowed reference in that bucket therefore comes from the old store.
The write changes no representative class. The theorem works for every held
variable. It does not need a separately supplied bucket-avoidance premise.

setValue_pending first proves that the pending replacement creates no new
enumerated slot. Each enumerated slot after the write already existed before
it. The incoming-reference theorem then supplies its required avoidance.
No bound, root or Safe premise is needed for these reference properties.
These facts do not assert cache-index correctness or language preservation.

## Actual narrowing witnesses

SourcePruningEnumerationAction.prepare_pending_complete retains its original
native outer-narrowing computation, sufficient fuel, Keeps, decoded values,
availability, closedness, complete action and actual enumeration states.
It now returns initial-to-entry pending and incoming implications, using the
actual first read frame and existing entry frame.

An Empty result still returns reject and has no successful final state.
An equal handle still returns the original value and pure action at entry.
Its history follows from the new entry outputs.

A changed nonempty handle still returns the same actual representative read,
root path, old pending-slot receipt, bound, replacement action and final state.
The new outputs transport history through its actual whole compression frame
and then the exact same-bucket write. They concern that same returned final
state at the same reached native heap. There is no replacement witness,
fresh successful-action premise or identity-narrowing assumption.

## Concrete callback and next integration step

SourcePruningRecordTypes.recordTypes_frame already proves a full compression
frame for each actual successful concrete typing callback. The generic frame
theorems now transport incoming and pending history through that receipt.
Its pre-expansion recordTypes_inr case is already a pure metadata result.
The fragment case can compress representative paths. No exact-state
ReadOnlyOracle assumption is required for these reference facts.

The next step is the native cache adapter for the actual narrowed replacement.
It must retain roots, Safe, exact canonical waiting counts, current native
expandable flags, pending realization and the captured target at the reached
cache. Narrowing can change the candidate flag. Keeping the old flag without
checking the new decoded node is insufficient. The suspended bucket stays
the same, so exact waiting counts should stay the same.

Then compose the actual selection, reads, narrowing action, concrete callback
and ordinary entry. The current selected ordinary theorem still starts from
the exact cache used by pure selection. It has no intervening operation.
This checkpoint does not silently apply it after a narrowed write.
Arbitrary user callbacks and ordered activation refreshes need their own
actual preservation receipts. The full driver composition remains open.

## Verification

Both changed modules pass Lean 4.34.1 with all linters and warnings as errors
on their first strict attempts. The installed helper build passes.
The aggregate Audit passes with 3750 jobs and 76716 theorem dependencies.
The older unused inputs warning remains unchanged.

Installed public readback checks six declarations. Its full output has
185 lines and 16750 bytes. Its SHA-256 is
`f817e0c178560d8fe24b763d6dd0d26cf8d5328d25b5b4873b607d3893cd2d2b`.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
All five checks run serially under 4 GiB heavy-management caps with no swap.
No compiler attempt fails. Complete inputs, raw logs, cap records, final
sources and the proof patch remain in restart-evidence/20261025-narrow-reference-history.
Haskell, H6, selected ordinary workers and all older narrowing producers stay
unchanged. No Haskell suite repeats. No Haskell repair is needed for this proof.

## Strongest claim and remaining work

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache and original allocation history, and
prescribed finite budgets and modeled node-call rounds derive sufficient
finite bounds and a mathematical width chosen after construction.
With empty inherited payload, the final available value has exactly the
original finite-tree language under the formal formula and entailment
interfaces. The theorem does not cover the whole typing or pruning driver.

The new pruning results preserve stored suspended-reference history through
covered selected ordinary alternatives and actual native narrowing effects.
The generic compression facts also apply to the concrete callback's existing
receipt. Complete native indexed driver composition, fragment-hole history,
fragment acyclicity, successful extraction and whole-driver language semantics
remain open. Terminal parents, parent normalization, initial-only numeric
admission, arbitrary Haskell demand, full raw-stream erasure, concrete solvers
and physical runtime correspondence remain open. No practical resource or
convergence bound follows.
