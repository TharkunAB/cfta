# Enumeration observations and path compression

Updated: 2026-10-24. Start: `ae8970309774ea10a833b64de7945f48d50ff11e`.
Primitive proof: `550ac2718f04690450dd31e553d93c775f4a11cb`.
Partial-render proof: `45585fde7b5e420db64de2c6beed54fb5a128766`.

## Main refresh

The fresh pull, main fetch and direct remote checks found main unchanged at
`a5fbb66eec52b8c28a4beacd982f00626c9e279a`. This commit is already an
ancestor of formalize. There is no new upstream commit to merge at this check.
The prior evaluation includes partial enumeration, phase-4 program typing,
refinement memoization within each exclusion, optional term orders and the
negative-depth repair. Read `notes-current-upstream-program-enumeration.md`
and `notes-current-upstream-type-depth.md` for that evaluation.

No Haskell source changes in this checkpoint. The external repair index stays
first in root FINDINGS. The two optional LPO defects remain open. This work
does not claim a new Haskell repair or repeat checks of unchanged Haskell.

## Checked observer claims

`EnumerationObservations.lean` extends the existing complete compression frame
with symmetry. The frame preserves the allocation counter, all stored values,
all obligations, both ancestry fields, and every finite root path with its
representative ID and stored size. It permits different parent paths.

Two successful representative reads from framed inputs return the same root.
Two successful value reads return the same complete value. Both results retain
the full frame between the actual final states. They use independent bounds.
The caller supplies totality of the left forest. The frame derives totality
of the right forest.

Both primitive reads also have finite transport theorems. One actual successful
left read constructs an actual right read with the same result and a full
final frame. The right read is not a premise. For values, the observed left
read supplies the required stored slot. Total forests alone do not imply that
the slot exists.

`EnumerationNodeObservation.lean` models the actual public getUnexpandedNode
projection. It reads the representative's value. An unenumerated value returns
its stored optional node. Other values return none. A present empty node stays
present. The model does not expand the node or inspect its accepted language.
It proves exact success inversion, paired agreement, finite transport, and
retention of the exact final state at a larger bound.

`EnumerationPartialObservation.lean` proves two claims about the existing
expandPartial action. A successful partial render from a total forest preserves
the complete frame. More fuel retains its exact successful partial term and
exact final state from the same initial state. The proofs retain child order,
original hole IDs and the empty-constraint recursive truncation branch.

## Boundaries and next target

These theorems do not assert equal fuel across different forests. A compressed
path can need less lookup fuel. They do not equate errors or native missing-slot
exceptions. The Haskell observer stores Node values; the existing model stores
node IDs. A complete native representation theorem remains separate.

The partial-render results do not yet compare outputs from two framed inputs
or construct a matching render in the other input. That is the next proof
target. A total forest alone does not ensure partial rendering terminates:
an enumerated slot can contain a fragment that refers to itself.

An arbitrary read-only callback can inspect raw parent paths and return a
different result. Its unchanged state alone does not establish output
congruence. The complete cached-driver bridge still needs the actual observer
results, callback congruence, and the complete canonical mutation history.

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
combined execution and exact finite-tree language theorem under its existing
construction, allocation, cache-history, finite-call and guard premises.
Full-pipeline composition, resource bounds, practical machine width, source
and solver correspondence, phase-4 correctness and convergence remain open.
The H23 counter-composition proposal remains queued. The full goal is active.

## Validation and preservation

Pinned Lean 4.34.1 checked all three new modules with warnings as errors and
all linters. The installed combined build passed. Audit passed: 3667 jobs and
75754 theorem dependency checks. It replayed one older unused-variable warning
from InternedFreshOrdinaryClosedCompletion. The new sources have no warning.

All 12 compiled public signatures and 11 axiom reports were read. Frame.symm
uses no axiom. The other ten public theorem reports list propext and Quot.sound.
There is no new axiom, sorry, native decision shortcut or proof-limit override.

The retained first partial-render attempt failed because of Lean layout after
using. A one-line layout repair passed. The first combined Audit then found
that two new unnamed local instances had the same generated name. Distinct
explicit names fixed that import collision. The theorem statements and proof
bodies did not change. The successful combined Audit and public readback use
the final installed sources. Both failed attempts remain in the evidence.

All earlier proof bodies and sealed evidence remain. Audit adds only two imports.
The restart documents retain their prior contents after the new status block.
Evidence is in `restart-evidence/20261024-observer-compression`. It includes the
baseline, source proposals, reviews, checks, failures, final public readback,
preservation verifier and the preceding checkpoint's publication receipts.
This record precedes the evidence commit and its authorized push to formalize.
