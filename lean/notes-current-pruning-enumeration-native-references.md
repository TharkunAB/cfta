# Native suspended-reference history through captured finalization

## Current result

Mutation shape and storage proof reuse: `fa26b8e1b14aeb15a9c04bdc178200fb0b3db068`.
Native reference history: `3a765d71dee49787ab5f191a3a9eb59818c180c2`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The actual terminal, child, ordered traversal and selected-edge producers now
retain suspended-reference history on their existing returned witnesses.
The captured-edge producer also retains global pending references through
the original captured-slot final write. This last output requires initial
global pending references and initial incoming avoidance of the target.
These facts are conditional outputs. No admission premise or numeric Ranges
condition was added. No runtime worker body changed.

## Meaning of the reference conditions

`ReferencesAllowed allowed state` applies a fixed variable predicate to every
stored suspended reference. `InputsAllowed allowed bucket` applies it to a
supplied suspended bucket. The fixed predicate does not change when the
union-find forest changes.

`IncomingAvoid held state` says no stored suspended reference belongs to the
current class of held. `PendingReferences state` requires that condition for
every enumerated slot. It does not inspect fragment holes. These predicates
do not by themselves prove fragment acyclicity or successful extraction.

## Actual mutation and fold effects

`DispatchShape.singleton` identifies an actual successful dispatcher action
run at the same state from which it captured its payloads. The endpoint is
the unchanged state or the exact assimilation of two actually stored pending
payloads. The mutation retains source-first concatenation, source elimination
and the ancestry update. The theorem does not prove language or caller effects.

The storage and waiting-count theorem now uses this shared shape. Its complete
public contract is unchanged. Its old exhaustive dispatcher proof is retained
in the prior checkpoint. Missing slots, invalid values, unsupported actions,
native faults and Empty rejection do not supply a successful singleton.

`NativeReferences.assimilated_allowed` proves the fixed predicate from the
two actual stored-slot equations. Target replacement stores only their
concatenated references. Source elimination adds no reference. An ancestry
update changes no values.

`fold_allowed` proves the predicate at every actual returned outer fold
endpoint. It makes no successful-fold premise. The proof enters the suffix
only when the actual runtime match returns a successful singleton. Every
other head result retains the current pre-action outer state. This includes
faults, unsupported results and raw-empty rejection after a successful prefix.
This is a property of the returned outer state, not of arbitrary error rows.

`incoming_written` adds the supplied incoming bucket to the actual current
old payload. Its conclusion concerns the exact post-write values. It does
not require a successful final raw row. `prepared_allowed` covers actual
shallow child actions. Fresh allocation creates an empty pending payload.
Ordinary preparation then stores only the supplied suspended bucket.

## Terminal, child and traversal producers

`CachedTerminalAdapter.complete` now returns a universal fixed-reference
implication on its same resultCache. A fold rejection retains the reached
folded cache. A completed fold supplies its actual incoming read and write
packet. The value-preserving read frame exposes the current oldScs receipt.
The exact write equation proves the result even when incoming replacement
is Empty and the final raw list is empty.

The two Empty cases have different mutation order. Assimilation rejects
before both raw writes. Incoming restriction performs its pending write and
ancestry update before rejection. Cache preservation must cover both cases.
Membership in a returned raw list cannot justify the post-write empty case.

`incoming_preserved` converts fixed reference preservation to incoming
avoidance through the actual protected-class equivalence. `pending_preserved`
uses actual enumerated origin and protection of each original enumerated
class. It does not require final Safe.

`ChildCompletion.complete` returns fixed-reference preservation and a global
pending-reference preservation implication. It retains the Empty input case,
fresh shallow case and terminal case. `TraversalCompletion.complete` composes
these facts through actual intermediate caches and retains them at the first
valid child rejection. Each original input bucket supplies its fixed allowed
predicate. Successful head output supplies safety for the recursive tail.
Rejected output does not gain an unconditional Safe assertion.

## Own classes and the captured raw-slot write

`SelectedEdge.complete` preserves incoming avoidance of an old allocated
root avoided by the inherited bucket. Suspension creates fresh slots with
empty stored payloads. Existing own-class preparation proves avoidance for
every actual child bucket. The traversal's fixed-reference output and class
protection then prove incoming avoidance at the reached cache.
Enumerated origin gives preservation of global pending references.
Residual recording changes obligations only and retains these properties.
Both complete and valid rejected outcomes retain the new history outputs.

`CapturedEdge.complete` uses the selected-edge outputs at its same middle
cache. Initial `PendingReferences` supplies the old enumerated classes.
Initial `IncomingAvoid uv` supplies the newly enumerated captured target.
The existing `setValue_pending` theorem proves the final raw-slot write.
Expansion-ancestry reset changes neither values nor classes. Child rejection
does not perform that write and uses selected-edge history directly.

Ready.avoids only covers the target's own stored bucket. It is not silently
used as IncomingAvoid. The extra initial fact stays explicit in the output
implication. All old producer premises, numeric admission and witnesses stay.

## Verification

All nine changed modules pass Lean 4.34.1 with all linters and warnings as
errors. Fourteen actual strict compiler attempts are retained. Four fail:
the extracted shape initially uses lookup equalities already reduced by
dependent cases; shallow preparation initially leaves its written payload
implicit; terminal integration initially rewrites a self-referential record
equation and has one multiline application error; the next terminal attempt
needs the projected values equation before type refinement. Final proofs
make these terms explicit. No production resource limit or linter changed.
The passing reference check before adding the conversion lemmas is retained
separately from the final passing check with those new lemmas.

A source-preparation assertion fails before writing either target file.
A prematurely issued driver then stops at the missing source copy and never
invokes Lean. These are preparation events, separate from compiler attempts.
The corrected generator, event record and cap receipt remain in the evidence.
Two failed patch-context checks also make no source change.

Installed builds and all fifteen public declarations pass. The complete
public output has 1184 lines and 116998 bytes. Its SHA-256 is
`023a98ae97f06e33166b4fc1e077704661315179ab3d9dcd4ba6d8f9764ce46d`.
All axiom sets are subsets of `propext`, `Classical.choice` and `Quot.sound`.
The aggregate Audit passes with 3749 jobs and 76709 theorem dependencies.
The older unused inputs warning remains unchanged. Checks run serially under
4 GiB heavy-management caps with no swap. No Haskell runtime tests repeat.
All actual attempted compiler inputs, complete raw logs, reports, final
sources and cap records remain in `restart-evidence/20261025-native-references`.

## Remaining work and strongest claim

Carry the captured-edge history implication into each processed native
alternative receipt. The branch completion theorem currently consumes the
new field as unused proof data. Its old result contract stays unchanged.
Each receipt has its own enumeration cache; no merged final cache exists.
Use entry's RenderStable to transport the initial global and incoming facts.
Derive initial IncomingAvoid from current unblocked scheduler selection,
using actual native flags, canonical waiting counts and root paths.
Narrowing and oracle calls must preserve the facts at their actual positions.

Then prove fragment-hole and dependency history, successful receipt semantics,
extraction and whole-driver language preservation. Parent normalization and
terminal-parent integration remain open. Initial-only numeric admission,
arbitrary Haskell demand, full raw-stream erasure, concrete solver and runtime
representation correspondence remain open. No practical resource or
convergence bound follows from these proofs.

H6 remains the strongest end-to-end language result. Covered closed
construction, valid initial cache and allocation history, prescribed finite
budgets and modeled node-call rounds derive sufficient finite bounds and a
mathematical width chosen after construction. With empty inherited payload,
the final available value has exactly the original finite-tree language under
the formal formula and entailment interfaces. Whole typing and pruning remain
outside this claim. H6, Haskell runtime and the optimized interned core are
unchanged. No new Haskell repair is identified. Root FINDINGS retains the
external Haskell fix handoff first.
