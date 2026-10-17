# Selected child phases and retained native writers

Proof checkpoint: `5f88f078`. Starting checkpoint: `26b30c7e`.
Source main remains `c0cc8a05`.
The full-library goal remains active. Read
[the proof status](notes-proof-status-20261017.md) for the target and limits.
This checkpoint adds no Haskell patch or new production defect.

## Strongest current claim

For a validated finite graph, the checked exact-size model returns exactly
the distinct accepted terms of the requested node-count size. It counts
them correctly. Rank and unrank follow the specified order and are inverses.
Cyclic graphs are included. Ordering and solver contracts remain explicit.

The checked recursive native intersection has exact intersection semantics
for supported closed resident Original operands. Initial numeric resources
construct supported physical executions. A complete constrained outer pass
preserves the full guarded language on finite ordinary terms. This last
domain excludes Mu, references, and explicit unions in every descendant.

These are separate checked results for the implementation model. They do
not establish that every valid public Haskell call terminates and satisfies
its contract. The full target remains, for each public operation:

`Valid(input) ∧ InitialSupportAndResources(input) ⇒ termination ∧ Spec(input, result or error)`.

The initial support predicate must not assume successful future execution.
Passing an Audit does not supply a missing Haskell correspondence theorem.

## Exact selected edit phases

`SourceCurrentSharedEditChildLineage.Slice` records one actual child position.
It retains its original input, captured start and finish states, and memo
bundles. It retains actual `EditChildren` executions on the preceding and
following lists, with their matching `ChildrenReads`. The source offset is
preserved. Dispatch is either an unchanged unselected child or an actual
selected `EditNode` with `NodeReads`.

`indexed` derives this decomposition from actual child reads.
`selected` transports initial Ready data, availability, selected domains,
global memo validity, and native history through the exact prefix. It
derives Ready and native histories at the selected call's start and finish.
The heaps grow from the initial state through those states to the actual
final child reader. The theorem does not assume their histories separately.

`row_child` follows actual `makeNode` normalization. A final surviving row
and selected child retain original source row and child indices. The theorem
retains the full original symbol and guard, ordered children, actual selected
node read, histories at its captured states, and growth into the final node
heap. The existing selected path domains remain explicit. Unselected values
can be open or contain Mu. No whole-forest closure or global Cap is added.

These results describe completed reads. They do not construct general outer
completion or exclude collision with an active outer owner.

## Class right-fold phases

`SourceCurrentClassPassPhaseLineage.fold_indexed` decomposes an actual class
right fold at a source occurrence. The tail `records.drop (index + 1)` runs
first. The selected class runs next. The head `records.take index` runs last.
All three executions retain their exact values, states, local memo, and
global memo bundles. Equal class records remain separate indexed occurrences.

`fold_phase` transports the initial supported invariants through this actual
schedule. It derives captured Ready and native histories at the selected
class entry and return, with growth into the actual final reader. It retains
the existing coherent active records and selected path domains. It adds no
global closure, future history law, new Parent range plan, or phase decrease.

## Actual native node writers

`SourceCurrentNativeNodeWriterHistory.Written` retains the exact captured
request and evaluating node handle. It records an actual complete
`compileNode` body, its literal returned value, and its protected finish.
It also records Good and readiness at entry, the retained evaluating owner,
and growth from both body endpoint heaps into the reader heap.

`writers` derives that receipt for every returned node cell from the existing
actual causal native history. `warm` uses actual lookup and demand to identify
the full captured request, under the existing key-safety premise. The body
result for a Mu case is the complete `compileNode` value. It is not identified
with the callback's ordinary body result.

An internal active-owner state need not have the completed endpoint history.
The theorem does not assume that it does.

## Ready cells at a later reader

`SourceCurrentNativeWriterReadyRetention.trace_retained` derives native
ready-cell and handle retention from actual checked steps.
Its stronger `Written` keeps the same node body and finish receipt and adds
retention from the body return's complete native state to the reader.
`Written.forget` recovers the earlier heap-only receipt.
`writers` derives the stronger receipt from the same actual causal history.

`edge_writers` transfers each ready edge cell at that body return to the
final reader. The final reader's edge history then supplies its actual
earlier edge writer. This avoids an unsupported history premise at the
internal active-owner state.

`SourceCurrentNativeReaderRowLineage.edge_returned` first derives the exact
returned edge cell from Good and an actual complete edge call. It needs no
initial completed history. The cold branch uses the captured protected owner.
The warm branch identifies the full original request.

`rows_child` starts with an actual completed `compileRows` call, initial Good,
a final reader history, and explicit retention from the compilation return
to that reader. Actual suffix and `makeNode` traces retain the selected cell.
The reader history supplies its earlier writer. The theorem derives original
row indices, full symbol and joined guard, same-index original children,
and an actual earlier child query with Good endpoints and growth into the
reader heap. It requires no history at the internal compilation states.

The retention input describes actual completed states. Actual later traces
and the stronger node-writer receipt produce it. It is not a theorem that
arbitrary initial input will reach those states. On a warm hit the earlier
child call can precede the current body. No current-body ancestry or global
event embedding is claimed.

## Active stored-substitution induction

`SourceCurrentStoredMuActiveChildLineage.Compatible` equates the resolved
replacement values of the two own names. The two outer maps also agree,
including absent entries, on every fixed capture's free names.

`Aligned` compares actual warm raw source calls and their actual warm
reconstructions at a common Ready heap. `reference` proves the active-name
and fixed-capture base case. `StrictChild` retains actual source row and child
membership and a strict syntax-size witness. `ordinary` derives the ordinary
parent case from `Aligned` only for these strict source children.

The parent proof derives row survival, complete symbols and guards, ordered
child observations, and physical Empty agreement. Closed shortcuts remain
included. Normalization uses row membership; it does not assert an indexed
bijection between normalized row lists.

`node_complete` starts from past raw source calls, their contexts and growth
into a common Ready heap, available inputs, and replacement availability.
It constructs both sequential stored calls and their local publication
histories. It derives final availability, warm replay at the common final
reader, and `Related` for the results. `Related` means physical Empty
agreement and observations at every depth and fixed view. It does not mean
literal equality of Mu atoms or a general root-filter law.

The strict-child hypothesis remains explicit. The nested-binder case still
needs compatible extended captures. Existing common cache winners also need
chronological source-writer alignment. The local histories of these two new
reconstructions do not establish that missing earlier-winner law.

## Validation and preservation

All six new strict source checks have empty logs. All canonical targets pass.
All 23 new public declarations have complete signature, proof or definition,
and axiom output. The probes use all eight required print options. They have
no omitted terms, printer failures, or nonstandard axioms.

Full pinned Audit passes 3154 jobs and 69499 dependency checks. It replays
only the unchanged unused `inputs` warning in
`InternedFreshOrdinaryClosedCompletion.lean:24:5`. Effective memory maximum
and high are 4 GiB. Swap maximum is zero. Audit peak is 366 MiB.

Constructed checks derive real selected sibling leaf calls in sequence,
class-fold tail and head execution, native captured writers, retained ready
cells, and active ordinary reconstruction. The active reconstruction fixture
uses distinct raw parent identities, a nested ordinary child, duplicate rows,
a removed row, and a nonempty reconstructed node. Its fixed productive Mu
capture is closed. Map agreement on its free names is therefore vacuous in
that fixture; the generic base theorem covers arbitrary free captures.
The active fixture has signature and axiom output. The public induction
declarations have complete proof output.

A separate reader-row fixture constructs an initial cold edge call with an
ordinary child and a productive Mu child. Actual constructor work then
creates a distinct ordinary operand. A later cold node call runs row
compilation while its owner evaluates. It reuses the earlier ready edge.
Actual finish steps derive retention into the final reader and publish the
node result. The reader-row theorem recovers full guards and the historical
Mu child call. The fixture supplies no future trace or returned-value law.
It does not prove general Mu body alignment.

Six constructed declaration pairs pass. Five have complete proof output.
The active stored-substitution fixture has signature and axiom output.

Evidence is in `restart-evidence/20261017-selected-child-lineage/`. Preserve
every failed attempt and earlier evidence file. The preservation verifier
checks the 22071 starting files, 3147 old non-Audit Lean files, all 242 Haskell
files, 206 active-package files, 120 frozen manifests with 911 module pins,
two stashes, and three other worktrees. Audit adds only the six declared
imports. No Haskell source changed, so the current source validation remains
the retained Nix build and 798 examples plus the golden check.

## Remaining work

The largest mathematical gap is general recursive outer-node progress.
Exact row and child origins need a causal measure compatible with physical
memo keys and every active ancestor. Top inherited payloads and nonempty
local classes remain included in this obligation. A copied child can need
fresh work before its original sibling. Whole-value descent is insufficient.

Next, compose the exact selected-child and class-phase receipts with native
row writers on the same actual execution. Retain full guards, ordered child
positions, complete captured requests, and final-reader growth. Prove a
decrease or owner separation for all active node frames. A source-only label
does not exclude a physical-key alias.

Complete the retained-Mu binder case and chronological warm-winner alignment.
Then compose smart cleanup and root filtering. Heap growth over four cache
tables does not transport the issued-reference ledger. Keep freshness and
ledger obligations explicit.

Repeated-pass convergence, remaining recursive callers, frontend validation,
concrete lazy Haskell publication and interning, external adapters, and full
public pipeline composition remain open. The optimized interned core stays
in place. Root FINDINGS keeps the external Haskell repair registry first.
Field-pool repair `b9219b9e` remains merged and validated.
