# Actual parent histories and indexed edited rows

Proof checkpoint: `c1be0445`. Starting checkpoint: `97451269`.
Source main remains `c0cc8a05`.
The full-library goal remains active. Read
[the proof status](notes-proof-status-20261017.md) for the target and limits.
This checkpoint adds no Haskell behavior patch or new production defect.

## Actual native history transport

`SourceCurrentParentNativeHistory` transports persistent native edge-writer
history through actual Target, Force, and Leaf calls. Actual node, child,
and row edits retain history and constructor validity at their exact
returned heaps. These edit laws need only initial constructor validity,
initial history, and the existing actual Reads. Global memo validity is a
different type. The proof does not substitute it for constructor validity.

The ordered class pass also retains history. Actual native query traces
produce the history changes. Constructor and physical stages retain the
native tables and derive growth from their actual executions. No caller
supplies a history law for a future stage.

The complete Parent law follows actual Scan, Required, ordered class edits,
local reduction, and the returned edge constructor. It retains the existing
Parent range plan and initial Ready, admission, available operands, field
readback, inherited readiness, and emptiness memo correctness. It derives
history at the actual returned checked state. Class-pass and edit history
transport do not require the Parent range plan.

This is a theorem about a completed Parent graph. It does not construct a
future outer Parent call or establish general recursive progress.

## Indexed actual rows

`SourceCurrentSharedEditRowLineage.children_indexed` identifies the same
original child position. An unselected child is unchanged. A selected child
retains its actual `EditNode` call. This theorem does not retain the preceding
child execution. It does not derive native history at that child's start.

`rows_indexed` derives the exact original index of each raw rebuilt row.
It retains the full original symbol and guard, ordered returned children,
actual child execution, and the literal `makeEdge` result. It also retains
the exact `EditRows` execution of all preceding source rows, with matching
`RowsReads` and the actual memo bundle at the selected row start. Captured
row-start and constructor states have Ready. Their heaps and the returned
edge heap grow into the actual final row reader.

`node_survivor` follows actual `makeNode` normalization. Every final row
comes from an indexed live raw row. It retains the same exact fields,
captured execution receipts, and growth into the final node heap. It does
not assert a bijection. Normalization can remove, reorder, and merge rows.

These theorems use actual completed reads and initial physical facts.
They do not assume a guard-origin law for a returned row. Arbitrary values
can occur in the children. The proofs do not require an ordinary-only or
whole-forest closed domain. Existing selected path domains remain explicit.

## History at the same captured row

`SourceCurrentParentRowWriterLineage.node_survivor` composes these results.
Initial history follows the exact preceding `RowsReads` to the selected
row start. Its returned constructor validity supports the selected row's
actual `ChildrenReads`. The theorem derives history at the same captured
start and constructor states. It retains the original source index, full
fields, ordered children, live-row test, and growth into the actual final
node reader. The theorem adds no history premise for a captured later state.

These histories concern native edge writers. They are distinct from Mu
publication histories and from active outer memo owner frames.
The heap growth relation retains four cache tables. It does not establish
transport of the issued-reference ledger. Freshness obligations remain
explicit in the retained-Mu correspondence work.

## Constructed executions

Seven constructed checks cover the new composition. The row fixture starts
from its own state. Raw rows have order `[second, dead, first, second]`.
It executes selected and unselected child branches. A full nonempty equality
guard and an unselected open depth reference remain. The selected Empty child
makes one row dead. Normalization removes that row, reorders live rows, and
removes the duplicate. The raw index-two execution prefix and both captured
writer histories are derived from that execution.

A separate fixture constructs a nonempty class pass over finite, recursive,
and open values. No one global Cap contains that forest. Initial numeric
room and selected path domains construct the pass and its returned history.
The Parent fixture constructs initial numeric completion on the unchanged
precheck branch, followed by actual edge construction. It does not separately
exercise a full Parent classes branch. The public Parent theorem includes
that branch with its explicit original range plan.

The independent-child fixture builds two actual used-Mu source calls with
different unused outer assignments. Two distinct replacement maps agree on
the fixed supported reference. The theorem constructs equal sequential stored
results and an exact full-state warm second call. The result remains Mu.

## Independent retained-Mu children

`SourceCurrentStoredMuChildLineage.independent` handles a source child that
does not use a varying callback argument. Two actual past raw calls grow
into a common Ready reader. The replacement maps agree on the fixed source
support. The initial raw value and first map's replacements are available.

The theorem derives exact raw equality. It then constructs both stored
reconstructions in sequence with one exact result. The second call retains
the entire first returned heap. The theorem retains warm replay, Keeps,
result availability, and the local publication history. Source children
and captures can contain arbitrary nested Mu values. The caller supplies
no future reconstruction, output relation, or final reconstruction heap.

This is one induction case. Active children can contain the changing own
name. Their nonempty results still need a coupled source and chronological
writer induction. Smart Mu erasure and earlier warm winners remain part
of that obligation. The independent case does not remove them.

## Remaining boundaries

General outer progress still needs source-row occurrence information that
is compatible with every active owner's physical request key. A decreasing
causal label alone does not exclude aliases. Class-only height conditions
give no witness for a Top inherited payload. The precise obstruction and
source review are in this checkpoint's evidence directory.

The actual native writer histories and indexed row executions provide
inputs to that missing argument. They do not establish general outer
termination. Repeated-pass convergence, active retained-Mu alignment,
frontend/runtime adapters, and full public Haskell correspondence remain open.

Current evidence is in `restart-evidence/20261017-parent-row-lineage/`.
The final full pinned Audit passes 3148 jobs and 69431 dependency checks.
All four new strict logs are empty. Thirteen complete public signature, proof,
and axiom checks pass. Only propext, Classical.choice, and Quot.sound occur.
Seven constructed signature and axiom checks pass. Six also print complete
proofs. The independent-child constructed check prints its signature and
axioms; its proof is checked in the strict source.
The Audit replays one unchanged old unused-variable warning. Effective memory
maximum and high are 4 GiB; swap is zero. Audit peak is 383 MiB. The selected
JSON receipts and manifests retain exact constructed checks and file hashes.
Older attempts and evidence retain their bytes. Earlier private-premise lint
warnings remain in the failed or superseded history attempts. Final strict16
is truly empty. Earlier descriptions of some superseded logs as empty were
inaccurate; those descriptions do not apply to the selected final evidence.
