# Captured class tasks and final physical readback

Source main remains `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Starting checkpoint: `7b956d72`. Proofs: `ec3ebf72`, `305da606`,
`c2321463`, and `66b9c097`. The preceding generic trace and inventory
proofs are in [the delayed-worklist note](notes-delayed-emptiness.md).

## Checked task and heap properties

`SourceEmptinessClassFields` passes physical annotation heaps through the
actual plain projections and native leaves of both class-fold schedules.
The concrete source top and conjunction derive normalized emitted fields.
The proof reuses the existing compiled native annotation certificates.
It does not assume the desired final heap.

`SourceEmptinessTasks` stores original complete values or captured class
handles. Each class cell retains its original child forest and ordered paths.
Capture changes task storage without running native work. A first force
runs the actual analysis fold at its reached scoped native state. It stores
the returned complete value. Later hits return that value without effects.
Actual forces derive closed available output, physical history, task-store
readiness, and retention of every previously completed result.

`SourceEmptinessTaskRows` retains the exact child prefix and stored class
order of each source row. Natural paths become signed paths without changing
their order. Ordered receipts identify the exact suspended class bodies.
Actual completed nodeEdges reads derive closed available child forests.
The exposure graph retains the returned constructor heap and captures rows.
Every closed available input has finite exposure in this graph.

`SourceEmptinessTaskFields` preserves normalized fields through actual forces
and exposure. The first-force proof uses the captured forest and actual fold.
Hits and direct values keep their native state. Exposure uses the actual row
read and the fact that pure capture has no native effect.

`SourceDelayedEmptinessInventory` derives final physical records by induction
on the reached worklist. Local force and exposure laws preserve earlier
records and certify actual admissions. It assumes no final heap invariant.

`SourceEmptinessTaskTrace` instantiates those local laws with the task graph.
It derives final availability, closedness, and exact keys for all stored
records. It derives complete task reads for every newly stored row in one
final heap. Previously completed results remain unchanged. The literal table
readout retains every original key. Its empty read fallback is unused on
certified returned rows. Certified closed encoding agrees with the previous
physical-key encoding.

The resulting readback theorem needs no supplied inventory, coverage,
final-record validity, or final-coherence premise. It still operates on the
certified closed resident domain. It does not prove raw record readback.
The source theorem derives finite original closed construction, initial
task readiness, and normalized fields from normalized source annotations.

The completed table has at most the admission budget's number of entries.
After row completion, budget + 1 equality checks suffice for the existing
least-fixed-point computation. This does not bound native calls, allocation,
or task forcing, and it does not prove exploration completes.

## Source and semantic limits found in review

This graph uses complete nodeEdges reads as exposure leaves. It captures
all rows before child work. Haskell exposes later lazy rows progressively.
The graph therefore does not establish exact Haskell row demand, original
child-thunk evaluation, or the complete native cache-effect schedule.
Logical task handles model sharing within each captured requirement.
They are not a proved representation of GHC closures or machine identities.

Task readiness establishes availability and closedness of saved results.
It contains no law about the language of those results. These physical laws
alone can therefore admit a saved EmptyNode for a productive captured body.
The reached miss graph supplies the actual fold, but its semantic property
still needs transport through the task store and later hits.

The current suspended `ClassReceipt` also requires result = none. It does
not describe a filled cell. Derive an immutable body receipt that survives
capture, finish, native advance, exposure, and the complete reached trace.
Derive a saved-result invariant: each common selected proper subtree of an
accepted captured forest is accepted by its completed result. Start with the
empty store. Capture adds a suspended cell. A miss uses Fold.included and
class_witness at its actual ready state. A hit uses the saved invariant.

Then combine accepted source exposure, normalized satisfied classes, and
final task reads to derive smaller accepted requirements for the literal
table. Physical readback alone does not establish these semantic laws.
Do not assume total intersection or projection closure of a fixed final
resident heap. Those operations can allocate more records. Derive the
requirements of the actual finite calls directly.

Model progressive row demand and original child forcing separately. Transfer
the old scoped native leaves to the newer checked constraint-operation state.
Derive reached word ranges, native completion, and each oracle call. Compose
both gate modes and the three memo families through the current lazy class
scan, selected fallback, and caller. Whole current reduction remains open.

The full library scope remains unchanged. Runtime correspondence, identity
capacity and reuse, derived refinements, named measures, getAllAtPath,
decision-model, parser/decoder bridges, recursive generators, and extraction
remain separate targets. Keep the optimized interned core and older proofs.
Sized exact node-count classes, finite class execution, canonical sequence,
distinct size order, and both signed inverse directions remain separate.

## Validation and preservation

The full pinned Lean build passes 2,014 jobs and 51,484 theorem dependency
checks. Only propext, Classical.choice, and Quot.sound occur. No new warning
occurs. The old ClosedCompletion unused-input warning remains. The aggregate
log is `/tmp/mcfta-source-emptiness-thunks-audit-20261015.log`.

All prior Lean definitions remain unchanged except one additive Audit import.
All four Haskell package trees match `7b956d72`. Their prior Nix validation
was not repeated. All prior repros, marked drafts, external drafts, stashes,
and other worktrees remain.
