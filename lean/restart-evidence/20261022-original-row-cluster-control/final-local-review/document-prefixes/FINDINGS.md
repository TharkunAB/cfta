# Current formalization findings

## Haskell fix handoff for external work

### External Haskell repair status

No new Haskell repair is required by this proof checkpoint.

| Repair | Imported status | External action |
| --- | --- | --- |
| Recursive self-type field pools | Fixed by `b9219b9e`, merged in PR #65 at `c0cc8a05`. The API rejects a field pool for the datatype itself. This includes the reported `Chain` case. | No additional patch. Keep the historical reproducer and validation below. |
| Typing binder size-order documentation | Fixed by `74691832`, merged in PR #97 at current imported main `794903b3f`. This changes documentation. | No additional patch. The earlier failed runtime reproduction remains unvalidated. |

Both repairs are in the imported main history. No Haskell source changes
in this checkpoint. All earlier repair entries and evidence remain below.

## Original-row cluster control

Updated: 2026-10-22 06:27 CEST. Proof checkpoint: `272cb31f5f`.
Start: `4f7a7e064f`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-row-cluster-control.md`.

SourceCurrentOriginalRowClusterScan defines cluster, scan and comparison phases.
It reuses the complete populated H7 State and forwards its exact outcomes.
comparison_lift consumes one observed H7 done equation.
It derives a positive consumed prefix bounded by the supplied H7 fuel.
At that prefix, execute yields the inline resume at the SAME returned state.
The candidate identity test comes first. Promotion retains the reconstruction order.
Generated common results never become later operands.
No genuine-input cluster completion, new semantic law or resource law is proved.
H7 and this control are noncomputable. No compiled program or Haskell refinement is claimed.

H15 remains the checked comparison and domain-capacity foundation.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Physical pruning, generated parents, grouping, Mu, full traversal and the public pass remain open.
The overall goal is incomplete.

Preservation covers 86577 baseline files/modes, 298 baseline Haskell files
and 207 active package files. Only one Audit import and nine additive doc
prefixes may change old files. FINDINGS keeps its repair index FIRST.
The preceding 4f7a7e064 checkpoint is LOCAL_ONLY. Remote publication remains
PENDING_USER_APPROVAL. This tool performs no push or network command.

