# Minimum proposed literal stateful scan model

This is a control description. It is not a Lean implementation or a proof.

`RuleOutRun pivot candidates before promoted remaining after` records one literal worker run.
Its only comparison observation is `SourceCurrentSameSymbolEdgeControl.execute fuel (.call (pivot,candidate) []) before = .done common middle`.
The chosen fuel, full middle state and common result belong to that actual comparison.

- Empty candidates return `(none,[])` and the identical state.
- If `common.entry.identity = candidate.entry.identity`, continue on the suffix with the old pivot at middle.
- Otherwise, if `common.entry.identity = pivot.entry.identity`, return `(some candidate,suffix)` at middle without scanning that suffix.
- Otherwise, run the suffix with the old pivot at middle, then prepend the original candidate to the returned remaining tail.

The second branch MUST include failure of the first test. The third includes failure of both tests.
The generated common edge is used only by these tests. It is not pushed into candidates or used as the next pivot.
No equality/empty/self fast path can bypass the actual comparison call.

`ClusterRun cluster before kept after` records reduction with that worker.
Empty cluster returns the identical state and empty list.
For `pivot::tail`, run the worker at before. On `some candidate`, reduce `candidate::remaining` at the actual worker return.
On `none`, reduce remaining at the actual worker return and prepend the old pivot to kept.
The size lemma is `promoted.toList.length + remaining.length ≤ tail.length`; therefore both recursive cluster inputs are shorter.
The remaining worker tail is a sublist of its input. A promoted candidate is an original member. The final kept list is not generally an order-preserving sublist.

The public completion result derives such a graph; it does not assume a successful graph or future callback completion.
This is the smallest model consistent with the existing relational class-scan style. If root requires a new executable fuel equation, first expose literal scan frames and an H7-comparison frame, then prove that runner refines this graph. Reuse H7 step/execute; do not duplicate the native body.
