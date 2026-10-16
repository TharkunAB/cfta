# Same actual outer Work counts

The frozen module is `SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.lean`.
It has 477 lines. Its SHA-256 is `a96b2c8848afec618a15cdc7dac59e1728622124ed8888ca62a42d57261515e6`.

All eight public execution-family theorems consume the supplied actual strict Reads.
They derive one ConstructorWorkTrace at those exact initial and returned heaps.
They require the initial semantic Context, inherited equality readiness, resident finite-ordinary inputs, and causal quantitative stores.
The input row, arity, height, and hereditary guard envelopes are explicit.
They require no Capacity, reserved headroom, numeric entry Plan, final Context, or future result law.

The induction follows the literal source order. Each original row first runs Parent.
The next induction uses the returned parent's derived profile and guards.
It then traverses the returned children and resumes the original row suffix.
Descendants does not pay for Parent a second time. Its raw edge rebuild costs at most one edge request.
Ordinary node reconstruction costs at most one node request.
Inherited combine and indexed descent retain the heap and emit no constructor Work.
A warm outer memo hit retains the heap and emits no constructor Work.
The proof aligns the captured stored owner before it applies the smaller body induction.

The node totals are OuterBudgetNumbers.nodeNodes/nodeEdges.
Edge calls and bodies use ParentUniformBudgets.nodeBudget/edgeBudget.
Rows multiply their original length by rowNodes/rowEdges.
Descendants uses descendantsNodes/descendantsEdges at its supplied returned-edge envelope.
Children and Walk multiply their original length by the node totals.
WorkBounds.next_le derives both returned supply bounds from the same actual trace.
The trace counts literal constructor requests, including requests that hit constructor caches.
It does not count instructions, host allocations, or GHC forcing events.

## Validation

The pinned toolchain is Lean 4.34.1. All final direct and standalone checks enable every linter.
Both final standalone sources enable explicit proofs, universes, deep terms, full names, and one million print steps.

- Full source direct-1: process 56016, terminal exit 0, no diagnostics.
- Final full source direct-2: process 26412, terminal exit 0, no diagnostics. This adds WorkBounds.next_le.
- Isolated imported public checks: terminal exit 0, 13 axiom and 13 full-signature results.
- Isolated imported integration checks: process 50586, terminal exit 0, two axiom and two full-signature results.
- Final canonical-import public checks: terminal exit 0, 13 axiom and 13 full-signature results.
- Final canonical-import integration checks: process 80397, terminal exit 0, two axiom and two full-signature results.

The final imported logs have no warnings, errors, sorryAx, omitted terms, or truncation.
The dependencies are the standard propext, Classical.choice, and Quot.sound where used.
The production source contains no sorry, admit, or new axiom.

The root-owned canonical log `outer-work-resource-defs-canonical-1.log` records this module built successfully at 1658/1659 in 5.5 seconds.
The whole batch exited 1 only because the separate new OuterResourceDefs module failed an arithmetic proof.
That batch status is preserved. It is not reported as a whole-batch pass.
The historical dependency warning about `inputs` is outside this module.

The two integration kernels prove:

1. The actual evaluated owner remains published through its smaller body. Finish installs the derived certificate. The literal repeated demand is ready at the identical full caller state. The original call has the computed Work bound, and the warm repeat has zero Work.
2. The same ordered actual Rows return retains its full Post and quantitative stores. The result length is unchanged. The recorded constructor requests bound both final supplies.

The failed core and pre-parent drafts are retained with their exact source snapshots and logs.
The pre-parent-2 check closed every branch except the intentionally unavailable ParentWork dependency.
No compiled artifacts are stored in this evidence directory.

## Scope

This is a verifier for supplied completed strict Reads. It does not establish that every raw outer call terminates or that initial headroom admits every reached call.
The separate initial-resource recursion must construct that execution and its entry admission.
Finite ordinary excludes Mu, explicit union, and references throughout the input. Its guards and equality classes remain unrestricted.
General recursive constrained inputs and full Haskell correspondence remain separate obligations.
