# Independent output producer review

Reviewed 2026-10-16 19:31 CEST. No material defect found. No production source changed.

Frozen principal sources under lean/MicroCFTA/:

- SourceCurrentAllocatedFiniteOrdinaryOutputExecution.lean, 275 lines: bc65ca22a2d070bd809ce09a7a15b33d25f430daef0eba31bc7e1bea55791660.
- SourceCurrentAllocatedFiniteOrdinaryProfileBudget.lean, 106 lines: a4902c26116a5722576f34a76bcaee5dd5284001ab4dd2cbc840fa86dcd33881.
- SourceCurrentAllocatedFiniteOrdinaryOutputFinite.lean, 130 lines including cold: d98b0d11840b3de122cbaa93c4cb193c7e6a5a289636e29942907c80ee97751e.

All eight production hashes match root frozen-modules.json.

OutputExecution.verified:77 follows the actual checked physical trace by strong induction on its length. Each miss identifies the literal stored owner. The bind split retains the same body, finish, and continuation states. Smaller body traces derive certificates before their protected original finishes install them. Warm hits use OutputStored for the exact requested operands and returned value. Prefix effects derive Good, SemanticReady, field facts, and machine growth. No eager execution or supplied same-parent output law closes the induction. node_trace:246 and edge_trace:261 derive their component certificates from the original profiles and empty seen list. Local CertifiedControl is an explicit code-certificate premise only in the generic interpreter theorem.

The local constructor/node/edge code was also read. Original row pairs bound output rows by R squared. The actual child zip supplies each child profile. Rejection skips child demand and returns the one-child sentinel. Its output arity bound is max(A,1). Coherent constructor hits retain exact requested records. Empty-seen and profile/domain inversion exclude the recursive/reference/union cases covered by other library components.

ProfileBudget:19-57 structurally bounds the computed literal operand limits by a uniform original profile. Parameter monotonicity at 62 and 73, then node_budget_le:87 and edge_budget_le:97, bound the actual input-derived reservation. These proofs inspect no future result or request count.

OutputFinite.finite:32 constructs physical completion from initial Good, SemanticReady, causal old/new Stored, Idle, operand availability, profiles, heights, and initial counter headroom. The SAME receipt.trace supplies its output profile; the SAME trace.steps supplies final counter bounds. cold:65 derives both Stored invariants and Idle from literal initial native tables. serial:96 passes the first actual output profile, residency, height, and returned state into the next query. It has no second-profile, future-success, range-plan, or result-law premise. Good and SemanticReady remain explicit physical inputs; cold does not establish GHC initialization or noConstraint CAF transfer.

The independent kernels test more than aliases:

1. cold_repeat_generated constructs a cold query, derives its actual completed cell and execute-2 warm repeat through CompletedMemo.repeat_of_trace, independently constructs the repeated query, and aligns its output and WHOLE checked state through completed_unique. It then constructs a query of the first output against the original right operand. Initial headroom is 2*N(R,A,H)+N(R squared,max(A,1),H). All three physical receipts, exact unchanged warm execution, final profile, capacity, and counter bounds are conclusions. No initial result certificate, future cell, or second-input profile is supplied.
2. warm_node_trace constructs a one-step physical trace from explicit initial ready lookup/demand facts, then applies node_trace to retain the profile at the same full checked state.
3. edge_trace_budget combines edge_trace with actual prefix accounting and the uniform computed-limit budget. The output profile and both counter bounds describe the SAME result and state.
4. serial_literal derives both exact interpreter returns, final generated profile, and capacities from the public serial endpoint.

The result does not yet derive cumulative target/edit/class/outer numeric plans. Warm initial OutputStored is an explicit causal premise outside cold initialization. Arbitrary nonempty-seen domains, other runtime resources, and solver/GHC/IO transfer remain separate obligations.
