# Independent native budget scope review

Reviewed: 2026-10-16 19:04 CEST.
Verdict: No material defect found in the checked component.

The principal module exposes two computed budgets and four prefix theorems. `node_prefix_budget` and `edge_prefix_budget` derive all profile, code, original-request, and word certificates internally. Their inputs are initial `Good`, initial operand availability or edge residency, finite ordinary domain proofs, initial two-counter `Capacity`, and an actual finite `Demand.Steps` prefix. The prefix is an observation of execution. It is not a completion or desired-result premise.

`NativeBudgetCompile` derives the recursive costs from the literal node dispatcher, source row join, child zip, sentinel, and checked edge body. The row-pair bound preserves multiplicity. The zip bound needs no equal-arity premise. The sentinel branch needs no semantic guard truth. The node scheme uses the larger original height and the computed common row and arity envelope. Swapping operands has the same cost. This is sufficient for a prefix potential bound. It does not establish a strict step measure or termination.

`NativeBudgetExecution.step_bound` consumes only observed literal Work requests. Recursive starts use exact captured-owner readback through the initial physical origin invariant and safe typed keys. Ready hits skip their producer budget. A finish retains its continuation budget. The edge-body step can change equality operations while leaving the two constructor heaps fixed. `prefix_bound` composes these one-step facts by induction on the supplied actual prefix. Both generic compiler and body-bound parameters are discharged by the principal module. No public principal endpoint requires a future body certificate, completed query, output law, request-count bound, final readiness, or final capacity.

`QueryReservations.prefix_bounds` links these request counts to both actual constructor counters. Each prefix counter is at most its initial counter plus the same conservative combined node-and-edge budget. The capacity endpoints require initial supplies plus this computed budget to fit the separate layouts. The width is `bits + 2`. They preserve capacity at the exact supplied returned state.

Independent imported checks pass: six public declaration axiom/signature pairs and two integration pairs. The two integration kernels derive initial WordRanges and capacity at every actual yielded prefix solely from initial physical facts, original profiles, and computed headroom. They allow full guards, unequal edge arities, and warm tables. They require no execution completion.

Remaining scope is explicit. This bounds constructor requests in one sequential checked native query over original finite ordinary operands. It does not count all instructions, prove termination, count equality interner or sidecar allocations, bound result/domain/memo memory, or model concurrent losing reservations in the Haskell host. It does not yet derive a cumulative budget for successive generated queries or the full outer reduction. Mu, reference, and explicit union records remain excluded. The actual machine packing and GHC publication/runtime bridges remain separate.

Source references:
- `SourceCurrentAllocatedFiniteOrdinaryNativeProfile.lean`: mutual computed maxima, recursive shapes, and literal pair bound.
- `SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.lean`: full-expansion recurrence and height monotonicity.
- `SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.lean`: `rows_bound`, `node_bound`, `children_bound`, `sentinel_bound`, `body_bound`.
- `SourceCurrentAllocatedFiniteOrdinaryNativeBudgetExecution.lean`: `step_bound`, `prefix_bound`, `prefix_supplies`.
- `SourceCurrentAllocatedFiniteOrdinaryNativeBudget.lean`: `nodeBudget`, `edgeBudget`, and four principal prefix endpoints.

Validation: `native-budget-build-2.log` records canonical terminal exit 0, 1111 jobs, with only the existing dependency warning. The final independent logs are `native-budget-independent-public-1.log` and `native-budget-independent-kernels-1.log`. Both exit 0 without warnings, errors, or `sorryAx`. No proof source, Haskell source, prior evidence, Audit, or root documentation was edited by this review. No Lake process ran here.
