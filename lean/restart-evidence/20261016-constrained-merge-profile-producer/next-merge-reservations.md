# Next proof: actual ordinary Merge constructor reservations

Status: general recursive profile production is proved. Actual Merge
constructor request and reservation budgets are not proved. This is a proof
plan. The recurrence below has no checked production declaration yet.

Use the current actual MemoGraph Run/Call and allocated erasure. Do not use
a historical eager worker. MergeProfileProducer supplies physical effects,
both returned tables, and a universal profile certificate for the exact
winner. MergeProfileFinite constructs the actual allocated and literal
returns. All five current sources are frozen in frozen-modules.json.

## Static candidate budgets

Let R bound every original node's row count, A every original row's arity,
and H the original height. A coarse candidate for the two constructor
request bounds is:

```
N(R,A,0) = 0
N(R,A,H+1) = 1 + R*A*(1 + N(R*R,A,H))
E(R,A,0) = 0
E(R,A,H+1) = R + R*A*E(R*R,A,H)
```

The final root uses at most one node constructor request. There are at most
R*A direct child or column requests. Every retained non-singleton column
uses at most one additional ordinary-union node request. There are at most
R retained row constructors. Every recursive input has height at most the
parent's edge maximum and a profile bounded by R*R,A. A small child's R
profile can be widened because R <= R*R for natural R. A warm completed hit
skips all body work. Empty inputs use no constructor requests.

Prove these source-count statements and recurrence monotonicity before
claiming these budgets. If a branch needs a larger term, update the plan.
The bounds count all occurrences and may overcount shared subproblems.
They must bound actual requests, including constructor-cache hits. A cache
hit can use zero new reservations. Do not define work as the final counter
difference or bound only published cache entries.

## Exact next obligations

1. Interpret actual Run/Call with ConstructorWorkTrace. A Work instruction
   records its literal observations. Bind retains the exact middle heap and
   concatenates request lists. A Call hit has an empty trace. A miss uses its
   actual body trace, even when its candidate loses to an earlier winner.
2. Use MergeSelection.done at every ordinary selection. It identifies the
   unchanged entire heap and exact distinct original inputs at any fuel.
   No comparison constructor Work occurs in this ordinary domain. The
   imported actual-selection kernel supplies an empty constructor trace.
3. Certify local branch resource counts from original input profiles and
   height. Ordered maps must retain input/result positions and total request
   sums. Prove small-child and retained-column input bounds before invoking
   the smaller actual Call induction hypothesis. Keep selection, union,
   recursive call, row work, and row suffix in literal order.
4. Prove mutual actual Run/Call resource preservation with the initial
   physical and profile storage invariants. Derive the actual recursive
   outputs through MergeProfileProducer. Do not supply a completed body law,
   a future profile, or a bound on the actual request list.
5. Add an allocated finite wrapper. Construct its own call, request trace,
   and both final supply bounds from the original R,A,H. Top equality-field
   allocation is separate from these two constructor supplies.
6. Compose Required, Projection, Merge, and native queries in Operand and
   Target's rotated right fold. Derive every later profile, resident value,
   readiness fact, and remaining headroom from the preceding actual return.
   Continue through edits, class passes, local/parent calls, and the outer
   numeric plan. That plan remains an explicit premise today.

The existing Direct request receipt excludes requests inside nested Calls.
It supplies strict child-height facts, not the required cumulative Work
count. Actual profile production alone also supplies no reservation bound.
Use both results as dependencies rather than treating either as completion.

## Separate remaining scopes

Do not include equality, domain, sidecar, or thunk resources silently in
these two constructor counters. Count concurrent losing candidates and
intervening host operations in their own process-history model. Packed key
bounds do not prove signed Haskell counter bounds. Instruction steps and
selection evaluation fuel are separate from constructor requests.

General Mu/reference/union progress, repeated-pass convergence, current
frontend adapters, concrete Haskell execution, and full-pipeline composition
remain open. Preserve all older constructor/equality work and the optimized
interned core. The full-library goal remains active.
