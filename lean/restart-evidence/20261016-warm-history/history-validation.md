# Serial checked warm history

Validated 2026-10-16 06:29 CEST. `SourceCurrentAllocatedNativeWarmHistory.lean` is frozen
at SHA256 `eb59b9b5f2f101a72446f42cc56c22e93af173c8e861d2dfa517ff2f2631860a`. The file has 162 lines.

## Result and public API

`program pairs` is the literal existing `Code.walk` of empty-domain node
requests. It keeps the pair order and actual continuations. No new code AST
or effect-free query callback is introduced.

`Admissible source formulas solver inputs pair` records the original and
available operands in the fixed source heap, both closed free lists, and
both input memberships in the same `FiniteInput`.

`walk_complete source facts formulas solver inputs pairs state valid
contextual scopedCache semantic idle growth history admissible ranges`
derives one completed actual ordered walk. The output is an existential
`Receipt source formulas solver inputs fuel pairs state values after`.

The receipt extends the actual physical trace receipt. It retains the exact
trace, final `Good`, machine `Extension`, heap `Keeps`, operation-cache
growth, and every returned value's final availability. It also records the
same fixed contextual model, the returned scope cache, `SemanticReady`,
idle native cells, and closed result free lists.

Two ordered `All₂` relations retain the exact pair/result association:
contextual `NodeLaw` and independent physical intersection-language iff.
The relation preserves order and multiplicity.

`Memoized after pair value` records actual final table publication and the
exact original request's returned cell whenever its literal request key is
`some key`. The receipt derives ordered final memo evidence for every pair.
`Receipt.warm` derives an exact two-step repeat for each such pair at the
final state. The whole checked state remains unchanged on that repeat.
`Receipt.done` erases the history to actual checked execution.

## Why the induction is causal

The cons case obtains head word bounds using `before_bind` on the original
whole-walk range plan. `WarmQuery.query_complete` derives the actual head
trace and returned invariants. `after_body` then uses that exact trace to
derive continuation bounds. A second `before_bind` derives the remaining
tail's bounds. The tail receives only these reached invariants.

The physical trace composes the actual head with the actual tail. Earlier
results remain available through the tail's derived extension. The head's
literal completed cell is obtained from `CompletedMemo.completed_node`
using its actual completion and current physical readiness. The tail's
actual completion derives `done_retained`, which preserves both the table
publication and returned cell through the rest of the history.

No per-query completed-prefix callback, future physical invariant, future
semantic result, final-cache premise, or model refresh is supplied.

## Initial premises and scope

- The input `FiniteInput` is fixed for the entire serial history.
- Initial `Good`, fixed-model `Contextual`, `ScopeCache.Scoped`,
  `SemanticReady`, and idle native state remain explicit.
- Source-to-current heap growth and issued-key history remain explicit.
- Every listed pair must be original, available in that immutable source,
  closed, and valid in the fixed input model.
- Reached `WordRanges` are supplied once for the whole actual walk. Every
  head and tail plan is derived. No global machine-width capacity bound is
  proved here.
- Warm-hit evidence is conditional on a literal cacheable request key.
  A `none` key has no publication or warm-hit claim.
- The separate cold adapter can derive the fixed model and membership from
  the actual finite operand inventory. It is owned by the root task.
- The theorem covers serial completed checked-machine execution. It does
  not establish GHC lazy demand order, concurrent pending publication,
  physical machine-container representation, or other global query memo
  families that are absent from the checked state.

## Validation

Focused pinned build:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeWarmHistory

Exit 0, 1126 jobs. No new warning. The pre-existing unused `inputs` warning
was replayed from a dependency.

Public probes:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-warm-history/history-probe.lean

Exit 0. All three public theorem axioms and all three signatures pass.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

Three kernel examples verify:

1. Ordered result length, exact execution, the derived physical input plan,
   and final unchanged warm repeats from a receipt.
2. Actual serial completion with arbitrary extra fuel, final physical and
   semantic invariants, closed resident values, and ordered independent
   intersection language.
3. Repeating one cacheable pair twice yields `[value, value]` in the actual
   history and repeats unchanged at the final state. Equality follows from
   the two derived literal warm executions.

Only the new owned history module and new evidence files were written.
No frozen proof source, Audit, documentation, Haskell source, or Git state
was edited by this task.
