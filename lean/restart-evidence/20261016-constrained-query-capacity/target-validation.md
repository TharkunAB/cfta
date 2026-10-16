# Causal numeric target capacity

Validated and frozen at 2026-10-16 18:16 CEST.

`FoldCapacity` follows the existing literal right-fold schedule. Its first clause restricts the plan after an actual earlier head operand. Its second clause checks only numeric constructor supplies after that operand and an actual earlier tail fold. `TargetCapacity` retains the literal seed and ordered paths. Neither plan assumes a current native query completes. Neither contains a returned readiness, domain law, graph completion callback, or future key list.

`fold_ranges` uses induction on the remaining path list. A ranges-free operand receipt derives the initial facts for the smaller tail. The induction hypothesis derives that smaller tail's ranges. Only then does the proof verify the earlier actual tail with the existing structural theorem. That exact receipt derives current readiness, tail residency/domain, and retained head availability. The numeric capacity at this state supplies the current query word checks.

`finite` constructs the actual target graph, actual target reads, full same-state receipt, native/merge structural certificates, and finite ordinary result domain. It takes initial legitimate invariants and the numeric causal plan. It takes no completed target or supplied successful worker execution. Captured guards and equality classes remain unrestricted. Duplicate paths keep their order and multiplicity.

The plans do not give an a priori total allocation bound. A singleton target has no native query and therefore needs no capacity premise. General constrained outer termination and host demand correspondence remain separate obligations.

## Checks

- Source direct `target-direct-2.log`: terminal exit 0, no diagnostics. The earlier failed draft log is retained; it contained an induction-hypothesis argument mismatch and one proof indentation error.
- Root canonical TargetCapacity target: passed 1305 jobs in the combined build. The first combined dependency batch failed in the separately owned SharedCapacity source. Its repaired aggregate passed 1307 jobs, terminal exit 0, root process 16730. Root primitive Capacity passed 1103 jobs.
- `target-public.lean` / `target-public-1.log`: seven public axiom and full-signature pairs; terminal exit 0.
- `target-kernels.lean` / `target-kernels-1.log`: seven kernel axiom and full-signature pairs; terminal exit 0. They check singleton completion without capacity, two-path causal numeric plans, exact numeric supply projections, current words before the current query completes, full state/inventory/global/cache retention, and duplicate path completion.
- SharedCapacity read-only review: six public pairs and three kernel pairs pass. See `target-shared-independent-review.md`.
- All four final imported logs have no errors, warnings, or `sorryAx`. Reported axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

Only one additive production file and owned evidence were written. No canonical build, Git mutation, Haskell edit, old proof edit, or root documentation edit was performed by this agent. Direct Lean used pinned 4.34.1 and canonical imported dependencies. The derived direct olean is under `/tmp`, outside this evidence directory.
