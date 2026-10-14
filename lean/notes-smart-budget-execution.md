# Exact smart budgets through actual source execution

Updated: 2026-10-14 18:24 CEST. Proofs: `50d79bef`, `35e07971`, `a76a22f1`,
and `a7b5d94e`. Cold/native composition: `9ca74b4d` and `081ce3d1`.

## Exact smart decision

`InternedGuardedBudgetSmartFinish` proves actual filtered binder budget laws.
Root self filtering preserves the body language when the local language is
empty. A deep local occurrence retains the raw Mu step. Without a deep local,
smart finish gives the body with an empty local language.

`InternedGuardedBudgetLocalFinish.finish_local_exact` states the same exact
choice for normalized callback bodies. It uses the existing `Local` invariant
and actual coherent availability. No new cleanup analysis is supplied.

## Complete lexical interpretation

`InternedGuardedSmartBudget.evaluate` uses the existing
`InternedDepthSemantics.Shape`. Raw binders and smart binders with a deep local
use a budgeted Mu. Other smart binders evaluate their body at an empty local
language. Complete source guards and ordered children remain. This differs
from the raw pre-execution compiler interpretation, which charges every binder.

Positivity and upward-budget laws are proved. `evaluate_map` proves invariance
under arbitrary external shape-name maps. The maps can identify captured names.
The existing symbolic local remains distinct.

`InternedGuardedSmartBudgetSupport` and `SyntaxSupport.evaluate_related` prove
root bounds and support from the existing shape's complete free names. An
accepted forest has no empty child shape. Deleted node edges cannot accept a
term. `Values` supplies these bounds from actual coherent captured records.
Only surviving symbolic captures need freshness. Unused inputs can contain
the selected ordinary sentinel.

## Both canonical probe readbacks

`InternedGuardedBudgetProbeHeap.Correct` retains three proved properties:

- The stored body has the actual normalized local form.
- Its raw Mu budget language equals the Mu language of its exact ordinary probe.
- Its empty-local body budget language equals that of the ordinary probe.

The third property is required for exact smart readback. Raw Mu equality alone
does not select the unshifted empty-local language. `uses_eq` derives the exact
deep-local decision from the existing depth heap. `finish_language` and
`hit_language` then prove both actual finish branches at a canonical hit.

`InternedGuardedBudgetCallback.filter_view` derives both callback readbacks.
`uses_source` connects the actual ordinary probe to the existing symbolic
deep-local decision. `InternedGuardedBudgetRequest.request_heap` installs both
budget properties from actual fresh callback execution. Pending and canonical
branches retain existing complete records. `request_language` reads the actual
stored payload and its complete requested probes.

## Actual source and stored execution

`InternedGuardedBudgetExecution.build_language` proves exact source execution
and budget-heap preservation in one complete syntax induction. It retains the
existing depth heap as well. The theorem follows ordered children and edges,
both probes, root filtering, fresh completion, canonical hits, smart finish,
and pending outcomes. `closed_language` and `closed_heap` derive the exact
closed result and the budget invariant from the empty cache.

`InternedGuardedBudgetStoredExecution.execute_checked` composes this law with
the actual stored replacement plan. `unfold_mu_checked` gives the exact smart
plan language of an actual returned Mu unfolding. `unfold_heaps` proves both
heaps after arbitrary stored outer unfolding. These are actual execution laws.
No callback-language or canonical-budget contract remains as a premise of the
closed source theorem.

## Completed comparison and next proof

`a7b5d94e` completes all four comparison steps. Literal root alternatives are
included at the same budget. Changes outside deep names contribute only root
alternatives. The unused smart body at the empty local supplies an upward
closed candidate. Retained Mu steps compare upward candidates. These laws use
the existing shape fields and complete actual captured records.

`InternedGuardedBudgetStoredRefinement.unfold_strict` combines raw plan decrease
with exact actual execution. Every accepted Mu term reaches its actual returned
unfolding at a strictly smaller budget. `9ca74b4d` proves cold/shared budget-heap
propagation, general final graph/table completeness, and general closed-source
reference Sized laws. `081ce3d1` proves native propagation and exact independent
returned-value table language. Read [cold budget completeness](notes-cold-budget-completeness.md).

The ordinary native product-row case is now proved. A live ranked Mu witness
refutes the general functional child-map adapter. Derive related physical
rows from actual execution for the remaining native two-input law. Read
[ordinary product rows](notes-ordinary-product-rows.md). Do not assume
product-language equivalence or force the refuted general literal field.

## Validation and preservation

Lean 4.34.1 passes 1,456 aggregate jobs and 43,803 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-cold-budget-exact-20261014-audit.log`.
All completed modules are imported by `MicroCFTA/Audit.lean`.
No production Haskell source changed. Earlier Nix and formatter evidence
remains applicable. No worker is active.

Snapshot: `/tmp/mcfta-smart-budget-execution-checkpoint-20261014-1758/`.
All 1,803 Lean-tree files are saved. All 1,789 previous files remain. Only audit
imports, two coverage ledgers, and the two previous current component notes
changed among those files. Every earlier proof and marked draft retains its bytes.
