# Exact smart budgets through actual source execution

Updated: 2026-10-14 17:58 CEST. Proofs: `50d79bef`, `35e07971`, `a76a22f1`.

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

## Remaining comparison and next proof

The raw compiler theorem and smart executor theorem now have different exact
reference languages. Prove inclusion from raw plan budgets into smart plan
budgets for the actual captured shapes and upward budget inputs. Do not assume
the law for arbitrary inconsistent shape/language inputs.

The unused smart branch needs a semantic law that separates root alternatives
from deep dependencies. For example, `mu x. union [x, leaf]` can lose its smart
binder step. Its self alternative occurs only at the root. Ordinary complete
free-name support still lists `x`; the existing shape also records that `x`
has no deep occurrence. Add semantic bounds for those existing fields. Do not
introduce another root/deep interpreter.

One possible proof requires these unproved steps:

1. Prove that the shape's literal root alternatives are included in the smart
   language at the same budget. Establish this for actual captured records.
2. Prove that changes outside the deep names can contribute only their literal
   root alternatives. Keep the already proved complete free-name support.
3. Use the smart body at an empty local as an upward closed candidate for the
   raw Mu when the local has no deep occurrence. A local root alternative is
   already in that candidate; unchanged external roots enter through step 1.
4. Use raw/smart body inclusion for retained Mu steps. The budgeted least
   definition quantifies only upward candidates, which can be used explicitly.

Then combine raw `unfold_plan_lower` with actual smart execution to obtain a
strictly smaller bound for the returned unfolding value. Propagate the new
budget probe heap through actual cold and native paths. Its source and stored
propagation are proved; cold/native propagation is not. Prove final repaired
graph/table completeness, then physical product readback and `product_exact`.

The primary node-count Sized sequence and both public term-rank inverses remain
proved at their recorded source-model boundaries. Mu-unfolding budgets are a
separate measure. General graph completeness is still open.

## Validation and preservation

Lean 4.34.1 passes 1,443 aggregate jobs and 43,730 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-smart-budget-execution-20261014-audit.log`.
All completed modules are imported by `MicroCFTA/Audit.lean`.
No production Haskell source changed. Earlier Nix and formatter evidence
remains applicable. No worker is active.

Snapshot: `/tmp/mcfta-smart-budget-execution-checkpoint-20261014-1758/`.
All 1,803 Lean-tree files are saved. All 1,789 previous files remain. Only audit
imports, two coverage ledgers, and the two previous current component notes
changed among those files. Every earlier proof and marked draft retains its bytes.
