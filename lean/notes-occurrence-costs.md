# General occurrence costs in repaired source execution

Updated: 2026-10-15 00:33 CEST.
Proofs: `efa2e558` and `d17e644b`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
Publish checkpoints on `formalize`.

## Exact source correspondence

`InternedOccurrenceCostSemantics` reuses the existing shape interpretation.
Shapes decide empty-child deletion and smart binder retention. A separate
ordered list records each free reference and its Mu cost. A retained Mu
adds one. Constructors and unions add zero. A binder removes its local.
External renaming commutes with the complete nested interpretation.
Supplying a literal callback argument gives the same captured costs for
every other name. These laws include arbitrary nested source syntax.

The actual correspondence compares membership of `(reference, cost)` pairs.
It does not compare occurrence multiplicities or canonical list order.
This is the information needed by the minimum free-occurrence measure.
That measure is an unfolding rank candidate, not a Sized term index.

`InternedFreshOrdinaryCostHeap.Correct` retains the actual local normal form.
It equates external body costs with ordinary-probe costs after each excludes
its own supplied name. The actual Depth probe proves ordinary-name freshness.
Actual reservation provenance proves fresh-identity absence.
`finish_costs` includes raw retention, unused smart cleanup, direct self,
and used smart retention. `hit_costs` uses exact immutable requested probes.

`InternedFreshOrdinaryCostExecutionFacts` proves source node, union, and
callback composition. `InternedFreshOrdinaryCostComposition` identifies the
actual decoded binder costs with the pure interpretation. The existing deep
observations select smart retention. `InternedFreshOrdinaryCostRequest`
follows hits, pending slots, reservation, and actual fresh callback completion.
Its recursive observations are discharged by the full syntax induction.

`InternedFreshOrdinaryCosts.build_costs` derives the returned cost membership
and preserves every complete stored cost record. The mutual proof covers
original child order, edge effects, all nested binders, both probes, and
fresh bodies. It supplies no whole-callback cost law or final cost heap.
`closed_heap` derives the invariant from empty captures and empty caches.
The heap statement also covers a pending outer outcome.

`closed_external_cost` proves exact external body/ordinary cost agreement for
every stored Mu in that actual source cache. `closed_predecessor` gives each
free Mu occurrence its exact predecessor in the ordinary probe.
`closed_probe_rank` proves a strictly smaller minimum free-occurrence rank
for that probe when the Mu is open. These statements have no binder-free,
first-order, shallow-body, or opaque-probe restriction.

## Actual stored execution

`InternedFreshOrdinaryStoredCosts` extends the repaired stored executor.
`preparedCosts` interprets its original `encode` plan with its actual
replacement inputs. `execute_costs` proves exact output cost membership and
preserves the weighted heap. `execute_complete_costs` derives the finite
actual call and retains context, depth heap, coverage, weighted heap,
availability, growth, and issued-name history. `unfold_complete_costs`
retains these caches for later actual unfoldings.

Original source construction derives the new weighted heap through
`closed_heap`. The prepared cost equality is not yet a comparison with the
original body's costs.

## Remaining general gate rank

The next target is a pure prepared-plan retention bound. Let `outer` be an
available open Mu with bound reference `own` and actual stored `body`. For each
`(name, cost)` in `costs body` with `name != own`, prove that some
`(name, after)` with `after <= cost` occurs in
`preparedCosts body (fun reference => if reference = own then some outer else none)`.

The bound must include arbitrary open nested Mu and root unions with Mu
members. A nonempty reconstruction lemma may be needed to keep every original
live edge available. Closed stored leaves remain exact inputs. Original free
references use the actual replacements. Fresh symbolic locals must preserve
lexical shadowing. Reuse stored slot lookup, scope, and original live-edge
invariants. Derive their premises from the source context.

Combine that bound with `execute_complete_costs`, the original minimum-cost
witness, and `mu_cost_iff` to prove strict decrease for actual repaired
unfolding. Retain the returned weighted heap through every later call.
Then instantiate the general constrained-recursion gate rank.
Do not substitute the probe's strict rank for the actual unfolding rank.
Do not use the closed-node dynamic Mu budget for an open Mu.

## Validation and preservation

The pinned Lean 4.34.1 audit passes 1,577 jobs and checks 44,674 theorem
dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`.
Log: `/tmp/mcfta-general-fresh-occurrence-costs-20261015-audit.log`.
Only the old unused `inputs` warning remains. No production Haskell code
changed. Earlier proof files are unchanged except for audit imports.
Every retained counterexample and marked draft remains.
Snapshot: `/tmp/mcfta-general-fresh-costs-checkpoint-20261015-0034/`.
It saves all 1,960 Lean-tree files and four root documents.

The Sized reference, optimized, and solver-decided paths retain their completed
source-model contracts. Native containers, lazy scheduling, primitive resources,
external solver behavior, and verified Haskell extraction retain their limits.
