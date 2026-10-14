# General repaired unfolding rank and certified gate

Updated: 2026-10-15 00:47 CEST.
Proofs: `0871fb7a` and `40027d5f`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
Publish completed checkpoints on `formalize`.

## Prepared-plan retention

`InternedOccurrenceCostSupport` proves positive support of the complete pure
cost interpreter. Every interpreted cost names a free reference of the
interpreted shape. Shape coherence makes that result nonempty.
The proof includes empty-child edge deletion and both binder forms.

`InternedStoredCostInputs` describes the exact facts needed at prepared
lexical slots. Closed captures keep their empty test. References keep their
supplied costs. Fresh symbolic locals shadow the original binder name.
All supplied external names remain external under every later binder.
The proof does not require globally distinct original binder names.

`InternedStoredCostRetention.encode_retains` proves cost retention and
nonempty reconstruction together. Each supplied replacement occurrence
survives with at most its original number of enclosing Mu frames.
The child and edge inductions retain original order. Source live-edge
normalization proves that every sibling remains nonempty. A smart binder
can add at most one frame. Its symbolic local cannot capture an external
supplied occurrence. Closed source records remain original captured inputs.
Arbitrary open nested Mu and root unions with Mu members are included.

`InternedPreparedCostRetention` derives every lexical premise from source
availability, canonical slot lookup, actual input shapes, and actual costs.
The general theorem uses open replacements. The required unfolding instance
replaces the bound reference with the available open outer Mu. Every other
reference supplies its original zero-cost occurrence. Thus each external
original body occurrence survives at no greater prepared-plan cost.

## Actual source unfolding

`InternedFreshOrdinaryUnfoldRank.unfold_decreases` takes the original
minimum-cost witness. `mu_cost_iff` removes its outer frame. Prepared-plan
retention bounds the remaining occurrence. Exact actual execution costs
transfer that occurrence to the returned record. The returned minimum is
no greater than this witness, so actual unfolding strictly decreases rank.
This is a theorem about the returned value, not just the ordinary probe.

`unfold_complete_decreases` derives the finite actual call. It retains
context, depth heap, payload coverage, weighted heap, availability, growth,
and issued-name history for every later call. `closed_unfold_decreases`
derives these premises from original empty-cache source construction and
an actual stored open Mu. No shallow-body, marker, first-order, guarded-head,
or successful-unfold premise is supplied.

## Certified gate adapter and its limit

`InternedFreshOrdinaryGateRank.Node` retains the actual source cache and
semantic invariants. The view keeps original edge order and child order.
`step.actual` is the exact repaired unfolding equation and returned cache.
`read` observes cached depth, free-set emptiness, a supplied constraint
predicate, and that actual step. The concrete minimum-cost `ranking`
instantiates `ConstrainedRecursionGate.UnfoldingRank` without a supplied
decrease law. The constraint predicate is arbitrary and remains explicit.

`eventually_exact` gives finite instrumented evaluation equal to the total
decision at every finite path. Every larger fuel amount gives the same
decision. `source_eventually_exact` derives original construction completion
and the initial certified node. It assumes no completed construction call.

Each unfolding route retains its returned cache. Each child in the view
starts in the parent's cache. The adapter does not yet give an ordered
global trace that shares memo effects between sibling edge or path queries.
That source correspondence is the next target. Model ordered short circuit
with actual returned caches. Reuse the rank theorem in every retained cache.
Then derive full gate trace/readback, or state the exact memo observation law
needed to identify this route adapter with global shared memo execution.

The completed Sized reference, optimized, and solver-decided source-model
contracts remain unchanged. This rank is separate from a Sized term index.
The optimized interned core remains. Native containers, lazy scheduling,
primitive resources, external solver behavior, and verified Haskell extraction
retain their stated limits. The Lava paper method remains relevant prior art.
No translator or Rocq dependency was added.

## Validation and preservation

The pinned Lean 4.34.1 audit passes 1,585 jobs and checks 44,758 theorem
dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`.
Only the old unused `inputs` warning remains. Log:
`/tmp/mcfta-general-open-unfold-rank-20261015-audit.log`.
No production Haskell code changed. Existing proof bytes are unchanged,
except for the six audit imports. All counterexamples and marked drafts
remain. Snapshot:
`/tmp/mcfta-general-unfold-rank-checkpoint-20261015-0047/`.
It saves all 1,967 Lean-tree files and four root documents.
