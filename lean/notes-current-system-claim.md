# Current system claim

Checked against the live theorem statements on 2026-10-18.
The causal source comparison proof checkpoint is `43859cfd`.

In simple technical English: a completed modeled reduction adds no tree
outside the input language. It retains every input tree that satisfies its inherited
constraints. Its initial cache, guard and resource assumptions remain
explicit. A returned size-query API has exact enumeration, counts and
rank/unrank laws under its separate construction assumptions.

## Broad reduction guarantee

A completed bounded call in the checked Lean model adds no accepted finite
tree. It retains every input tree that satisfies the inherited constraints.
The theorem assumes the initial semantic cache facts, recursive guard
certificate, resident inputs, and computed resource bounds.

For each ambient reference interpretation, the exact statement is:

`L(input) ∩ Sat(inherited) ⊆ L(result) ⊆ L(input)`.

The source is `SourceCurrentAllocatedPartialMemoSound.NodeLaw` at line 29.
`SourceCurrentOuterInitialActual.node_call` at line 432 derives that law
from actual completed modeled execution under the stated assumptions.

Empty inherited constraints give exact input and output languages.
The law does not prove that every returned tree satisfies the inherited
constraints. A contradictory inherited payload makes the preservation
premise false. It does not imply an Empty result from this theorem.

## Stronger result for size queries

Actual closed modeled construction with valid annotations derives the
internal assumptions for both reference and optimized size query paths.
Both paths finish with the same result and final cache.
If that result contains a query API, its size classes contain exactly the
accepted trees of each node count. They contain no duplicate tree.
Counts agree with the classes. Rank and unrank are inverse operations.
Enumeration prefixes contain exactly the accepted trees through the bound
and use nondecreasing node-count order.

The sources are `SourceFreshOrdinarySizedEntry.constructed_complete` in
`SourceFreshOrdinarySizedEntryCorrect.lean` at line 113 and
`SourceSizedApiLaws.Exact` at line 15. Valid annotations and a completed
original construction remain premises. The theorem retains errors.
It does not assert that every input returns a query API.

## Whole-library target and missing work

The target remains correctness of the whole library against its intended
semantics. Constructor language, constraint reduction, exact size classes,
counts, ranks, enumeration, probability, finite execution, and Haskell
correspondence remain separate contracts. A checked component does not
establish the full target.

General source comparison is now proved for assigned root profiles and
original root deletion. Actual histories from empty tables derive the
body/probe payload contract and its stronger original-root interface.
No semantic payload heap is supplied to those history-based endpoints.

The main current gap is deeper recursive guarded observation agreement.
It must match actual Mu unfolding, full row guards and ordered children.
The recursive guard certificate must follow from supported public
construction. Root-profile equality alone does not establish it.

General completion still needs active-owner exclusion, fresh-call bounds,
and repeated-pass convergence. Haskell correspondence still needs demand
and cache behavior, machine-integer adequacy, and the external interfaces.

Original root filtering tests bare references before substitution.
Equal assigned profiles alone do not preserve that test. The stronger
root contract is now derived for every stored recursive payload in an
actual modeled history. Its proof covers retained open Mu, unused binders
and earlier cache winners. See `notes-current-causal-source-comparison.md`
for checked evidence and the next causal Empty and deeper observation
steps. The broad reduction guarantee above has not changed.

No Haskell bytes change in this checkpoint. Root `FINDINGS.md` retains the
external repair registry first. The full-library goal remains active.
