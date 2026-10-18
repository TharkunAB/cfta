# Current system claim

Checked against the live theorem statements on 2026-10-18.
The root-deletion proof checkpoint is `2e24eca5`.

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

The main current gap is general recursive source comparison. Each actual
cache publication must establish the semantic facts used by later hits.
The recursive guard certificate must also follow from supported public
construction. It must not remain an unexplained initial assumption.

General completion still needs active-owner exclusion, fresh-call bounds,
and repeated-pass convergence. Haskell correspondence still needs demand
and cache behavior, machine-integer adequacy, and the external interfaces.

Original root filtering tests bare references before substitution.
Equal assigned profiles alone do not preserve that test. The checked
stronger root contract retains it. A separate causal route now derives
actual smart-unused deletion from a later reader's history, without an
assumed payload contract. The remaining source induction must also cover
retained open Mu and establish each actual publication's payload law.
See `notes-current-root-deletion-observations.md` for checked evidence and
the next proof step. The broad guarantee above has not changed.

No Haskell bytes change in this checkpoint. Root `FINDINGS.md` retains the
external repair registry first. The full-library goal remains active.
