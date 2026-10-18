# Current system claim

Checked against the live theorem statements on 2026-10-18.
The causal writer and original-reader fragment proof checkpoint is `f312f254`.

In simple technical English: a completed modeled reduction adds no tree
outside the input language. It retains every input tree that satisfies its
inherited constraints. Its initial cache, guard and resource assumptions remain
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

Causal filtered Empty agreement is now proved for all source syntax.
Every pair in the recursive Generated relation has equal Empty flags.
Historical node calls derive local simulation in both directions with
full guards and ordered mutual child generators. Selected Mu readback
constructs both calls under arbitrary common replacements.

Actual selected Mu reconstruction now derives both body/probe source
generators under arbitrary common outer and local replacements. It retains
complete issued paths, both actual epsilon endpoints and final warm calls.
These are generator memberships at the explicit produced reader. They do
not assert guarded observation equality.

An actual warm union parent now supplies indexed literal-atom calls and
full original RowCalls at the original reader. Whole subgroup calls can
still allocate. A source-built case checks that behavior. The earlier
conditional union theorem remains a later-reader result. Neither theorem
establishes the full source Law for all syntax.

A sound normalization rule permits literal inclusion before and after
at most one source pair. It requires the genuine full literal clauses
for that source relation. Arbitrary chains of source pairs remain excluded.

The main current gap is the complete source-generated guarded simulation.
The used-Mu clause must match actual unfolding with a reached related
endpoint at the same supported reader. Variables need the mutual
Generated/Inputs semantic induction hypothesis. A separate checked actual
construction rules out arbitrary weak simulation up to transitive closure.
Causal Ready and physical Empty agreement do not repair that rule.
A justified progress argument or stronger semantic induction is required.
This counterexample does not concern the actual Generated relation.
The recursive guard certificate must follow from supported public construction.

General completion still needs active-owner exclusion, fresh-call bounds,
and repeated-pass convergence. Haskell correspondence still needs demand
and cache behavior, machine-integer adequacy, and the external interfaces.

Original root filtering tests bare references before substitution.
Equal assigned profiles alone do not preserve that test. The stronger
root contract is now derived for every stored recursive payload in an
actual modeled history. Its proof covers retained open Mu, unused binders
and earlier cache winners. See `notes-current-causal-source-comparison.md`
for the original payload proof. See `notes-current-causal-empty-fusion.md`
for causal Empty agreement and the guarded node clause. See
`notes-current-causal-union-local.md` for conditional union clauses and
the earlier fixed-reader and progress obligations. See
`notes-current-causal-writer-generators.md` for actual selected-writer
generators, original-reader fragment calls and sound restricted normalization.
The broad reduction guarantee above has not changed.

No Haskell bytes change in this checkpoint. Root `FINDINGS.md` retains the
external repair registry first. The full-library goal remains active.
