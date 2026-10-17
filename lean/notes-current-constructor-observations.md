# Physical empty agreement and actual parent construction

Checked at proof commit `17b9e2fe`. Starting checkpoint is `dc9504dc`.
Source main remains `c0cc8a05`, merged at `896b0a1c`.
The whole-library objective remains active. No Haskell behavior changes.

## Completed results

`SourceCurrentStoredUnionSurvival.initial` strengthens the preceding union
reconstruction theorem. Initial Ready, available originals, and available
replacements construct both operation orders in one growing cache. The
theorem retains all actual intermediate heaps, four Keeps facts, and both
final available results. The results agree on physical emptiness and have
the same open observations at every finite depth and every fixed view.
No future return or output relation is an input.

`SourceCurrentOpenObservationSurvival.Related` records exactly those two
properties. Its node theorem derives matching row survival from the
original related rows. Full symbols and guards remain equal. Children
remain ordered. The caller does not supply a relation on the surviving
rows. Its union theorem preserves Related for ordered related inputs.
These theorems cover ordinary node and union constructors. They do not
claim congruence for root self filtering or recursive binders.

`SourceCurrentRelatedParentConstruction.complete` constructs both parents
from initial Ready, available child lists, and Related children. It executes
the first edge and node, then the second edge and node. It retains all four
run pairs and Keeps facts. Both edges have the requested symbol, full guard,
and original ordered children. Both parents remain available at the final
heap, and the parents are Related.

The parent integration starts from the actual source that produces the
physically unequal `union[A, B, z]` and `union[AB, z]` results. It applies the
new initial theorem, then constructs both actual parents. It supplies no
future return, ready heap, or child relation.

## How physical emptiness is derived

`SourceCurrentOrdinaryObservationEmpty` uses Normal.proper to show that an
available ordinary node has at least one row. For ordinary roots, one level
of matching observations therefore determines physical emptiness. This
argument excludes Mu roots. The actual warm ordinary union theorem derives
all returned availability and ordinary shapes from the completed calls.

`SourceCurrentStoredUnionEmpty` treats closed and open stored unions.
Closed calls retain their exact original members. Proper resident unions
have a nonempty member. Open calls expose the actual ordered member calls
and final makeUnion. The existing exact makeUnion empty theorem then gives
the result. The flattening theorem derives the same all-empty test for the
actual flattened member returns.

The final proof handles empty, singleton, ordinary merge, and retained union
selection directly. Coherence retains complete values through distinctNodes.
Actual replay aligns every call at the final heap. No step infers physical
emptiness from unrestricted observations of Mu values.

## Checked filter boundary

Related is insufficient for root self filtering, even with equal aggregate
metadata. A checked source constructs ordinary values A(a) and B(a), a closed
unused raw Mu(empty), and an open unused raw Mu(a). Let AB be the ordinary
merge of A and B. It then constructs these values in sequence:

- x = union[a, A(a), B(a), Mu(empty)].
- y = union[Mu(a), AB, Mu(empty)].

The values satisfy the exact new Related predicate. Both are physically
nonempty and neither is a bare reference. Their free-name lists, deep-name
lists, and cached depths are equal. The actual root filter removes the
literal a member from x. It retains the Mu(a) member of y. The filtered
results already differ in reference observations at depth zero.

This counterexample excludes aggregate observations and metadata as a
sufficient binder-filter relation. The next relation must retain the
provenance of literal immediate union members. The counterexample does
not compare the body and ordinary probe of one selected writer. It does
not establish a Haskell defect.

A second checked source compares smart construction of
`binder true (union [binder false empty, var 0])` and
`binder true (var 0)`. The first build creates a Ready heap. Its actual warm
replay and the second build then start at that same heap. Their returns are
the raw Mu(empty) and Empty. They have the same observations at every depth
and view but differ in physical emptiness. At that common starting heap,
both raw body builds complete with Related results for every available
reference. This premise concerns that heap. No relation at every future
callback heap is asserted. This also compares different source expressions,
not the body and ordinary probe of one selected writer.

## Remaining work

Derive the actual retained-Mu body and ordinary-probe relation from causal
selected writers. The union producer now provides physical empty agreement,
and actual ordinary parent construction preserves it. Root self filtering,
smart cleanup, nested binders, and earlier warm winners still need adequate
literal member and child correspondence. Derive actual growth and issued
reference history; four-table growth alone is insufficient.

General recursive outer progress, full mutual completion, repeated-pass
convergence, current frontend/runtime adapters, and complete public Haskell
correspondence also remain open. Keep the full objective.

## Validation

All five new strict source logs are empty. All canonical builds pass.
All eleven public declarations have explicit full signatures, proofs, and
axiom reports. The full pinned Audit passes 3119 jobs and 68380 dependency
checks. Effective MemoryMax and MemoryHigh are 4 GiB, swap is zero, and
peak memory is 378 MiB. The old unused-variable warning in unchanged
InternedFreshOrdinaryClosedCompletion remains in the Audit log.

Selected constructed checks cover empty ordinary results, closed and open
stored unions, the unequal normalization results, actual parents, and the
filter boundary. Only propext, Classical.choice, and Quot.sound occur in
selected axiom reports. Exact selections and failed attempts are retained
in `restart-evidence/20261017-constructor-observations/`.

All earlier sources and artifacts remain preserved. No Haskell files change.
Root FINDINGS retains the external repair registry first, including merged
field-pool repair b9219b9e. Record every later Haskell repair with its failure,
reproducer, paths, commit, validation, and upstream status.
