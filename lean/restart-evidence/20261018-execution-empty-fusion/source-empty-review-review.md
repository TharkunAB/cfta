# Independent review of source Empty abstraction

Date: 2026-10-18 15:17 CEST.

Reviewed final production:
`lean/MicroCFTA/SourceCurrentSourceEmptyAbstraction.lean`.
SHA-256:
`2f2c46b72904bb0f374e25fb9b0c8b4febabe1f5eb222781346145c50153693f`.

No material mathematical or contract issue was found. The complete source
and both final full public printouts were inspected. No Lean check was run
for this review. Both public pairs are reused evidence.

## Projection and binder case

`project` sends an ignored external root to an opaque nonempty profile.
It does not delete the root. This distinction preserves the Empty test.
For example, deleting the external root in `mu x. z` would create a false
Empty result. The current projection retains a nonempty alternative.

`lift` retains the new symbolic local. Each repeated lift also retains the
earlier symbolic locals. `project_map` and `project_local` retain the exact
lexical environment under a new binder. `lower_any` and `lower_names` state
the two list equations needed to remove only the local on binder exit.
`project_lower` uses these equations with the actual Boolean conditional.
It does not assume an output relation.

The direct-3 rewrite failure is preserved in the reviewed evidence. The
printed expression did not expose its matching failure. This review makes
no unsupported claim about a Lean elaborator defect or a hidden type
mismatch. The final repair applies `congrArg` to the full conditional
context and then uses `lower_names` in its selected branch. This is the
same Boolean equality and the same function as the intended rewrite.
The checked final proof resolves the issue without a stronger premise.

## Source induction and actual calls

The mutual interpretation proof follows empty, variable, node, union and
both binder forms. Node survival uses only ordered child Empty tests. The
union case preserves opacity and root alternatives. The smart binder case
retains fresh locals until its own lowering step. Raw binders remain opaque.

`same_empty` projects all external names into one empty atom type. Equal
ordered lexical Empty flags give exactly equal projected environments.
The theorem compares one complete source expression. It does not compare
the encoded plans of two different stored values.

`source` applies the existing repaired profile theorem to both actual
source executions. It derives each returned context and availability fact
from the corresponding initial context and actual call. Normalization
then relates the physical Empty test to the returned profile. No final
context, output Empty agreement, writer law, supplied graph or future
completion premise is hidden in this argument. The two initial and final
heaps may differ. Actual completion remains an explicit equation.

The result permits arbitrary source syntax and available captures. It does
not impose BinderFree, finite Cap, closure or absence of a local variable.
It does not prove source/filter/stored fusion, general Generated Empty
agreement, equality of records, language inhabitation or outer completion.

## Reused validation

- `source-empty-direct-6`: exit 0; log 0 bytes; source equals final production.
- `source-empty-canonical-1`: exit 0; warning-free 267-job build.
- `source-empty-public-1`: two full signature/proof/axiom triples; all eight
  explicit options; only `propext`, `Classical.choice` and `Quot.sound`.

Public snapshot SHA-256:
`9bb88ab43287cf95f3f51ee4bed49f70de9d3da46e68eecda53897d5083417a1`.
The effective resource readbacks are 4294967296-byte MemoryMax and
MemoryHigh, with zero MemorySwapMax. Each reused run has the pinned Lean
4.34.1 command and a five-minute limit. No constructed fixture is included
in this review. The existing stored-empty component remains unchanged.
