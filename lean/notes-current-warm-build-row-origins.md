# Stored row origins through warm binder reuse

Proof checkpoint: `6478734b7f7aee02a36d809bf602c971d4b213e5`.
Starting checkpoint: `288f3ac27c609cad054b462856793997b6dc7efe`.
Imported main: `794903b3fbad3becb8b28736fc33463760731fc7`.
Evidence: `restart-evidence/20261021-warm-build-row-origins/`.

## Whole-library target

For every public operation, supported valid initial inputs must imply
termination and the intended result. Support must follow from initial
data and resources. It must not assume a future successful return.
Keep the optimized interned core and the older constructor and equality
targets. Construction, transforms, reduction, size classes, counts, ranks,
enumeration, generation, probability and external interfaces remain in scope.

## Current result

SourceCurrentNativeOriginalPublicationTrace now has two additive theorems.
build_trace_warm_writers takes an actual completed build and entry Context.
It returns one rooted issued Path. Every final full Mu cell is an exact
entry cell or a writer in that path. Every full Mu present before an indexed
publication completes is an entry cell or a writer at a smaller index.
Each writer keeps its full key and payload, missing cell, actual prefix,
three callback paths, and physical and issued suffixes.

build_trace_warm_target calls that theorem once. An actual missing entry
cell and final full cell select an indexed writer in the same returned path.
Full payload injection gives every component equality. The theorem retains
all generic clauses. It does not assign an independently recovered event
to an index in this path.

SourceCurrentWarmBuildRowOrigins.build_row_origins also consumes one actual
completed warm build and Context. It calls the warm trace producer once.
Its sites, final writers, precompletion writers and row origins share that
path. Strong induction on an indexed publication follows only new binder
cells at strictly smaller indices. It keeps the complete selected row.

RowOrigin retains a producer index at most the selected outer index.
The producer stays in the same path. Its raw callback, filter, Context,
Reached and actual SourceRow stay with the row. A nonunion terminal keeps
its actual SourceRow and completed build. It also keeps Context, Reached,
the exact input environment and a syntax bound relative to this producer.
UnionDescent retains the actual union route. Physical and issued growth
connect the callback entry to the terminal start. Suffixes connect its return
to the raw callback return, producer body return and selected outer body return.

The node alternative retains its actual ordered RowCall and complete
output-row equality. Source and canonical output indices can differ.
The capture alternative retains its active lexical Path, exact lookup,
original slot offset and same RowAt row. The prior-binder alternative retains
both actual probes, request, finish, full selected Mu payload, its stored row,
and that same full cell at build entry. It does not infer original source
ancestry for an arbitrary warm entry cell.

## Statement repairs

The first successful statement lacked the terminal's union descent.
An unrelated depth-probe node could satisfy its weaker receipt.
The next statement retained that route but lacked entry growth.
It proved prior cell presence without proving a hit at its returned cut.
The final joint terminal helper derives the route, prefix, exact environment
and suffix together. All earlier sources and successful checks remain.
The final selected sources are d702efba for the trace and ae6b1f3b for rows.

## Actual warm entry consumer

WarmBuildRowFixture.actual_warm_entry_row reuses the earlier source family.
It first builds a nested binder with a nullary tag17 row. It then builds
an outer binder over the union of its own reference and that nested binder.
The first completed build derives the exact warm heap and entry Context.
The outer target's key is absent at entry and its full cell is present at exit.

The consumer calls build_row_origins once and keeps every generic clause.
The returned final writer clause selects the target in that same path.
The actual missing entry cell excludes its initial alternative.
Finite source classification and replay exclude a new nested publication.
The same returned producer therefore has the outer body expression.
Its exact union descent excludes a node terminal. Empty original inputs
exclude a row-bearing capture. The returned terminal is the nested binder.

Actual path prefixes and the exported terminal prefix give growth to the
same returned binder's cut. The full entry cell supplies both its node table
and record lookup there. Its actual probes identify the key and full payload.
The same returned request is a warm hit and returns firstMu at that cut.
Its terminal stop equals its cut. No hidden event identity is assumed.

The example keeps the complete row, raw source, actual terminal and all
generic writer and row clauses. Its final source hash is
a01b57d6cdec60b9ee8e49837a5dbc42cdeca1d50e23555adbb86d7a30c43934.
The independent root strict check has an empty log. The full readback passes.
This is one new consumer of an existing source family. It adds no independent
source family, actual native execution prefix or actual unfold.

## Current validation

The selected independent root strict logs are empty. Canonical builds pass.
Complete public readbacks use all eight printer options and only standard
axioms. The latest default Audit passes 3542 jobs and 74348 dependencies.
Its only warning is the existing unused ClosedCompletion input.
The evidence retains every actual attempt, including the initial sandbox
launch failure, elaboration failures, successful weaker statements and
the successful warning-bearing intermediate check.
Each actual Lean job has a fresh usage check and a five-minute, 4 GiB cap.
The effective memory max and high are 4 GiB. Swap is zero.

## Remaining main proof

The largest gap is outer selected renewal and active cache key exclusion.
Native PhysicalTraceCompletion.initial_complete already proves finite
intersection from closed Original operands, an idle cache and WordRanges.
Original means complete interned-reference payload syntax. It can include
generated records. It does not mean original-program source ancestry.

The next concrete conjecture concerns one actual Parent-to-child dispatch
below an active owner with an empty inherited payload. If the returned child
has the owner's reference, prove that its actual descended inherited payload
is nonempty. Existing selected_split and node_key_ne_top then separate keys.
The missing implication concerns actual selected class edits and competing
sources. A supplied future rank or successful whole outer call is not enough.
Read the exact next-outer-key-plan.md in this evidence directory.

The recursive C1/C2 proposal in that plan is rejected as a copying route.
Its positive constrained Mu endpoints make the class primary gate true.
The actual scan then rejects or skips the class instead of selecting an edit.
No checked counterexample or Haskell runtime defect is claimed.

The warm source index is a finite provenance order within one completed build.
It is not a rank for future outer requests. Generated node and non-Mu capture
ancestry, self replacement, complete residual observations, final retention,
general outer completion, repeated-pass convergence and Haskell refinement
remain open. The whole-library goal stays active.

## Preservation

The original publication trace module keeps every earlier declaration exactly.
Its full previous source remains in warm-trace/publication-trace-before.lean.txt.
Its historical frozen hash checks that archive. The live module adds only the
two new theorems. All other older proof sources and frozen registry files keep
their bytes. The prior row statements remain in historical evidence packages.
All Haskell and active package files, stashes and other worktrees remain.
FINDINGS keeps the external repair registry first. No new Haskell repair or
runtime result is claimed.
