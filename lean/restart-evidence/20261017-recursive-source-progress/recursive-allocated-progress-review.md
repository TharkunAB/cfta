# Current allocated recursive-query progress

Reviewed on 2026-10-17 at 00:31 CEST. Production sources were read only.

The current allocated engine already constructs complete native queries on
closed original Mu inputs, conditional on reached machine-word checks. It
does not need a future-completion oracle for those inputs. The next missing
initial-resource theorem is a word-capacity bound for the actual recursive
checked program. General constrained outer reduction remains a separate
termination problem.

## The existing initialization route

`InternedFreshOrdinaryConstruction.build` is not restricted to the finite
ordinary domain. Its binder branch at lines 107–112 executes the Depth probe,
the selected ordinary probe, and the real constructor request. Its name must
not be used to infer that Mu construction is excluded. General constructor
completion is not a theorem of this module: a successful actual build is
still an explicit premise of the following initialization endpoints.

`SourceCurrentAllocatedNativeOriginalHistory.constructed`, lines 125–149,
takes a covered equality-allocation History, valid initial interner, and
that actual build. It derives current allocated Good, SemanticReady,
availability, closedness, and Original syntax. The physical state has cold
native tables and the actual final equality cache.

`SourceCurrentAllocatedPartialInitialization.constructed`, lines 105–142,
also works for this generic actual build. It derives the full initial caller
Context, exact allocated empty inherited value, computed singleton inventory,
and empty global tables. `NativeInventoryState.initial`, lines 74–82,
derives contextual and coverage laws for the cold native tables.

There are two existing query routes from these facts:

- `NativeConstructedHistory.query_complete`, lines 25–52, and
  `NativePreparedHistory.query_complete`, lines 25–59, construct exact serial
  current checked executions. Closed resident operands derive Original and
  the finite input model. Preparation derives the actual covered field
  history. Their remaining execution premise is WordRanges for that exact
  checked program. They do not take a completed query or future law.
- `AllocatedTargetQuery.finite`, lines 78–99, consumes current Ready and
  inventory At, closed resident operands, WordRanges, and initial global
  validity. It constructs the actual physical Step, computed next inventory,
  full Ready/At, effects, extension, closed resident result, exact independent
  intersection language, and the same global bundle. There is no finite
  ordinary domain premise. `NativeInventoryState.query_complete`, lines
  85–108, can also grow the inventory for later generated closed operands.

Thus an initialization-to-current-Step adapter can already be proved by
composition. It must retain the actual initialization cache and operations;
it need not assume all initial facts individually. Such an adapter would
still have explicit WordRanges unless the next resource theorem is proved.

## Why recursive completion is not circular

`SourceRecursiveIntersectionInputExact.source_schedule_total`, lines
100–120, derives a successful finite semantic schedule from actual original
closed resident records. `RequestProgress.initial_complete`, lines 77–89,
packages that derived result as Completes. It is not a caller premise.
`RequestProgress.physical_child_requiredFuel` and `entered_requiredFuel`,
lines 33–74, transfer the strictly smaller semantic measure to the actual
selected child and canonical allocated domain.

`NativePhysicalTraceCompletion.initial_complete`, lines 535–557, constructs
the current checked physical Trace using that derived measure and initial
Idle. The contextual completion at lines 606–639 derives the corresponding
same-return semantic law and Idle state. Internal local Mu combinators take
child certificates, but the closed initial endpoints discharge them by this
induction. They do not expose those certificates as future-query inputs.

The actual recursive code is explicit. `SourceRecursiveIntersectionCompile`
at lines 28–43 compiles Mu as enter, child node request on the actual bodies,
then optionalBinder. Reference dispatch reads the source binding before its
next request. `NativeMuSource.enter_prefix`, lines 20–37, gives the exact
current checked transition and retained operation state. Repeated-pair
cutoff and its placeholder are separate source branches. This is stronger
than returning an opaque Mu unchanged in the outer caller.

## The remaining initial-resource bridge

`NativeRequestBounds.WordRanges`, lines 125–136, quantifies every actual
yielded checked prefix. It checks the reached request words; it does not
assume a completed query. The initialization/history endpoints still take
this universal prefix property explicitly.

The completed finite ordinary resource proof cannot be applied to Mu:

- `FiniteOrdinaryNativeProfile.NodeShape`, lines 19–22, is false on Mu,
  references, and union inputs.
- `NativeBudgetCompile.NodeInputs`, lines 25–29, also fixes emptyDomain.
- `NativeBudgetCode.Bound`, lines 27–37, is false on enter, read, and
  optionalBinder instructions.
- `ActualNativeWork.counted`, lines 218–261, accepts a supplied actual Step
  and finite ordinary input profiles. It counts that accepted trace. It
  does not construct a recursive trace or derive recursive WordRanges.

The smallest substantive next resource module is a new
`SourceCurrentAllocatedRecursiveQueryCapacity` with this endpoint shape:

```text
ranges : actual covered constructor history/build
       -> current initial Good/SemanticReady or their derived initialization
       -> closed resident query operands
       -> initial node, edge, and shifted-domain supplies
          for explicit budgets computed from those source operands
       -> NativeRequestBounds.WordRanges
            (.code (requestNode emptyDomain left right)) initialChecked
```

It must derive its semantic completion measure through
`RequestProgress.initial_complete`. Completes, a successful physical query,
future output profiles, and future capacities must not be public inputs.
The potential must cover actual enter/read/optionalBinder instructions,
actual field allocations, and constructor work from binder reconstruction.
The domain supply is additional to the two ordinary constructor supplies.
`IntersectionEmptyDomain.make` reserves zero and shifts nonempty raw domain
IDs by one. Current node and edge KeySafe require
`domain.identity < 2^(width-1)`, not merely an unsigned full-period bound.
The older `NativeCapacity.Capacity` at lines 17–20 demonstrates this third
resource, but its execution theorem is not yet the current checked bridge.

The noncircular proof order is: derive the finite source inventory and
semantic measure; prove input-only recursive resource bounds and all actual
checked-prefix word checks; then call the existing allocated finite query
constructor. Count domain entry and optional-binder work before using the
resulting word plan. A theorem that first assumes the current query's
completed trace or a final resource certificate would not close this gap.

## A concrete branch witness for the next proof

Use two distinct closed recursive operands, for example
`mu X. (f(X) + a())` and `mu Y. (f(Y) + b())`, with `a != b` and a common
recursive `f` row. Construct both in one actual source heap. The unequal
operands avoid the closed-self shortcut. Check the actual sorted request
selects a Mu branch, enters a nonempty domain, follows an interned reference,
uses the repeated-pair cutoff, and completes optionalBinder. The complete
query must use `SourceEqualityNativeDemand` and its actual operations cache.

The first bounded witness may prove WordRanges by an explicit finite
checked-prefix argument for those concrete inputs. It must construct the
build and query itself. An opaque outer Mu return, a self-intersection, or
only an assumed child trace would not exercise this route. This example is
a proposed proof target, not a claimed established execution in this audit.

## Historical native endpoints

`SourceRecursiveIntersectionNative.constructed_node_table_exact`, lines
73–104, has no futureComplete premise, but it still takes historical native
WordRanges. Its interpreter uses explicit pure emptyGuard/conjoin arguments
and an unallocated native state. The current interpreter carries checked
operations, a separate edgeBody control, actual field lookup and allocated
conjunction, and the resulting operation histories. Historical Strong Valid
and current physical Good are also different invariants.

There is no direct state projection that turns that older theorem into the
current full checked execution. Reuse the established source-schedule and
semantic measure lemmas through current allocated completion. Do not replace
its operation effects or word checks with an old completed native receipt.

## Verified scope

`recursive-allocated-progress-public.lean` independently checks eleven exact
public axiom/signature pairs, including current initialization, recursive
completion, current query, finite ordinary Work, and the older endpoint.
The strict pinned Lean invocation passed in
`recursive-allocated-progress-public-1.log` with no error, warning, or
`sorryAx`. No production module or proof scope was changed.

The established result is general closed recursive native completion under
explicit current WordRanges and legitimate entry facts. Initial-only
recursive resource admission, general constrained outer reduction,
fixpoint termination, and concrete runtime demand correspondence remain
open. Finite ordinary initial-resource root completion remains established.
