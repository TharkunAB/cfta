# Next target: literal local reduction and the outer caller

Source main is `5399d310`. The twelve new seeded, gate, and Scan modules are
canonical-green. The root reports an Audit of 2456 jobs and 58268 dependency
checks. This note ran no builds and changed no proof or Haskell source.

The full objective remains the whole library: independent mathematical
specifications, proofs for the algorithms and public APIs, and explicit
correspondence to the current implementation. This next target connects the
literal current local reducer and parent edge to the existing eight-family
outer caller graph. It does not replace the remaining runtime, solver,
frontend, or Sized obligations.

## Established components to reuse

All module names below are under `lean/MicroCFTA/`.

| Component | Exact reuse |
| --- | --- |
| Literal refused query | `SourceCurrentAllocatedSeededWorker.seeded p h n values paths before`; Completion.`seeded_complete`; Stability.`seeded_done_unique`; Sound.`seeded_sound`; WorkerActual.`verified` and `.finite` |
| Literal current gates | `SourceCurrentAllocatedGateWorker.primary` and `.secondary`; `primary_complete`, `secondary_complete`, successful stability/uniqueness, and strict primary reads |
| Literal current Scan | `SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes before fourth`; Completion.`scan_complete` and `.scan_uniform`; Stability.`scan_done_unique`; WorkerActual.`sound`, `.verified`, and `.finite` |
| Warm allocated precheck | `SourceCurrentAllocatedPrecheck.state`, `.loaded_complete`, `.complete`, `.resident_complete`, `Receipt.classes`, and `Receipt.classes_exact` (`:29–32`, `:66`, `:95`, `:106`, `:186`, `:200`) |
| Required children | `SourceEqualityRequiredExecution.requireAll fuel readFuel paths values heap` (`:109`); execution equivalence (`:131`); `SourceCurrentConjunctionRequired.Receipt.stable` and `.scan_required_complete` (`:107`, `:170`); `SourceCurrentConjunctionRequiredActual.verified` (`:40`) |
| Literal checked class pass | `SourceCurrentAllocatedClassWorker.pass e p h m c n records values checked merge`; Completion.`pass_complete`; Stability and WorkerActual.`verified`, `.caller`, `.caller_finite` (`WorkerActual:65`, `:91`, `:117`) |
| One relational Scan plus continuation | `SourceCurrentConjunctionScanClassPass.Reduction`, `.Ranges`; use **Actual**.`Reads`, `.verified`, `.from_scan`, `.finite` for strict current primary reads (`Actual:37`, `:105`, `:190`, `:253`) |
| Local relational reduction | `SourceCurrentAllocatedLocalReduction.Reduction` and `.Ranges`; **Actual**.`prefix_verified`, `.verified`, `.finite` (`Actual:82`, `:111`, `:173`) |
| Parent edge | `SourceCurrentAllocatedParentEdge.Edge`; **Actual**.`verified` and `.finite` (`Actual:64`, `:132`); `SourceCurrentAllocatedMkEdge.reject_correct`, `.finite`, and `Receipt.language` (`:163`, `:109`, `:188`) |
| Completed mutual caller | `SourceCurrentAllocatedPartialGraph` eight families; strict `PartialSourceReads`; `PartialActual.node_call` through `.walk` and `.root_exact` (`:228–280`); `PartialFrames` and `PartialCallSteps` protect both result families |

The current local module is named `SourceCurrentAllocatedLocalReduction`.
There is no `SourceCurrentAllocatedPartialReduction.lean` file to import.
Seeded execution and Scan execution are established components. Their
literal worker soundness is no longer the next missing step.

## Source branches that the new literal layer must retain

`cfta/src/Data/CFTA/Equality/Operations.hs:194–241` defines the local pass:

1. `go EmptyConstraints EmptyConstraints origNs` returns `origNs`.
2. A contradictory actual local/inherited combination erases the original
   child slots. It skips Scan and class editing.
3. `unsafeSubsumptionOrderedEclasses ecs` supplies the actual original class
   records. Primary true refuses a class; primary false selects it.
4. For a refused class, secondary true skips its query. Secondary false runs
   the first-seeded intersection, then the current `provablyEmpty` decision.
   A true decision erases the original children and skips the suffix and
   class continuation. False permits continuation; it proves no acceptance.
5. A successful Scan requires the union of selected original paths on
   **origNs**, at the actual Scan-return heap. It then executes
   `foldr reduceEClass withNeededChildren eclasses`, followed by final empty
   propagation. This is one pass, not an internal fixpoint.

`reduceEClass` captures the forest at that class's actual entry. It walks
the class paths in ascending order. Each target excludes its own path,
projects the other paths, merges each projection, and intersects their
first-seeded list. The class right fold executes its tail before its head.
Only class-local target slots reset. Merge, native, fourth, global, equality,
and outer result tables remain warm.

At `Operations.hs:156–167`, `reduceEdgeIntersection` runs the local reducer
and `mkEdge`. At `:80–98`, an ordinary outer node maps each row in this order:
edge reduction, inherited descendants of the **returned edge**, then the
next row. At `:143–145`, inherited contradiction skips child calls; live
children receive the actual indexed `eqConstraintsDescend` payload.
Empty, Mu, and union branches retain their existing source behavior.
The `Rec` branch is an explicit error (`:91`).

These are completed serial schedules. They do not prove GHC forcing order,
lazy CAF evaluation, pending publication, or concrete global-table events.

## First additive implementation

First add a record-indexed Scan wrapper. The frozen Scan worker returns
selected **paths**, while ClassWorker needs the original `Record` values.
Use the exact same literal stage functions, retain original records or
positions as branches return, and prove path-projection agreement with the
frozen worker. `SelectedRecords.retained_records` is a proof-side existential,
not an executable selector. Each reached gate/query runs once. Use a pure
subsequence-recovery alternative only if existing precheck uniqueness and
canonical-trie facts genuinely prove its agreement with `Retained`.
Do not use `Classical.choose`, gate replay, or membership-set filtering.

Add a literal local worker and its completion/stability/Actual adapters.
Keep the established component fuel tuples visible. Combine sufficient
bounds by maxima only after the actual stage return is fixed. The
conjunction budget remains a separate fixed input.

- Execute `SourceEqualityPartialPrecheckAllocation.run` once. Use its actual
  returned operations through `Precheck.state`. Preserve the current native
  state and constructor heap. Propagate a real error with its reached
  operation state. Do not reset operations or replace an error with a branch.
- For `.unchanged` and `.emptyChildren`, return at that prefix state. For
  `.classes records`, call the literal current Scan on `records.map paths`.
- On a stop, erase the original child list at the literal Scan return.
  On success, retain the actual selected records, run literal `requireAll`,
  advance the full checked state with its returned heap, then call the
  existing literal `ClassWorker.pass` on the required forest and warm merge.
- Preserve each exact phase failure, full checked state, fourth memo, and
  merge. A failed class worker also carries its reached shared state and
  local target slots. Do not discard that diagnostic state.

Then prove finite relational local graphs give stable literal bounds. For
supplied literal success, construct the legitimate finite relational return
and align through unconditional whole-return uniqueness. Reuse
`LocalReductionActual.verified` and strict reads at that same return.
Do not assert that arbitrary native success supplies physical Trace inputs.

## Derive selected support from the same actual Scan

Do not add selected-path closedness as a new local-entry premise.

1. `SourceCurrentConjunctionRequired.selected_primary` transports the actual
   selected primary-false certificates to the successful Scan-return heap.
2. `scan_required_complete` derives maximal-tip support, literal required
   bounds, selected `ForestClosed` domains, readiness, same-cache fields,
   inventory admission, and exact required-filter language. Other siblings
   can remain open.
3. `SelectedRecords.retained_records` and `Retained.fields` (`:102`, `:73`)
   give the positional original sublist and exact `kept.map paths = selected`.
   The actual precheck supplies proper paths, coherent records, ascending
   tries, and Nontrivial classes. Transport these through that sublist.
4. `RequiredActual.verified` aligns a supplied literal required success with
   the derived receipt. `required_unique` identifies both list and heap.
5. `SourceCurrentConjunctionRequiredClassPass.selected_domains` (`:29`)
   supplies every retained record path domain from that receipt. Its
   `satisfied_required` (`:44`) discharges the required-language filter for
   class-satisfying terms. ClassWorker therefore needs no supplied future
   domain or language law.

For actual global receipts, use `ScanClassPassActual.Reads` and
`SourceCurrentAllocatedRequiredReadValidity.required`. The older base Reads
uses the superseded primary-read interface. Construct or validate reads for
the **same** actual Scan, required return, and class pass. Thread each actual
final bundle into the next stage. Do not equate independently chosen deep
read histories. Required heap advancement retains native cells, domains,
and equality operations; class execution can grow them.

## Parent and mutual outer composition

Wrap the literal local worker in the parent constructor. Check raw guard
contradiction first. Rejection uses `MkEdge.reject` and its actual Top-field
allocation with no child-computation premise. The live branch loads the
resident field, runs local reduction, and builds the parent at its literal
return. Retain actual arity checks and sentinel behavior. Use
`ParentEdgeActual` for the receipt; do not fabricate a successful field load.

Next implement the eight literal outer families in the shape of
`PartialGraph`: NodeCall, NodeBody, EdgeCall, EdgeBody, Rows, Descendants,
Children, and Walk. Use `PartialState.beginNode/beginEdge` and the complete
FlatMemoThunk protocol. Ready hits reuse their recorded result. Evaluate
branches run the stored winning owner and finish that exact handle.
Busy/absent, exhausted, errors, and unexpected Rec remain observable
incomplete outcomes; they are not successful graph constructors.

Reuse `InheritedPrefix.resident_finite` for the returned edge and
`PartialDescent.complete` for each current index. Derive child requests from
their literal allocation result, not from a desired semantic callback.
Rebuild same-arity edges and nodes with `RawRebuild`. Use `PartialFrames`
and `PartialCallSteps` to retain evaluating owners and all returned cells
across nested calls in both result families.

`PartialActual` already proves the eight mutual semantic steps from actual
strict reads and reached checks. `PartialChecks.Checks` (`:142`) asks only
for the range plan of actual reached EdgeBody prefixes; `.restrict` and
`.edge_body` supply the exact child plan. It is not a completed body-law
oracle. `PartialEdgeActual.Ranges` (`:33`) is conditional on a reached live
load, and `CallRanges` (`:42`) is conditional on the actual evaluate winner.
A new executable completion plan must retain this prefix discipline.

Use actual-graph to stable-worker proofs first. Claim general termination
only after deriving existence of those graphs from an independent measure
or a clearly stated initial completion domain. The existing conditional
`PartialActual.root_exact` does not supply that existence: it consumes an
actual completed call, strict reads, Checks, Context, inherited EqReady, and
input residency. Its empty inherited payload must have an actual allocation
receipt. It must not be a fabricated physical identity.

## Checkpoint and claim discipline

Keep initial Context and reached range obligations explicit. Context includes
Good/readiness, loaded fields, scopes, idle native tables, computed-inventory
admission, sound outer cells, warm merge Stored/CacheCovers, fourth Correct,
global Valid, and ProbeHeap. Cold/history entry modules can derive these
when their actual construction premises apply. Final Context, selected
domains, body laws, and result language must be conclusions.

Preserve all older proof and counterexample bytes. Add new modules and
focused raw evidence. Use one coordinated pinned Lake process. A green
Audit checks the formal statements; it does not close concrete solver/IO,
machine identity, host demand/publication, new frontend validation/codec,
all API, or separate Sized contracts. Those remain part of the full goal.

Record every Haskell behavior repair in the **first root FINDINGS.md fix
registry**, with exact failure, reproducer, changed files, fix commit, and
upstream status. Report a new source defect before changing Haskell. This
checkpoint changed no Haskell behavior. Preserve the historical repairs,
counterexamples, marked drafts, restart authorities, and evidence across
every upstream refresh.
