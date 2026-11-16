import MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins
import MicroCFTA.SourcePruningEnumerationSharedBranchingAppend

namespace MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedBranching (scan scan_append)
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

set_option autoImplicit false

/-- Each indexed output belongs to one full row-output block in the actual scan. -/
theorem scan_output_block_origin
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) (edges : List Edge) (caller : Caller width) (queries : Queries)
    (index : Nat) (output : Output)
    (observed : (outputs (scan visit before edges caller queries))[index]? = some output) :
    ∃ (attempted : List Edge) (edge : Edge) (remaining : List Edge)
        (rowCaller : Caller width) (rowQueries : Queries)
        (processed : List (SelectedEdge.Result width)) (earlier : List Output)
        (rowResult : Result Output Reason width) (localIndex : Nat) (later : List Output),
      edges = attempted ++ edge :: remaining ∧
      scan visit before attempted caller queries = .complete processed earlier rowCaller rowQueries ∧
      visit edge rowCaller rowQueries before = rowResult ∧
      (outputs rowResult)[localIndex]? = some output ∧
      index = earlier.length + localIndex ∧
      outputs (scan visit before edges caller queries) = earlier ++ outputs rowResult ++ later := by
  obtain ⟨attempted, edge, remaining, rowCaller, rowQueries, processed, earlier,
    rowResult, localIndex, order, prefixRun, row, selected, offset⟩ :=
    scan_output_origin visit before edges caller queries index output observed
  have whole : outputs (scan visit before edges caller queries) =
      earlier ++ outputs (scan visit before (edge :: remaining) rowCaller rowQueries) := by
    rw [order, scan_append, prefixRun]
    dsimp only
    cases scan visit before (edge :: remaining) rowCaller rowQueries <;> rfl
  cases rowResult with
  | stopped rowProcessed rowOutputs currentStop =>
      refine ⟨attempted, edge, remaining, rowCaller, rowQueries, processed, earlier,
        .stopped rowProcessed rowOutputs currentStop, localIndex, [],
        order, prefixRun, row, selected, offset, ?_⟩
      rw [whole]
      simp only [scan, row, outputs, List.append_nil]
  | complete rowProcessed rowOutputs reached saved =>
      refine ⟨attempted, edge, remaining, rowCaller, rowQueries, processed, earlier,
        .complete rowProcessed rowOutputs reached saved, localIndex,
        outputs (scan visit before remaining reached saved),
        order, prefixRun, row, selected, offset, ?_⟩
      rw [whole]
      simp only [scan, row]
      cases scan visit before remaining reached saved <;>
        simp only [outputs, List.append_assoc]

end MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins
