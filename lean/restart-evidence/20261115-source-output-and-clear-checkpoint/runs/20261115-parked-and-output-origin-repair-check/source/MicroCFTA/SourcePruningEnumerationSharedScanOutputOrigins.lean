import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

/-!
# Actual ordered row origins for emitted outputs

Each indexed output comes from one row invoked by the actual shared scan.
The receipt keeps the complete earlier scan and its reached native endpoint.
The row receives the same captured cache as the complete scan.
Output offsets retain order and duplicate occurrences after a later stop.
This result does not construct a whole recursive history or an assignment.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

set_option autoImplicit false

/-- Retain the exact output list under completion or stop. -/
def outputs : Result Output Reason width → List Output
  | .complete _ values _ _ => values
  | .stopped _ values _ => values

/-- An indexed scan output has one actual row and its exact completed prefix. -/
theorem scan_output_origin
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) (edges : List Edge) (caller : Caller width) (queries : Queries)
    (index : Nat) (output : Output)
    (observed : (outputs (scan visit before edges caller queries))[index]? = some output) :
    ∃ (attempted : List Edge) (edge : Edge) (remaining : List Edge)
        (rowCaller : Caller width) (rowQueries : Queries)
        (processed : List (SelectedEdge.Result width)) (earlier : List Output)
        (rowResult : Result Output Reason width) (localIndex : Nat),
      edges = attempted ++ edge :: remaining ∧
      scan visit before attempted caller queries = .complete processed earlier rowCaller rowQueries ∧
      visit edge rowCaller rowQueries before = rowResult ∧
      (outputs rowResult)[localIndex]? = some output ∧
      index = earlier.length + localIndex := by
  induction edges generalizing caller queries index with
  | nil =>
      simp only [scan, outputs, List.getElem?_nil] at observed
      cases observed
  | cons first rest ih =>
      cases head : visit first caller queries before with
      | stopped processed current stop =>
          have same : (outputs (scan visit before (first :: rest) caller queries)) = current := by
            simp only [scan, head, outputs]
          rw [same] at observed
          exact ⟨[], first, rest, caller, queries, [], [], .stopped processed current stop,
            index, rfl, rfl, head, observed, by simp⟩
      | complete processed current reached saved =>
          have combined : outputs (scan visit before (first :: rest) caller queries) =
              current ++ outputs (scan visit before rest reached saved) := by
            simp only [scan, head]
            cases scan visit before rest reached saved <;> rfl
          rw [combined] at observed
          by_cases inside : index < current.length
          · have here : current[index]? = some output := by
              simpa only [List.getElem?_append_left inside] using observed
            exact ⟨[], first, rest, caller, queries, [], [], .complete processed current reached saved,
              index, rfl, rfl, head, here, by simp⟩
          · have outside : current.length ≤ index := by omega
            have later : (outputs (scan visit before rest reached saved))[index - current.length]? = some output := by
              simpa only [List.getElem?_append_right outside] using observed
            obtain ⟨attempted, edge, remaining, rowCaller, rowQueries, previous, earlier,
              rowResult, localIndex, order, prefixRun, row, selected, offset⟩ :=
              ih reached saved (index - current.length) later
            refine ⟨first :: attempted, edge, remaining, rowCaller, rowQueries,
              processed ++ previous, current ++ earlier, rowResult, localIndex, ?_, ?_, row, selected, ?_⟩
            · rw [order]
              rfl
            · simp only [scan, head, prefixRun]
            · simp only [List.length_append]
              omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The identity no-stop eager scan retains the actual producing row and output offset. -/
theorem identity_eager_scan_output_origin
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List Edge) (workFuel recursiveDepth uv : Nat)
    (metadata : SourcePruningRecordTypes.Metadata Unit) (scs : List Suspended)
    (before : Cached) (edges : List Edge) (caller : Caller width) (queries : Queries)
    (index : Nat) (output : SourcePruningEnumerationSharedPreparedRecursive.Output width Unit) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
      workFuel workFuel workFuel workFuel workFuel edgesOf
    let recur := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow child
      (fun _ _ _ node state => MergedSourceComparison.Result.done node state)
      graph [] checkEmpty edgesOf none (fun _ _ => none) workFuel recursiveDepth
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
      graph [] none (fun _ _ => none) workFuel metadata uv
    let visit := fun edge current saved captured =>
      SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
        workFuel uv scs edge current saved captured
    (outputs (scan visit before edges caller queries))[index]? = some output →
    ∃ (attempted : List Edge) (edge : Edge) (remaining : List Edge)
        (rowCaller : Caller width) (rowQueries : Queries)
        (processed : List (SelectedEdge.Result width))
        (earlier : List (SourcePruningEnumerationSharedPreparedRecursive.Output width Unit))
        (rowResult : Result
          (SourcePruningEnumerationSharedPreparedRecursive.Output width Unit)
          (SourcePruningEnumerationSharedPreparedRecursive.Failure width Unit) width)
        (localIndex : Nat),
      edges = attempted ++ edge :: remaining ∧
      scan visit before attempted caller queries = .complete processed earlier rowCaller rowQueries ∧
      SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
        workFuel uv scs edge rowCaller rowQueries before = rowResult ∧
      (outputs rowResult)[localIndex]? = some output ∧
      index = earlier.length + localIndex := by
  dsimp only
  intro observed
  exact scan_output_origin _ before edges caller queries index output observed

end MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins

#check @MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins.scan_output_origin
#print axioms MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins.scan_output_origin

#check @MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins.identity_eager_scan_output_origin
#print axioms MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins.identity_eager_scan_output_origin
