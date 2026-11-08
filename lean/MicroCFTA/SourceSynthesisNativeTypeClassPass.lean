import MicroCFTA.SourceSynthesisNativeTypeSharedEdit
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# Type routes through the actual current class pass

Each class captures its actual entry forest. Only its target slots reset.
The checked state and both warm Merge certificates pass between classes.
The source right fold executes the tail first. Its route transport supplies
the next class's input certificates. Final empty propagation makes no call.

These laws concern completed current class graphs and initial structural
routes. They do not prove completion, all reached source classifications,
finite-word bounds, or native lazy demand order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeClassPass
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityProjectionGraph (select_member)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes)
open SourceCurrentAllocatedClassEdits (Class)
open SourceCurrentAllocatedClassPass (Fold Pass)
open SourceCurrentAllocatedSharedTargetState (initial)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable {width : Nat}

private theorem propagate_routes (valid : Guard → Prop) (values : List (Value Symbol Guard)) :
    ForestRoutes valid values (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · have typed : ∀ value ∈ EqualityLeafProjectionRuntimeEmpty.erase values, Annotated valid value := by
      intro value member
      obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
      exact .empty
    intro path _
    cases path with
    | nil => exact typed
    | cons index path =>
        intro value found
        exact .annotated path value (typed value (select_member found))
  · exact fun _ route => route

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A class retains warm native and Merge facts while clearing only its local slots. -/
theorem class_edit (lib : Library) {record values results} {before after : Checked width} {memo saved : Memo}
    (actual : Class record values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : SourceEqualityClassOrder.Coherent record)
    (routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ ForestRoutes (Origin lib) values results := by
  cases actual with
  | edit lower =>
      obtain ⟨next, extension, returned, resultClosed, retained⟩ :=
        SourceSynthesisNativeTypeSharedEdit.list lib lower ready available closed routes
          (SourceCurrentAllocatedClassEditPlan.compiled_populated record) available closed
          (SourceCurrentHereditaryTypeEditPlan.compiled_forest_paths (Origin lib) record coherent values routes)
      exact ⟨SourceSynthesisNativeTypeSharedState.initial lib _ _
          next.checked next.costs next.physicalMemo next.typedMemo,
        extension, returned, resultClosed, retained⟩

/-- Each head class receives the exact tail return and its transported Type routes. -/
theorem fold (lib : Library) {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Fold records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ ForestRoutes (Origin lib) values results := by
  revert ready available closed coherent routes
  induction actual with
  | nil =>
      intro ready available closed _ _
      exact ⟨ready, .refl _, available, closed, fun _ route => route⟩
  | cons tail head ih =>
      intro ready available closed coherent routes
      obtain ⟨middleReady, first, middleAvailable, middleClosed, tailRoutes⟩ := ih ready available closed
        (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => routes record (List.mem_cons_of_mem _ member))
      obtain ⟨next, last, returned, resultClosed, headRoutes⟩ := class_edit lib head middleReady
        middleAvailable middleClosed (coherent _ List.mem_cons_self)
        (fun path member => tailRoutes (path.map Int.ofNat) (routes _ List.mem_cons_self path member))
      exact ⟨next, first.trans last, returned, resultClosed,
        fun path route => headRoutes path (tailRoutes path route)⟩

/-- The actual full pass retains all Type routes through final literal empty propagation. -/
theorem pass (lib : Library) {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Pass records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values) :
    Ready lib (initial after saved) ∧ Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ ForestRoutes (Origin lib) values results := by
  cases actual with
  | done actual =>
      obtain ⟨next, extension, returned, resultClosed, retained⟩ :=
        fold lib actual ready available closed coherent routes
      have scope := SourceEqualityEmptyPropagation.scope _ _ returned resultClosed
      exact ⟨next, extension, scope.1, scope.2,
        fun path route => propagate_routes (Origin lib) _ path (retained path route)⟩

end MicroCFTA.SourceSynthesisNativeTypeClassPass
