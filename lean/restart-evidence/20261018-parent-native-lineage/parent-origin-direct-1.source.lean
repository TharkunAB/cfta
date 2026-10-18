import MicroCFTA.SourceCurrentActualLocalReduceRowOrigins

/-!
# Row origins through literal Parent construction

The actual local reducer supplies indexed row origins. The checked Parent
constructor retains those children or returns its Empty sentinel. Raw
contradiction also returns that sentinel before field or child demand.
The initial raw guard supplies the unselected path footprint. Successful
execution remains explicit. These laws do not prove general completion.
-/
namespace MicroCFTA.SourceCurrentActualParentRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentActualRequiredRowOrigins (Link)
open SourceCurrentClassPositionalFootprints (Unselected)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

/-- Raw rejection has exactly one Empty child without a child availability premise. -/
theorem reject_children (symbol : Symbol) (before : Checked width) (good : Good before) :
    (SourceCurrentAllocatedMkEdge.reject symbol before).1.children = [.empty] := by
  exact (MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
    good.semantic.ready.semantic.1.normal.facts symbol SourceEqualityConstraintConstructors.top [.empty]
    (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)).2.2

/-- Actual checked construction retains the input children or the source Empty sentinel. -/
theorem build_children {symbol loaded children before result after}
    (actual : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result,after))
    (good : Good (width := width) before) (loadedReady : EqReady before.operations.constraints loaded.stored)
    (available : Values before.native.machine.heap children) :
    result.children = if SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
      children.length then children else [.empty] := by
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard children
    before.operations before.native.machine.heap good.operations loadedReady
  have returned := congrArg Prod.fst actual
  simp only [SourceCurrentAllocatedMkEdge.build,built.1] at returned
  cases Except.ok.inj returned
  cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
  | true =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = true := keep
    simp only [SourceEqualityMkEdgeAllocation.work,selected,ite_true,keep]
    exact (MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
      good.semantic.ready.semantic.1.normal.facts symbol (SourceEqualityConjoinAllocation.readback loaded)
      children available).2.2
  | false =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = false := keep
    simp only [SourceEqualityMkEdgeAllocation.work,selected,Bool.false_eq_true,ite_false,keep]
    exact (MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
      good.semantic.ready.semantic.1.normal.facts symbol SourceEqualityConstraintConstructors.top [.empty]
      (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)).2.2

private theorem empty_link {index childIndex : Nat} {source result : Node}
    (present : ([.empty] : List Node)[index]? = some result) : Link childIndex source result := by
  have same : result = .empty := List.mem_singleton.mp (List.mem_of_getElem? present)
  cases same
  intro row impossible
  cases impossible

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧
      next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq Node]

/-- A completed Parent retains the indexed source row and its unselected continuation. -/
theorem edge {g s r e p h m c n budget symbol original inherited children before fourth memo returned after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done returned after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧
        Values before.native.machine.heap children)
    (guards : GuardHeap before.native.machine.heap) (index childIndex : Nat)
    (footprint : ∀ originals : List Record, SourceEqualityPhysicalPayload.own original = .ok (some originals) →
      ∀ record ∈ originals, Unselected record index childIndex)
    {source result : Node} (input : children[index]? = some source)
    (output : returned.children[index]? = some result) : Link childIndex source result := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    rw [reject_children symbol before good] at output
    exact empty_link output
  | false =>
    obtain ⟨field,inheritedReady,available⟩ := live rejected
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,Bool.false_eq_true,ite_false] at actual
    cases loaded : SourceEqualityConstraintFieldLookup.load original before.operations.constraints with
    | error => simp only [loaded] at actual; cases actual
    | ok value =>
      cases value with
      | none => simp only [loaded] at actual; cases actual
      | some loadedValue =>
        simp only [loaded] at actual
        obtain ⟨values,middle,completed,warm,first,last⟩ := parent_bind_done _ _ actual
        have properties := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
          good.operations.constraints field.1 loadedValue loaded
        have reduced : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
            loadedValue inherited children before fourth memo = .done values middle completed warm := by
          cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
              loadedValue inherited children before fourth memo with
          | failed => simp only [SourceCurrentAllocatedParentWorker.reduceChildren,observed] at first; cases first
          | done output checked next current =>
            simp only [SourceCurrentAllocatedParentWorker.reduceChildren,observed] at first
            cases first
            rfl
        obtain ⟨effect,_,known⟩ := SourceCurrentParentOperationInvariants.reduce reduced good stored
          properties.1 inheritedReady available
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk built checked =>
          cases built with
          | error => simp only [SourceCurrentAllocatedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedParentWorker.build,observed] at last
            cases last
            have fields := build_children observed effect.good (properties.1.grows effect.operations.constraint_growth) known
            cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loadedValue) values.length with
            | false =>
              simp only [keep,Bool.false_eq_true,ite_false] at fields
              rw [fields] at output
              exact empty_link output
            | true =>
              simp only [keep,ite_true] at fields
              rw [fields] at output
              exact SourceCurrentActualLocalReduceRowOrigins.reduce reduced good stored original field.1 loaded
                inheritedReady available guards index childIndex footprint input output

end MicroCFTA.SourceCurrentActualParentRowOrigins
