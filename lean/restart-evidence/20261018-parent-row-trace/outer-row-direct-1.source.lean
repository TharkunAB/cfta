import MicroCFTA.SourceCurrentOuterInheritedGain

/-!
# Full row fields through actual outer requests

Actual Parent returns retain the original full field or the plain sentinel.
Returned outer cells retain the field of their captured edge request.
Warm hits use actual key equality and resident edge identity.
-/
namespace MicroCFTA.SourceCurrentOuterRowFieldOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "NativeGood" => SourceCurrentNativeOperationHeap.Good
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat}

/-- A returned row retains its full source field or the plain rejection field. -/
def Fields (symbol : Symbol) (original : Guard) (result : Edge) : Prop :=
  result.entry.key.symbol = symbol ∧
    (result.entry.key.constraint = original ∨ result.entry.key.constraint = top)

private theorem raw_fields [DecidableEq (EdgeKey Symbol Guard)] (before : Checked width)
    (good : NativeGood before) (symbol : Symbol) (field : Guard) (children : List Node)
    (available : Values before.native.machine.heap children) :
    (run (makeEdge symbol field children) before.native.machine.heap).1.entry.key.symbol = symbol ∧
      (run (makeEdge symbol field children) before.native.machine.heap).1.entry.key.constraint = field := by
  have actual := MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
    good.semantic.ready.semantic.1.normal.facts symbol field children available
  exact ⟨actual.1,actual.2.1⟩

private theorem reject_fields [DecidableEq (EdgeKey Symbol Guard)] (before : Checked width)
    (good : NativeGood before) (symbol : Symbol) (original : Guard) :
    Fields symbol original (SourceCurrentAllocatedMkEdge.reject symbol before).1 := by
  have actual := raw_fields before good symbol top [.empty]
    (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
  exact ⟨actual.1,Or.inr actual.2⟩

private theorem build_fields [DecidableEq (EdgeKey Symbol Guard)]
    {symbol loaded children before result after}
    (actual : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result,after))
    (good : NativeGood (width := width) before)
    (loadedReady : EqReady before.operations.constraints loaded.stored)
    (available : Values before.native.machine.heap children) :
    Fields symbol (SourceEqualityConjoinAllocation.readback loaded) result := by
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard children
    before.operations before.native.machine.heap good.operations loadedReady
  cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
  | true =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = true := keep
    have equation : SourceCurrentAllocatedMkEdge.build symbol loaded children before =
        (.ok (run (makeEdge symbol (SourceEqualityConjoinAllocation.readback loaded) children) before.native.machine.heap).1,
          SourceCurrentAllocatedQueryMemo.advancePhysical before
            ⟨(run (makeEdge symbol (SourceEqualityConjoinAllocation.readback loaded) children) before.native.machine.heap).2,
            (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).2⟩) := by
      simp only [SourceCurrentAllocatedMkEdge.build,built.1,SourceEqualityMkEdgeAllocation.work,
        SourceEqualityMkEdgeAllocation.outputState,selected,ite_true]
      rfl
    have same := Except.ok.inj (congrArg Prod.fst (equation.symm.trans actual))
    cases same
    have fields := raw_fields before good symbol (SourceEqualityConjoinAllocation.readback loaded) children available
    exact ⟨fields.1,Or.inl fields.2⟩
  | false =>
    have selected : SourceEqualityMkEdgeAllocation.accepted
        (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length = false := keep
    have equation : SourceCurrentAllocatedMkEdge.build symbol loaded children before =
        (.ok (run (makeEdge symbol top [.empty]) before.native.machine.heap).1,
          SourceCurrentAllocatedQueryMemo.advancePhysical before
            ⟨(run (makeEdge symbol top [.empty]) before.native.machine.heap).2,
            SourceEqualityMkEdgeAllocation.emptyField
              (SourceEqualityMkEdgeAllocation.check loaded.stored loaded.guard children.length before.operations).2⟩) := by
      simp only [SourceCurrentAllocatedMkEdge.build,built.1,SourceEqualityMkEdgeAllocation.work,
        SourceEqualityMkEdgeAllocation.outputState,selected,Bool.false_eq_true,ite_false]
    have same := Except.ok.inj (congrArg Prod.fst (equation.symm.trans actual))
    cases same
    have fields := raw_fields before good symbol top [.empty]
      (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
    exact ⟨fields.1,Or.inr fields.2⟩

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → SourceCurrentEmptinessMemo.Memo →
      SourceCurrentMemoMergeGraph.Memo Symbol Guard → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : SourceCurrentEmptinessMemo.Memo}
    {saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧
      next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Initial physical inputs and an actual Parent return derive its complete row-field origin. -/
theorem parent
    {g s r e p h m c n budget symbol original inherited children before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children
      before fourth memo = .done result after saved current)
    (good : NativeGood (width := width) before)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧
      Values before.native.machine.heap children) : Fields symbol original result := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    exact reject_fields before good symbol original
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
        obtain ⟨effect,_retained,known⟩ := SourceCurrentParentOperationInvariants.reduce reduced good stored
          properties.1 inheritedReady available
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk returned checked =>
          cases returned with
          | error => simp only [SourceCurrentAllocatedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedParentWorker.build,observed] at last
            cases last
            have fields := build_fields observed effect.good
              (properties.1.grows effect.operations.constraint_growth) known
            simpa only [properties.2] using fields

end MicroCFTA.SourceCurrentOuterRowFieldOrigins
