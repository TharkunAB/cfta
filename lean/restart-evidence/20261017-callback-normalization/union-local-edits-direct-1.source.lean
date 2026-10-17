import MicroCFTA.SourceCurrentUnionNormalTargets
import MicroCFTA.SourceCurrentAllocatedClassWorker

/-!
# Union normality through actual shared edits and class passes

The fuel induction includes recursive heads and every selected child.
Rebuilt rows retain the actual source guard. Class folds use their literal
returned forests and checked states. The theorem covers stopping failures.
-/
namespace MicroCFTA.SourceCurrentUnionNormalEdits
open InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record

private theorem bind (first : SourceCurrentAllocatedSharedEditWorker.Outcome width A)
    (next : A → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width B)
    (normal : UnionNormal first.state.checked.native.machine.heap)
    (later : ∀ value after, UnionNormal after.checked.native.machine.heap → UnionNormal (next value after).state.checked.native.machine.heap) :
    UnionNormal (first.bind next).state.checked.native.machine.heap := by
  cases first with
  | failed => exact normal
  | done value state => exact later value state normal

private theorem leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h m s n : Nat)
    (record : Record) (originals : List (Value Symbol Guard)) (path : EqualityNormalize.Path)
    (value : Value Symbol Guard) (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedEditWorker.leaf p h m s n record originals path value state).state.checked.native.machine.heap := by
  have retained := SourceCurrentUnionNormalTargets.shared_leaf p h m s n record originals path value state normal
  cases actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path value state <;>
    simpa only [SourceCurrentAllocatedSharedEditWorker.leaf,actual,SourceCurrentAllocatedSharedEditWorker.lift,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.state,SourceCurrentAllocatedSharedEditWorker.Outcome.state] using retained

private theorem head [DecidableEq (EdgeKey Symbol Guard)] (h : Nat) (value : Value Symbol Guard)
    (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedEditWorker.head h value state).state.checked.native.machine.heap := by
  have retained := SourceCurrentRequiredUnionNormalRead.head h value state.checked.native.machine.heap normal
  cases actual : SourceEqualityRequiredWorker.head h value state.checked.native.machine.heap <;>
    simpa only [SourceCurrentAllocatedSharedEditWorker.head,actual,SourceCurrentRequiredUnionNormalRead.StoppedNormal,
      SourceCurrentAllocatedSharedEditWorker.Outcome.state,SourceCurrentAllocatedSharedEditGraph.advanceHeap,
      SourceCurrentAllocatedSharedTargetState.advance,SourceCurrentConjunctionClassScan.advanceHeap,
      SourceCurrentAllocatedQueryMemo.advancePhysical,SourceRecursiveIntersectionThunks.advance] using retained

private theorem children
    (call : Edits EqualityNormalize.Path → Value Symbol Guard → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width (Value Symbol Guard))
    (checked : ∀ edits value state, UnionNormal state.checked.native.machine.heap → UnionNormal (call edits value state).state.checked.native.machine.heap)
    (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat) (values : List (Value Symbol Guard))
    (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedEditWorker.children call entries index values state).state.checked.native.machine.heap := by
  induction values generalizing index state with
  | nil => exact normal
  | cons value rest ih =>
      rw [SourceCurrentAllocatedSharedEditWorker.children]
      split
      · exact bind _ _ (ih (index+1) state normal) (fun _ _ afterNormal => afterNormal)
      · exact bind _ _ (checked _ value state normal) (fun _ middle middleNormal =>
          bind _ _ (ih (index+1) middle middleNormal) (fun _ _ afterNormal => afterNormal))

private theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    (call : Edits EqualityNormalize.Path → Value Symbol Guard → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width (Value Symbol Guard))
    (checked : ∀ edits value state, UnionNormal state.checked.native.machine.heap → UnionNormal (call edits value state).state.checked.native.machine.heap)
    (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedEditWorker.rows call entries edges state).state.checked.native.machine.heap := by
  induction edges generalizing state with
  | nil => exact normal
  | cons edge rest ih =>
      apply bind _ _ (children call checked entries 0 edge.children state normal)
      intro values middle middleNormal
      apply bind _ _ (SourceCurrentRequiredUnionNormal.edge edge.entry.key.symbol edge.entry.key.constraint values _ middleNormal)
      intro _ after afterNormal
      exact bind _ _ (ih after afterNormal) (fun _ _ finalNormal => finalNormal)

/-- All bounded shared edit branches retain normality at their literal returned state. -/
theorem edit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : Record) (originals : List (Value Symbol Guard)) (e p h m s n : Nat)
    (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value state).state.checked.native.machine.heap := by
  induction e generalizing edits value state with
  | zero => exact normal
  | succ e ih =>
      cases edits with
      | editAt target => exact leaf p h m s n record originals target value state normal
      | editBelow entries =>
          cases value with
          | empty | reference => exact normal
          | node entry edges depth free =>
              exact bind _ _ (rows _ ih entries edges state normal)
                (fun rebuilt after afterNormal => SourceCurrentRequiredUnionNormal.node rebuilt _ afterNormal)
          | union | mu => exact bind _ _ (head h _ state normal)
              (fun exposed after afterNormal => ih (.editBelow entries) exposed after afterNormal)

/-- Child-list edits retain normality without requiring any finite cap or closed sibling. -/
theorem editList [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : Record) (originals : List (Value Symbol Guard)) (e p h m s n : Nat)
    (edits : Edits EqualityNormalize.Path) (values : List (Value Symbol Guard))
    (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) edits values state).state.checked.native.machine.heap := by
  cases edits with
  | editAt => exact normal
  | editBelow entries => exact children _ (edit record originals e p h m s n) entries 0 values state normal

private theorem runClass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (e p h m s n : Nat) (record : Record) (values : List (Value Symbol Guard))
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedClassWorker.runClass e p h m s n record values state memo).state.native.machine.heap := by
  have retained := editList record values e p h m s n (SourceCurrentAllocatedClassEditPlan.compiled record) values
    (SourceCurrentAllocatedSharedTargetState.initial state memo) normal
  cases actual : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n) (SourceCurrentAllocatedClassEditPlan.compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial state memo) <;>
    simpa only [SourceCurrentAllocatedClassWorker.runClass,actual,SourceCurrentAllocatedClassWorker.Outcome.state,
      SourceCurrentAllocatedSharedEditWorker.Outcome.state] using retained

private theorem class_bind (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List (Value Symbol Guard) → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    (normal : UnionNormal first.state.native.machine.heap)
    (later : ∀ values after memo, UnionNormal after.native.machine.heap → UnionNormal (next values after memo).state.native.machine.heap) :
    UnionNormal (first.bind next).state.native.machine.heap := by
  cases first with
  | failed => exact normal
  | done value state memo => exact later value state memo normal

private theorem fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (e p h m s n : Nat)
    (records : List Record) (values : List (Value Symbol Guard))
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedClassWorker.fold e p h m s n records values state memo).state.native.machine.heap := by
  induction records generalizing values state memo with
  | nil => exact normal
  | cons record rest ih =>
      exact class_bind _ _ (ih values state memo normal)
        (fun middle after saved afterNormal => runClass e p h m s n record middle after saved afterNormal)

/-- The complete actual right fold and final propagation retain union normality. -/
theorem pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (e p h m s n : Nat)
    (records : List Record) (values : List (Value Symbol Guard))
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedClassWorker.pass e p h m s n records values state memo).state.native.machine.heap :=
  class_bind _ _ (fold e p h m s n records values state memo normal) (fun _ _ _ afterNormal => afterNormal)
end MicroCFTA.SourceCurrentUnionNormalEdits
