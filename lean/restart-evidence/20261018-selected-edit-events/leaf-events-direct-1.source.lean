import MicroCFTA.SourceCurrentLowerOperationInvariants

/-!
# Literal selected leaf events

A completed shared leaf supplies its actual target force, native request,
and intermediate full state. Slot hits retain the original full state.
Slot misses retain the actual target worker and literal installed slot.
The native trace contains literal steps, without semantic read receipts.
Initial physical facts also derive intermediate and final residency.
These results verify completed observations. They do not prove completion
or derive historical native writers from weak physical cache validity.
-/
namespace MicroCFTA.SourceCurrentActualSharedLeafEvents
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedSharedTargetState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "request" => SourceRecursiveIntersectionCode.requestNode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A completed force is an exact prior slot hit or an actual completed target followed by storage. -/
theorem force {p h m s n : Nat} {record : Record} {originals : List Node} {path : Path}
    {before middle : Shared width} {target : Node}
    (actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before =
      .done target middle) :
    (before.targets path = some target ∧ middle = before) ∨
    (before.targets path = none ∧ ∃ (checked : Checked width) (saved : Memo),
      SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo =
          .done target checked saved ∧ middle = store before path target checked saved) := by
  cases found : before.targets path with
  | some value =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.force,found] at actual
    cases actual
    exact .inl ⟨rfl,rfl⟩
  | none =>
    cases completed : SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
    | failed => simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,completed] at actual; cases actual
    | done value checked saved =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,completed] at actual
      cases actual
      exact .inr ⟨rfl,checked,saved,completed,rfl⟩

/-- Literal shared target-leaf success derives the force and checked request at their exact states. -/
theorem target_leaf {p h m s n : Nat} {record : Record} {originals : List Node} {path : Path}
    {input result : Node} {before after : Shared width}
    (actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path input before =
      .done result after) :
    ∃ (target : Node) (middle : Shared width) (checked : Checked width),
      SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before = .done target middle ∧
      SourceEqualityNativeDemand.execute n (.code (request emptyDomain target input)) middle.checked =
        .done result checked ∧ after = advance middle checked ∧
      after.targets = middle.targets ∧ after.memo = middle.memo ∧
      ∃ count, count < n ∧ SourceEqualityNativeDemand.Steps count
        (.code (request emptyDomain target input)) middle.checked (.code (.pure result)) checked := by
  cases forced : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before with
  | failed =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,forced,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    cases actual
  | done target middle =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,forced,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    cases queried : SourceEqualityNativeDemand.execute n (.code (request emptyDomain target input)) middle.checked with
    | yielded | failed | constraintError | blocked =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.step,queried] at actual
      cases actual
    | done value checked =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.step,queried] at actual
      cases actual
      exact ⟨target,middle,checked,forced,queried,rfl,rfl,rfl,
        SourceEqualityNativeDemand.done_trace n _ _ _ _ queried⟩

private theorem unlift {p h m s n : Nat} {record : Record} {originals : List Node} {path : Path}
    {input result : Node} {before after : Shared width}
    (actual : SourceCurrentAllocatedSharedEditWorker.leaf p h m s n record originals path input before =
      .done result after) :
    SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path input before = .done result after := by
  cases observed : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path input before with
  | failed => simp only [SourceCurrentAllocatedSharedEditWorker.leaf,observed,
      SourceCurrentAllocatedSharedEditWorker.lift] at actual; cases actual
  | done value state =>
    simp only [SourceCurrentAllocatedSharedEditWorker.leaf,observed,SourceCurrentAllocatedSharedEditWorker.lift] at actual
    cases actual
    rfl

/-- A selected edit leaf derives the actual target and literal native steps without a semantic Reads premise. -/
theorem leaf {p h m s n : Nat} {record : Record} {originals : List Node} {path : Path}
    {input result : Node} {before after : Shared width}
    (actual : SourceCurrentAllocatedSharedEditWorker.leaf p h m s n record originals path input before =
      .done result after) :
    ∃ (target : Node) (middle : Shared width) (checked : Checked width),
      SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before = .done target middle ∧
      SourceEqualityNativeDemand.execute n (.code (request emptyDomain target input)) middle.checked =
        .done result checked ∧ after = advance middle checked ∧
      after.targets = middle.targets ∧ after.memo = middle.memo ∧
      ∃ count, count < n ∧ SourceEqualityNativeDemand.Steps count
        (.code (request emptyDomain target input)) middle.checked (.code (.pure result)) checked :=
  target_leaf (unlift actual)

/-- Initial physical slot and operand residency derive the force midpoint and completed leaf invariants. -/
theorem physical {p h m s n : Nat} {record : Record} {originals : List Node} {path : Path}
    {input result : Node} {before after : Shared width}
    (actual : SourceCurrentAllocatedSharedEditWorker.leaf p h m s n record originals path input before =
      .done result after)
    (good : SourceCurrentLowerOperationInvariants.SharedGood before)
    (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap input) :
    ∃ (target : Node) (middle : Shared width) (checked : Checked width),
      SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before = .done target middle ∧
      SourceEqualityNativeDemand.execute n (.code (request emptyDomain target input)) middle.checked =
        .done result checked ∧ after = advance middle checked ∧
      SourceCurrentLowerOperationInvariants.Effect before.checked middle.checked ∧
      SourceCurrentLowerOperationInvariants.SharedGood middle ∧
      Available middle.checked.native.machine.heap target ∧ Available middle.checked.native.machine.heap input ∧
      SourceCurrentLowerOperationInvariants.Effect before.checked after.checked ∧
      SourceCurrentLowerOperationInvariants.SharedGood after ∧ Available after.checked.native.machine.heap result := by
  obtain ⟨target,middle,checked,forced,queried,final,_⟩ := leaf actual
  obtain ⟨effect,current,known⟩ := SourceCurrentLowerOperationInvariants.force forced good originalsAvailable
  obtain ⟨last,retained,resultKnown⟩ := SourceCurrentLowerOperationInvariants.leaf (unlift actual) good originalsAvailable available
  exact ⟨target,middle,checked,forced,queried,final,effect,current,known,
    effect.keeps.available input available,last,retained,resultKnown⟩

end MicroCFTA.SourceCurrentActualSharedLeafEvents
