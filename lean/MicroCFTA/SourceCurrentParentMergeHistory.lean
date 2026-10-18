import MicroCFTA.SourceCurrentLowerMergeHistory
import MicroCFTA.SourceCurrentParentOperationInvariants

/-!
# Historical Merge writers through literal Parent returns

Scan, required children and constructors retain the Merge table.
Actual class edits preserve every historical writer from their initial memo.
Initial physical facts justify the reached calls. No semantic reads,
future completion or source-rank assumption is an input.
-/
namespace MicroCFTA.SourceCurrentParentMergeHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (Effect)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Raw" => SourceCurrentMergePositiveRowOrigins.Raw SourceCurrentAllocatedMerge.literalClear
  (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula))
variable {width : Nat}

private theorem physical_only {before : Checked width} (good : Good before)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap)
    (fields : SourceCurrentConjunctionEquality.Fields before.operations heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) :=
  let effects := (⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩ :
    SourceCurrentConjunctionRowsAllocation.Effects (physical before) ⟨heap,before.operations⟩)
  ⟨good.advance _ effects,keeps,effects.grows⟩

private theorem local_bind_done {A B : Type}
    (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

private theorem local_scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s p h n budget records values before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.scan g s p h n budget records values before fourth memo = .done result after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ current = memo := by
  cases observed : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.scan,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedLocalWorker.scan,observed] at actual
    cases actual
    have paths := (SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records before fourth).symm
    rw [observed] at paths
    exact ⟨SourceCurrentParentOperationInvariants.scan paths good available,rfl⟩

private theorem local_required [DecidableEq (EdgeKey Symbol Guard)]
    {r h paths values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.required r h paths values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Values after.native.machine.heap results ∧ saved = fourth ∧ current = memo := by
  cases observed : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | pending | unresolved | exhausted => simp only [SourceCurrentAllocatedLocalWorker.required,observed] at actual; cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedLocalWorker.required,observed] at actual
    cases actual
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.requireAll
      (FieldAvailable before.operations) r h paths values _ _ heap observed good.semantic good.costs good.fields available
    exact ⟨physical_only good heap keeps semantic costs fields,known,rfl,rfl⟩

private theorem local_pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {e p h m s n records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.pass e p h m s n records values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (raw : Raw memo) : Raw current := by
  cases observed : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo with
  | failed => simp only [SourceCurrentAllocatedLocalWorker.pass,observed] at actual; cases actual
  | done output checked completed =>
    simp only [SourceCurrentAllocatedLocalWorker.pass,observed] at actual
    cases actual
    exact SourceCurrentLowerMergeHistory.class_pass observed good stored available raw

/-- Actual Scan and required returns lead to a class pass that retains Merge writers. -/
theorem classes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget records values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values)
    (raw : Raw memo) : Raw current := by
  obtain ⟨result,middle,completed,current,first,later⟩ := local_bind_done _ _ actual
  obtain ⟨effect,rfl⟩ := local_scan first good available
  cases stopped : result.1 with
  | some paths => simp only [stopped] at later; cases later; exact raw
  | none =>
    simp only [stopped] at later
    obtain ⟨required,checked,following,warm,requiredDone,passDone⟩ := local_bind_done _ _ later
    obtain ⟨firstEffect,known,_,rfl⟩ := local_required requiredDone effect.good
      (fun value member => effect.keeps.available value (available value member))
    exact local_pass passDone firstEffect.good (stored.grows (effect.keeps.trans firstEffect.keeps)) known raw

private theorem precheck_good (loaded : Allocated) (inherited : EqValue) (before : Checked width)
    (good : Good before) (stored : EqReady before.operations.constraints loaded.stored)
    (ready : EqReady before.operations.constraints inherited) :
    Good (SourceCurrentAllocatedPrecheck.state before loaded inherited) := by
  obtain ⟨own,done,valid,ownReady,_,growth⟩ := SourceEqualityAccessorAllocation.equalities_correct
    loaded.stored loaded.guard before.operations good.operations stored
  have checked := SourceEqualityPrecheckAllocation.precheck_correct own inherited
    (SourceEqualityAccessorAllocation.equalities loaded.stored loaded.guard before.operations).2 valid ownReady
    (ready.grows growth.constraint_growth)
  have same : SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations =
      SourceEqualityPrecheckAllocation.precheck own inherited
        (SourceEqualityAccessorAllocation.equalities loaded.stored loaded.guard before.operations).2 := by
    simp only [SourceEqualityPartialPrecheckAllocation.run,done]
  have total := SourceCurrentConjunctionEquality.grows_trans growth checked.2.2
  apply good.advance
  rw [same]
  exact ⟨SourceEqualityRequiredCache.pure_keeps _ good.heap,
    ⟨good.semantic,good.costs,checked.2.1,good.fields.grows total⟩,total⟩

/-- A literal local reduction preserves Merge writers through every successful precheck branch. -/
theorem reduce [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget loaded inherited values before fourth memo results after saved current}
    (actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo = .done results after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (loadedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (available : Values before.native.machine.heap values)
    (raw : Raw memo) : Raw current := by
  have currentGood := precheck_good loaded inherited before good loadedReady inheritedReady
  cases observed : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message => simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual; cases actual
  | ok branch =>
    cases branch with
    | unchanged | emptyChildren =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual
      cases actual
      exact raw
    | classes records =>
      simp only [SourceCurrentAllocatedLocalWorker.reduce,observed] at actual
      exact classes actual currentGood stored available raw

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧ next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value,middle,current,memo,rfl,actual⟩
  | failed => cases actual

/-- A literal Parent return preserves actual historical Merge writers from its initial memo. -/
theorem parent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {g s r e p h m c n budget symbol original inherited children before fourth memo result after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done result after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (raw : Raw memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧ Values before.native.machine.heap children) :
    Raw current := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
    simp only [SourceCurrentAllocatedParentWorker.edge,rejected,ite_true] at actual
    cases actual
    exact raw
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
        have middleRaw := reduce reduced good stored properties.1 inheritedReady available raw
        cases observed : SourceCurrentAllocatedMkEdge.build symbol loadedValue values middle with
        | mk returned checked =>
          cases returned with
          | error => simp only [SourceCurrentAllocatedParentWorker.build,observed] at last; cases last
          | ok value =>
            simp only [SourceCurrentAllocatedParentWorker.build,observed] at last
            cases last
            exact middleRaw

end MicroCFTA.SourceCurrentParentMergeHistory
