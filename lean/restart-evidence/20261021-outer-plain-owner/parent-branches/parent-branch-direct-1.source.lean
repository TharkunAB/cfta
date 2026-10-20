import MicroCFTA.SourceCurrentActualLocalBranchCases
import MicroCFTA.SourceCurrentActualParentRowOrigins

/-!
# Actual successful Parent branches

A successful literal Parent retains original children, erases their
slots, returns the Empty sentinel, or completes a nonempty selected pass.
The selected case keeps the same field load, local return and accepted
constructor call. It also keeps the exact Scan, Required and pass returns.
No positional footprint or future outer return is required.
-/
namespace MicroCFTA.SourceCurrentActualParentBranchCases
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable {width : Nat}

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧
      next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value, middle, current, memo, rfl, actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A completed Parent supplies its exact child shape or selected phase receipts. -/
theorem edge_cases {g s r e p h m c n budget symbol original inherited children before fourth memo returned after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited children
      before fourth memo = .done returned after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      FieldAvailable before.operations original ∧ EqReady before.operations.constraints inherited ∧
        Values before.native.machine.heap children) :
    returned.children = children ∨
      returned.children = EqualityLeafProjectionRuntimeEmpty.erase children ∨
      returned.children = [.empty] ∨
      ∃ (loaded : Allocated) (middle : Checked width) (records kept : List Record)
        (scanned : Checked width) (scanFourth : Fourth) (prepared : List Node) (preparedHeap : Heap),
        SourceEqualityMkEdgeAllocation.contradictory original = false ∧
        SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
        SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children
          before fourth memo = .done returned.children middle saved current ∧
        SourceCurrentAllocatedMkEdge.build symbol loaded returned.children middle = (.ok returned, after) ∧
        SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
          returned.children.length = true ∧
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
          .ok (.classes records) ∧
        SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget children records
          (prefixState before loaded inherited) fourth = .done (none, kept) scanned scanFourth ∧
        kept ≠ [] ∧
        SourceEqualityRequiredExecution.requireAll r h
          (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) children
          scanned.native.machine.heap = .done prepared preparedHeap ∧
        SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared
          (advanceHeap scanned preparedHeap) memo = .done returned.children middle current ∧
        saved = scanFourth := by
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory original with
  | true =>
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, ite_true] at actual
      cases actual
      exact Or.inr (Or.inr (Or.inl (SourceCurrentActualParentRowOrigins.reject_children symbol before good)))
  | false =>
      obtain ⟨field, inheritedReady, available⟩ := live rejected
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, Bool.false_eq_true, ite_false] at actual
      cases loadedAt : SourceEqualityConstraintFieldLookup.load original before.operations.constraints with
      | error => simp only [loadedAt] at actual; cases actual
      | ok value =>
          cases value with
          | none => simp only [loadedAt] at actual; cases actual
          | some loaded =>
              simp only [loadedAt] at actual
              obtain ⟨values, middle, completed, warm, first, last⟩ := parent_bind_done _ _ actual
              have properties := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
                good.operations.constraints field.1 loaded loadedAt
              have reduced : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
                  children before fourth memo = .done values middle completed warm := by
                cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
                    children before fourth memo with
                | failed => simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at first; cases first
                | done output checked next current =>
                    simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at first
                    cases first
                    rfl
              obtain ⟨effect, _, known⟩ := SourceCurrentParentOperationInvariants.reduce reduced good stored
                properties.1 inheritedReady available
              cases observed : SourceCurrentAllocatedMkEdge.build symbol loaded values middle with
              | mk built checked =>
                  cases built with
                  | error => simp only [SourceCurrentAllocatedParentWorker.build, observed] at last; cases last
                  | ok value =>
                      simp only [SourceCurrentAllocatedParentWorker.build, observed] at last
                      cases last
                      have fields := SourceCurrentActualParentRowOrigins.build_children observed effect.good
                        (properties.1.grows effect.operations.constraint_growth) known
                      cases keep : SourceEqualityMkEdgeAllocation.accepted
                          (SourceEqualityConjoinAllocation.readback loaded) values.length with
                      | false =>
                          simp only [keep, Bool.false_eq_true, ite_false] at fields
                          exact Or.inr (Or.inr (Or.inl fields))
                      | true =>
                          simp only [keep, ite_true] at fields
                          rcases SourceCurrentActualLocalBranchCases.reduce_cases reduced with originalChildren | erased | selected
                          · exact Or.inl (fields.trans originalChildren)
                          · exact Or.inr (Or.inl (fields.trans erased))
                          · obtain ⟨records, kept, scanned, scanFourth, prepared, preparedHeap,
                              precheck, scanCall, nonempty, requiredCall, passCall, sameFourth⟩ := selected
                            refine Or.inr (Or.inr (Or.inr ⟨loaded, middle, records, kept, scanned, scanFourth,
                              prepared, preparedHeap, rejected, loadedAt, ?_, ?_, ?_, precheck, scanCall,
                              nonempty, requiredCall, ?_, sameFourth⟩))
                            · simpa only [fields] using reduced
                            · simpa only [fields] using observed
                            · simpa only [fields] using keep
                            · simpa only [fields] using passCall

end MicroCFTA.SourceCurrentActualParentBranchCases
