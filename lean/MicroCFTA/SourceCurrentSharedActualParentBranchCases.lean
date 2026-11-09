import MicroCFTA.SourceCurrentAllocatedSharedLocalWorkerStability
import MicroCFTA.SourceEqualityPartialInheritedPlainPass
import MicroCFTA.SourceCurrentActualParentRowOrigins
import MicroCFTA.SourceCurrentSharedParentProbeHeap

/-!
# Actual successful shared Parent branches

The proof follows the literal shared Local and Parent calls. A return
retains the input children, erases their slots, returns Empty, or completes
the same nonempty selected Scan, Required, and class pass. The entry probe
invariant comes from the captured writer Context in its consumers.
-/
namespace MicroCFTA.SourceCurrentSharedActualParentBranchCases
namespace Local
open EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedSharedLocalWorker
open SourceCurrentAllocatedSharedLocalWorkerStability
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq Node] {width : Nat}

/-- A literal success supplies its exact original, erased or selected continuation. -/
private theorem reduce_cases {g s r e p h m c n budget : Nat} {loaded : Allocated}
    {inherited : EqValue} {values results : List Node} {before after : Checked width}
    {fourth saved : Fourth} {memo current : Memo}
    (actual : reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done results after saved current) :
    results = values ∨ results = EqualityLeafProjectionRuntimeEmpty.erase values ∨
      ∃ (records kept : List Record) (scanned : Checked width) (scanFourth : Fourth)
        (prepared : List Node) (preparedHeap : Heap),
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
          .ok (.classes records) ∧
        SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records
          (prefixState before loaded inherited) fourth = .done (none, kept) scanned scanFourth ∧
        kept ≠ [] ∧
        SourceEqualityRequiredExecution.requireAll r h
          (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values scanned.native.machine.heap =
          .done prepared preparedHeap ∧
        SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared
          (advanceHeap scanned preparedHeap) memo = .done results after current ∧
        saved = scanFourth := by
  cases checked : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message =>
      simp only [reduce, checked] at actual
      cases actual
  | ok branch =>
      cases branch with
      | unchanged =>
          simp only [reduce, checked] at actual
          cases actual
          exact Or.inl rfl
      | emptyChildren =>
          simp only [reduce, checked] at actual
          cases actual
          exact Or.inr (Or.inl rfl)
      | classes records =>
          have completed : classes g s r e p h m c n budget records values
              (prefixState before loaded inherited) fourth memo = .done results after saved current := by
            simpa only [reduce, checked, SourceCurrentAllocatedPrecheck.state] using actual
          obtain ⟨selection, scanned, scanFourth, scanMemo, first, later⟩ :=
            (bind_done_iff _ _ _ _ _ _).mp completed
          obtain ⟨scanCall, sameMemo⟩ := scan_done_iff.mp first
          cases selection with
          | mk stopped kept =>
              cases stopped with
              | some paths =>
                  cases later
                  exact Or.inr (Or.inl rfl)
              | none =>
                  by_cases empty : kept = []
                  · subst kept
                    have noPaths : SourceEqualitySelectedRequired.paths ([] : Constraints) = [] := by
                      simp [SourceEqualitySelectedRequired.paths, canonicalClass]
                    simp only [List.map_nil, noPaths, required,
                      SourceEqualityRequiredExecution.requireAll_identity, Outcome.bind,
                      pass, SourceCurrentAllocatedClassWorker.pass_nil] at later
                    cases later
                    rcases SourceEqualityPartialInheritedPlainPass.propagate_shape values with original | erased
                    · exact Or.inl original
                    · exact Or.inr (Or.inl erased)
                  · obtain ⟨prepared, preparedBefore, nextFourth, warm, requiredDone, passDone⟩ :=
                      (bind_done_iff _ _ _ _ _ _).mp later
                    obtain ⟨preparedHeap, requiredCall, preparedSame, nextSame, warmSame⟩ :=
                      required_done_iff.mp requiredDone
                    obtain ⟨passCall, sameFourth⟩ := pass_done_iff.mp passDone
                    have finalPass : SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared
                        (advanceHeap scanned preparedHeap) memo = .done results after current := by
                      simpa only [preparedSame, warmSame, sameMemo] using passCall
                    exact Or.inr (Or.inr ⟨records, kept, scanned, scanFourth, prepared, preparedHeap,
                      rfl, scanCall, empty, requiredCall, finalPass, sameFourth.trans nextSame⟩)


end Local

open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentLowerProbeHeap (Good)
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
    (first : SourceCurrentAllocatedSharedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedSharedParentWorker.Outcome B width)
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
    (actual : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget symbol original inherited children
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
        SourceCurrentAllocatedSharedLocalWorker.reduce g s r e p h m c n budget loaded inherited children
          before fourth memo = .done returned.children middle saved current ∧
        SourceCurrentAllocatedMkEdge.build symbol loaded returned.children middle = (.ok returned, after) ∧
        SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
          returned.children.length = true ∧
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
          .ok (.classes records) ∧
        SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget children records
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
      simp only [SourceCurrentAllocatedSharedParentWorker.edge, rejected, ite_true] at actual
      cases actual
      exact Or.inr (Or.inr (Or.inl (SourceCurrentActualParentRowOrigins.reject_children symbol before good.toGood)))
  | false =>
      obtain ⟨field, inheritedReady, available⟩ := live rejected
      simp only [SourceCurrentAllocatedSharedParentWorker.edge, rejected, Bool.false_eq_true, ite_false] at actual
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
              have reduced : SourceCurrentAllocatedSharedLocalWorker.reduce g s r e p h m c n budget loaded inherited
                  children before fourth memo = .done values middle completed warm := by
                cases observed : SourceCurrentAllocatedSharedLocalWorker.reduce g s r e p h m c n budget loaded inherited
                    children before fourth memo with
                | failed => simp only [SourceCurrentAllocatedSharedParentWorker.reduceChildren, observed] at first; cases first
                | done output checked next current =>
                    simp only [SourceCurrentAllocatedSharedParentWorker.reduceChildren, observed] at first
                    cases first
                    rfl
              obtain ⟨effect, _, known⟩ := SourceCurrentSharedParentProbeHeap.reduce reduced good stored
                properties.1 inheritedReady available
              cases observed : SourceCurrentAllocatedMkEdge.build symbol loaded values middle with
              | mk built checked =>
                  cases built with
                  | error => simp only [SourceCurrentAllocatedSharedParentWorker.build, observed] at last; cases last
                  | ok value =>
                      simp only [SourceCurrentAllocatedSharedParentWorker.build, observed] at last
                      cases last
                      have fields := SourceCurrentActualParentRowOrigins.build_children observed effect.good.toGood
                        (properties.1.grows effect.operations.constraint_growth) known
                      cases keep : SourceEqualityMkEdgeAllocation.accepted
                          (SourceEqualityConjoinAllocation.readback loaded) values.length with
                      | false =>
                          simp only [keep, Bool.false_eq_true, ite_false] at fields
                          exact Or.inr (Or.inr (Or.inl fields))
                      | true =>
                          simp only [keep, ite_true] at fields
                          rcases Local.reduce_cases reduced with originalChildren | erased | selected
                          · exact Or.inl (fields.trans originalChildren)
                          · exact Or.inr (Or.inl (fields.trans erased))
                          · obtain ⟨records, kept, scanned, scanFourth, prepared, preparedHeap,
                              precheck, scanCall, nonempty, requiredCall, passCall, sameFourth⟩ := selected
                            refine Or.inr (Or.inr (Or.inr ⟨loaded, middle, records, kept, scanned, scanFourth,
                              prepared, preparedHeap, rfl, rfl, ?_, ?_, ?_, precheck, scanCall,
                              nonempty, requiredCall, ?_, sameFourth⟩))
                            · simpa only [fields] using reduced
                            · simpa only [fields] using observed
                            · simpa only [fields] using keep
                            · simpa only [fields] using passCall


end MicroCFTA.SourceCurrentSharedActualParentBranchCases
