import MicroCFTA.SourceCurrentAllocatedNativeInventoryState

/-!
# Actual pre-query inventory rebase

The new inventory uses the current constructor heap and two closed resident
operands. Actual record growth retains each old root and its exact ranks.
The same native cells and equality operations remain at this query entry.
No query execution or future range condition is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeInventoryRebase
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Actual heap growth and two current operands determine the expanded input inventory. -/
def extend (inventory : Inventory) (target : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts target) (growth : Grows inventory.source target)
    (history : Extends inventory.source.nodes.issued target.nodes.issued)
    (left right : Value Symbol Guard) (leftAvailable : Available target left) (rightAvailable : Available target right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) : Inventory := by
  let roots := inventory.roots ++ [left, right]
  have available : Values target roots := by
    intro root member
    rcases List.mem_append.mp member with old | next
    · exact (inventory.available root old).grows inventory.source target growth history
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at next
      rcases next with rfl | rfl
      · exact leftAvailable
      · exact rightAvailable
  have closed : ∀ root ∈ roots, root.free = [] := by
    intro root member
    rcases List.mem_append.mp member with old | next
    · exact inventory.closed root old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at next
      rcases next with rfl | rfl
      · exact leftClosed
      · exact rightClosed
  exact ⟨target, facts, roots,
    SourceCurrentAllocatedNativeGrownInventory.closed_originals target facts roots available closed, available, closed⟩

/-- The expanded model retains all actual memo admission and contextual laws before the next query starts. -/
theorem rebase
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before) (current : At formulas solver inventory before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    let next := extend inventory before.native.machine.heap good.native.machine.1 current.growth current.history
      left right leftAvailable rightAvailable leftClosed rightClosed
    At formulas solver next before ∧
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      (next.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf left) ∧
      (next.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf right) := by
  let target := before.native.machine.heap
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let next := extend inventory target good.native.machine.1 current.growth current.history
    left right leftAvailable rightAvailable leftClosed rightClosed
  have included : ∀ root ∈ inventory.roots, root ∈ next.roots := fun _ member => List.mem_append.mpr (Or.inl member)
  have agreement : SourceCurrentAllocatedNativeContextRebase.Agreement (inventory.inputs holds) (next.inputs holds) :=
    SourceCurrentAllocatedNativeAdmittedQuery.inventory_agreement inventory.source target inventory.facts good.native.machine.1
      current.growth current.history holds inventory.roots inventory.originals inventory.available inventory.closed
      next.roots next.available next.closed included
  have contextual := SourceCurrentAllocatedNativeContextRebase.contextual agreement holds before.native
    current.covered.admitted current.covered.seen_admitted current.contextual
  have covered := current.covered.rebase agreement
  have admitted : At formulas solver next before := ⟨contextual, covered, grows_refl target, extends_refl target.nodes.issued⟩
  have leftMember : left ∈ next.roots := by change left ∈ inventory.roots ++ [left, right]; simp
  have rightMember : right ∈ next.roots := by change right ∈ inventory.roots ++ [left, right]; simp
  exact ⟨admitted, rfl, rfl,
    SourceCurrentAllocatedNativeInputInventoryModels.root_valid target good.native.machine.1 holds next.roots
      next.originals next.available next.closed left leftMember,
    SourceCurrentAllocatedNativeInputInventoryModels.root_valid target good.native.machine.1 holds next.roots
      next.originals next.available next.closed right rightMember⟩

end MicroCFTA.SourceCurrentAllocatedNativeInventoryRebase
