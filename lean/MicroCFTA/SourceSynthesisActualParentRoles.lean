import MicroCFTA.SourceCurrentActualParentRowOrigins
import MicroCFTA.SourceCurrentInheritedConstraintRegions
import MicroCFTA.SourceEqualityClassEdits
import MicroCFTA.SourceSynthesisGuardRegions

/-!
# Source occurrence roles through actual Parent returns

Actual application and filter guards derive physical edit footprints. Both
prefix directions are excluded at each non-annotation continuation child.
Completed Parent calls retain indexed row links and the original guard
region. Source occurrence equations establish the roles.
-/
namespace MicroCFTA.SourceSynthesisActualParentRoles
open InternedConstructorTemplates EqualityNormalize
open InternedNestedProvenance (Values)
open SourceSynthesisGeneralizeSyntax (Guard eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceSynthesisGuardRegions SourceEqualityConstraintRegions
open SourceCurrentActualRequiredRowOrigins (Link)
open SourceCurrentClassPositionalFootprints (Unselected)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap Plain

private theorem eqGuard_cached (classes : Constraints) :
    SourceEqualityGuardReadback.Cached (eqGuard classes).equalities := by
  rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
  exact SourceEqualityGuardReadback.normalize_cached classes

private theorem own_within (region : Path → Prop) (guard : Guard)
    (cached : SourceEqualityGuardReadback.Cached guard.equalities)
    (endpoints : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), region path)
    (originals : List Record) (ownDone : SourceEqualityPhysicalPayload.own guard = .ok (some originals)) :
    ∀ record ∈ originals, ∀ path ∈ record.paths, region path := by
  change Within region (some originals)
  apply read_preserves region (SourceCompactGuards.sourceEqualities guard)
    (SourceEqualityGuardReadback.source_cached guard cached) ?_ (some originals) ownDone
  intro classes same path member
  apply endpoints path
  simpa only [same, Option.getD] using member

private theorem signed_disjoint (path target : Path)
    (natural : ¬ path.IsPrefix target ∧ ¬ target.IsPrefix path) :
    SourceEqualityEditCompiledPaths.Disjoint (path.map Int.ofNat) (target.map Int.ofNat) :=
  ⟨fun initial => natural.1 ((SourceEqualityClassEdits.signed_prefix path target).mp initial),
    fun initial => natural.2 ((SourceEqualityClassEdits.signed_prefix target path).mp initial)⟩

private theorem application_disjoint (path : Path) (inside : applicationRegion path)
    (index childIndex : Nat) (programSlot : index = 2 ∨ index = 3) (nonzero : childIndex ≠ 0) :
    SourceEqualityEditCompiledPaths.Disjoint (path.map Int.ofNat) [Int.ofNat index, Int.ofNat childIndex] := by
  have opposite : 0 ≠ childIndex := Ne.symm nonzero
  apply signed_disjoint path [index, childIndex]
  rcases programSlot with rfl | rfl
  · rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;>
      simp_all [List.cons_prefix_cons]
  · rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;>
      simp_all [List.cons_prefix_cons]

private theorem filter_disjoint (path : Path) (inside : filterRegion path)
    (childIndex : Nat) (nonzero : childIndex ≠ 0) :
    SourceEqualityEditCompiledPaths.Disjoint (path.map Int.ofNat) [1, Int.ofNat childIndex] := by
  have opposite : 0 ≠ childIndex := Ne.symm nonzero
  apply signed_disjoint path [1, childIndex]
  rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;> simp_all [List.cons_prefix_cons]

variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A source application occurrence derives Parent row origins without a supplied edit footprint. -/
theorem application_parent (types function argument : Expression)
    (sourceName : String) (guard : Guard) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    {g s r e p h m c n budget symbol inherited children before fourth memo returned after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol guard inherited children
      before fourth memo = .done returned after saved current)
    (good : Good (width := width) (before : Checked width))
    (stored : Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory guard = false →
      FieldAvailable before.operations guard ∧ EqReady before.operations.constraints inherited ∧
        Values before.native.machine.heap children)
    (guards : GuardHeap before.native.machine.heap) (index childIndex : Nat)
    (programSlot : index = 2 ∨ index = 3) (nonzero : childIndex ≠ 0)
    {source result : Node} (input : children[index]? = some source)
    (output : returned.children[index]? = some result) :
    Link childIndex source result ∧
      ∀ path ∈ members ((SourceCompactGuards.sourceEqualities returned.entry.key.constraint).getD []),
        applicationRegion path := by
  have cached : SourceEqualityGuardReadback.Cached guard.equalities := by
    cases occurrence
    exact eqGuard_cached [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]]
  have endpoints := (application_guard_endpoints types function argument sourceName guard sourceChildren occurrence).2
  have footprint : ∀ originals : List Record, SourceEqualityPhysicalPayload.own guard = .ok (some originals) →
      ∀ record ∈ originals, Unselected record index childIndex := by
    intro originals ownDone record present path found
    exact application_disjoint path
      (own_within applicationRegion guard cached endpoints originals ownDone record present path found)
      index childIndex programSlot nonzero
  have linked := SourceCurrentActualParentRowOrigins.edge actual good stored live guards index childIndex footprint input output
  have fields := SourceCurrentOuterRowFieldOrigins.parent actual good stored live
  exact ⟨linked, SourceCurrentInheritedConstraintRegions.fields_preserve applicationRegion fields endpoints⟩

/-- A source filter occurrence derives Parent row origins without a supplied edit footprint. -/
theorem filter_parent (candidates goal : Expression)
    (sourceName : String) (guard : Guard) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    {g s r e p h m c n budget symbol inherited children before fourth memo returned after saved current}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol guard inherited children
      before fourth memo = .done returned after saved current)
    (good : Good (width := width) (before : Checked width))
    (stored : Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory guard = false →
      FieldAvailable before.operations guard ∧ EqReady before.operations.constraints inherited ∧
        Values before.native.machine.heap children)
    (guards : GuardHeap before.native.machine.heap) (childIndex : Nat) (nonzero : childIndex ≠ 0)
    {source result : Node} (input : children[1]? = some source)
    (output : returned.children[1]? = some result) :
    Link childIndex source result ∧
      ∀ path ∈ members ((SourceCompactGuards.sourceEqualities returned.entry.key.constraint).getD []),
        filterRegion path := by
  have cached : SourceEqualityGuardReadback.Cached guard.equalities := by
    cases occurrence
    exact eqGuard_cached [[[0], [1, 0]]]
  have endpoints := (filter_guard_endpoints candidates goal sourceName guard sourceChildren occurrence).2
  have footprint : ∀ originals : List Record, SourceEqualityPhysicalPayload.own guard = .ok (some originals) →
      ∀ record ∈ originals, Unselected record 1 childIndex := by
    intro originals ownDone record present path found
    exact filter_disjoint path
      (own_within filterRegion guard cached endpoints originals ownDone record present path found)
      childIndex nonzero
  have linked := SourceCurrentActualParentRowOrigins.edge actual good stored live guards 1 childIndex footprint input output
  have fields := SourceCurrentOuterRowFieldOrigins.parent actual good stored live
  exact ⟨linked, SourceCurrentInheritedConstraintRegions.fields_preserve filterRegion fields endpoints⟩

end MicroCFTA.SourceSynthesisActualParentRoles
