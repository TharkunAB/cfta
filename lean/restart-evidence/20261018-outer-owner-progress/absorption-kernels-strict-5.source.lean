import MicroCFTA.SourceCurrentAllocatedEqualityAbsorption
import MicroCFTA.SourceCurrentOuterEffectiveGain

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 10000000

namespace MicroCFTA.EqualityAbsorptionKernels
open Cache EqualityNormalize SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

private theorem array_small (classes : Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 4 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 4 classes
attribute [local cbv_eval] array_small

private def inheritedClasses : Constraints := [[[0],[1],[2]]]
private def ownClasses : Constraints := [[[0],[1]]]
private def original : Guard := ⟨some ownClasses,.top⟩
private def value (result : Except String Value) : Value :=
  match result with | .ok result => result | .error _ => .contradiction
private def first := construct (some inheritedClasses) Cache.emptyState
private def inherited := value first.1
private def second := construct original.equalities first.2
private def own := value second.1
private def before : Operations := SourceEqualityConstraintMemoAllocation.initial second.2
private def identity : Nat := inherited.identity.getD 0
private def records : List Record := inherited.payload.getD []

private theorem inherited_cached : SourceEqualityGuardReadback.Cached (some inheritedClasses) := by
  have actual : mkEqConstraints 1 inheritedClasses = .normalized inheritedClasses := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized actual
private theorem own_cached : SourceEqualityGuardReadback.Cached original.equalities := by
  have actual : mkEqConstraints 1 ownClasses = .normalized ownClasses := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized actual

private theorem allocation (classes : Option Constraints) (cached : SourceEqualityGuardReadback.Cached classes)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid cache) :
    construct classes cache = (.ok (value (construct classes cache).1),(construct classes cache).2) ∧
      Cache.Valid (construct classes cache).2 ∧ Ready (construct classes cache).2 (value (construct classes cache).1) ∧
      Cache.Steps cache (construct classes cache).2 ∧
      SourceEqualityPhysicalPayload.read classes = .ok (value (construct classes cache).1).payload := by
  obtain ⟨result,after,actual,valid,ready,steps,read,_⟩ := construct_complete classes cached cache valid
  rw [actual]
  exact ⟨rfl,valid,ready,steps,read⟩

private theorem initial : SourceEqualityConstraintMemoAllocation.Valid before ∧
    Ready before.constraints inherited ∧ SourceCurrentConjunctionEquality.FieldAvailable before original := by
  have one := allocation (some inheritedClasses) inherited_cached Cache.emptyState Cache.empty_valid
  have two := allocation original.equalities own_cached first.2 one.2.1
  have inheritedReady : Ready second.2 inherited :=
    one.2.2.1.grows (Cache.steps_table_extends two.2.2.2.1)
  have loaded := SourceEqualityConstraintFieldLookup.load_of_receipt original second.2 own_cached
    own two.2.2.2.2 two.2.2.1
  exact ⟨SourceEqualityConstraintMemoAllocation.initial_valid _ two.2.1,inheritedReady,
    own_cached,⟨own,original.guard⟩,loaded.1⟩

private theorem fixed : SourceCurrentEqualityNormalizationFixed.Fixed (records.map Record.paths) := by
  have same : records.map Record.paths = inheritedClasses := by cbv
  rw [same]
  apply SourceCurrentEqualityNormalizationFixed.of_step
  · intro paths member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[0],by simp,[1],by simp,by decide⟩
  · cbv

private theorem covered : Covers ownClasses (records.map Record.paths) := by
  have same : records.map Record.paths = inheritedClasses := by cbv
  rw [same]
  intro paths member
  obtain rfl := List.mem_singleton.mp member
  refine ⟨[[0],[1],[2]],List.mem_cons_self,?_⟩
  intro path member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
  rcases member with rfl | rfl <;> simp

private noncomputable def cold := SourceCurrentAllocatedInheritedPrefix.run original inherited before
private noncomputable def warm := SourceCurrentAllocatedInheritedPrefix.run original inherited cold.2
private noncomputable def child := SourceEqualityConstraintMemoAllocation.descend inherited 0 cold.2

private theorem nonempty : records ≠ [] := by
  intro same
  have size : records.length = 1 := by cbv
  rw [same] at size
  cases size

private theorem checked :
    SourceEqualityConstraintMemoAllocation.Valid before ∧ Ready before.constraints inherited ∧
    original.equalities = some [[[0],[1]]] ∧ records.map Record.paths = [[[0],[1],[2]]] ∧
    records ≠ [] ∧ SourceCompactGuards.sourceEqualities original = some ownClasses ∧
    Covers ownClasses (records.map Record.paths) ∧
    cold.1 = .ok (some inherited) ∧ warm = (.ok (some inherited),cold.2) ∧
    SourceCurrentOuterInheritedDescent.pathHeight child.1 < SourceCurrentOuterInheritedDescent.pathHeight inherited ∧
    child.1.identity ≠ inherited.identity := by
  have shape : inherited = .live identity records := by cbv
  have inheritedReady : Ready before.constraints (.live identity records) := shape ▸ initial.2.1
  have compiled : SourceCompactGuards.sourceEqualities original = some ownClasses := by cbv
  have prefixDone := SourceCurrentAllocatedEqualityAbsorption.inherited_prefix original identity records ownClasses
    before initial.1 inheritedReady initial.2.2 compiled fixed covered
  have descending := SourceCurrentAllocatedEqualityAbsorption.descend original identity records ownClasses 0
    before initial.1 inheritedReady initial.2.2 compiled fixed covered nonempty
  refine ⟨initial.1,initial.2.1,rfl,by cbv,nonempty,
    compiled,covered,?_,?_,?_,?_⟩
  · simpa only [cold,← shape] using prefixDone.1
  · cbv
  · simpa only [child,cold,← shape] using descending.2.1
  · rw [show inherited.identity = some identity by cbv]
    simpa only [child,cold,← shape] using descending.2.2

/-- A nonempty covered own class preserves actual cold and warm values before strict descent. -/
theorem actual_covered_nonempty_own :
    SourceEqualityConstraintMemoAllocation.Valid before ∧ Ready before.constraints inherited ∧
    original.equalities = some [[[0],[1]]] ∧ records.map Record.paths = [[[0],[1],[2]]] ∧
    records ≠ [] ∧ SourceCompactGuards.sourceEqualities original = some ownClasses ∧
    Covers ownClasses (records.map Record.paths) ∧
    cold.1 = .ok (some inherited) ∧ warm = (.ok (some inherited),cold.2) ∧
    SourceCurrentOuterInheritedDescent.pathHeight child.1 < SourceCurrentOuterInheritedDescent.pathHeight inherited ∧
    child.1.identity ≠ inherited.identity := checked

private def topRun := construct (some []) before.constraints
private def topValue := value topRun.1
private def topBefore : Operations := SourceEqualityConstraintMemoAllocation.initial topRun.2

private theorem top_checked :
    SourceEqualityConstraintMemoAllocation.Valid topBefore ∧ Ready topBefore.constraints topValue ∧
    topValue.payload = some [] ∧
    (SourceCurrentAllocatedInheritedPrefix.run original topValue topBefore).1 = .ok (some own) ∧
    SourceCurrentOuterInheritedDescent.pathHeight topValue < SourceCurrentOuterInheritedDescent.pathHeight own ∧
    SourceCurrentOuterEffectiveGain.NewPair original topValue := by
  have emptyCached : SourceEqualityGuardReadback.Cached (some []) := SourceEqualityGuardReadback.empty_cached
  have allocated := allocation (some []) emptyCached before.constraints initial.1.constraints
  have valid := SourceEqualityConstraintMemoAllocation.initial_valid _ allocated.2.1
  have ready : Ready topBefore.constraints topValue := allocated.2.2.1
  have field : SourceCurrentConjunctionEquality.FieldAvailable topBefore original :=
    ⟨own_cached,⟨own,original.guard⟩,by cbv⟩
  have fixed : SourceCurrentEqualityOperationFixed.FixedPayload topValue.payload := by
    intro outputs shape
    have same : topValue.payload = some [] := by cbv
    rw [same] at shape
    cases shape
    apply SourceCurrentEqualityNormalizationFixed.of_step
    · intro paths impossible
      cases impossible
    · cbv
  have actual : (SourceCurrentAllocatedInheritedPrefix.run original topValue topBefore).1 = .ok (some own) := by cbv
  have increase : SourceCurrentOuterInheritedDescent.pathHeight topValue <
      SourceCurrentOuterInheritedDescent.pathHeight own := by cbv
  exact ⟨valid,ready,by cbv,actual,increase,
    SourceCurrentOuterEffectiveGain.inherited_prefix actual valid ready field fixed increase⟩

/-- An actual empty-inherited prefix derives a new pair from its nonempty own class. -/
theorem actual_new_pair :
    SourceEqualityConstraintMemoAllocation.Valid topBefore ∧ Ready topBefore.constraints topValue ∧
    topValue.payload = some [] ∧
    (SourceCurrentAllocatedInheritedPrefix.run original topValue topBefore).1 = .ok (some own) ∧
    SourceCurrentOuterInheritedDescent.pathHeight topValue < SourceCurrentOuterInheritedDescent.pathHeight own ∧
    SourceCurrentOuterEffectiveGain.NewPair original topValue := top_checked

end MicroCFTA.EqualityAbsorptionKernels
