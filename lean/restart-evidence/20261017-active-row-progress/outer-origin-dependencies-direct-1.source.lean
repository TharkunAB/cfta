import MicroCFTA.SourceCurrentEqualityDependencyDescent
import MicroCFTA.SourceCurrentEqualityOperationFixed

/-!
# Original class dependencies in actual child requests

Actual combination retains every nontrivial input class inside a normalized
component. A strict-prefix dependency prevents two such components from
merging in a consistent result. If the first component survives child
descent, the dependent component also survives with the same dependency.
These facts do not rank all active outer owners.
-/
namespace MicroCFTA.SourceCurrentOuterOriginDependencies
open EqualityNormalize SourceEqualityClassOrder SourceEqualityDescend
open SourceEqualityConstraintAllocation
open SourceCurrentEqualityNormalizationFixed (Fixed)
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

private theorem fix_covers (fuel : Nat) (classes output : Constraints)
    (actual : fixMaybe fuel classes = .normalized output) : Covers classes output := by
  induction fuel generalizing classes with
  | zero => cases actual
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp only [fixMaybe, stepped] at actual
      | some next =>
          by_cases same : next = classes
          · subst next
            have equal : classes = output := by simpa only [fixMaybe, stepped, if_pos rfl, RunResult.normalized.injEq] using actual
            subst output
            exact fun paths member => ⟨paths, member, fun _ present => present⟩
          · have tail : fixMaybe fuel next = .normalized output := by
              simpa only [fixMaybe, stepped, if_neg same] using actual
            exact covers_trans classes next output
              (EqualitySaturation.step_covers classes next stepped) (ih next tail)

/-- Actual source normalization retains every active input class inside one output component. -/
theorem normalize_covers (classes output : Constraints)
    (actual : SourceCompactGuards.normalize classes = some output) (active : Active classes) :
    Covers classes output := by
  have normalized : mkEqConstraints (EqualityTermination.normalizationBound classes) classes = .normalized output := by
    unfold SourceCompactGuards.normalize at actual
    rw [SourceCompactGuards.arrayNormalize_eq] at actual
    cases result : mkEqConstraints (EqualityTermination.normalizationBound classes) classes with
    | timeout | contradiction => simp only [result, SymbolicEqualityBridge.resultClasses] at actual
    | normalized found =>
        have equal : found = output := Option.some.inj actual
        exact equal ▸ result
  have prepared : Covers classes (prepare classes) := by
    intro paths member
    have nontrivial : Nontrivial paths.eraseDups := by
      obtain ⟨left, first, right, second, different⟩ := active paths member
      exact ⟨left, List.mem_eraseDups.mpr first, right, List.mem_eraseDups.mpr second, different⟩
    exact ⟨paths.eraseDups, List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨paths, member, rfl⟩, (nontrivialB_correct _).mpr nontrivial⟩,
      fun _ present => List.mem_eraseDups.mpr present⟩
  exact covers_trans classes (prepare classes) output prepared
    (covers_trans (prepare classes) (complete (prepare classes)) output
      (complete_covers _) (fix_covers _ _ _ normalized))

private theorem combined_covers (first second output : Constraints)
    (actual : SourceCompactGuards.combineEqualities (some first) (some second) = some output)
    (active : Active (first ++ second)) : Covers (first ++ second) output := by
  cases first with
  | nil =>
      cases second with
      | nil =>
          intro paths member
          cases member
      | cons head tail => exact normalize_covers _ _ actual active
  | cons head tail => cases second <;> exact normalize_covers _ _ actual active

private theorem ready_active (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (value : Value) (ready : Ready cache value) :
    Active ((SourceEqualityInheritedPayload.classes value.payload).getD []) := by
  cases value with
  | contradiction => intro paths member; cases member
  | live identity originals =>
      intro paths member
      obtain ⟨record, included, rfl⟩ := List.mem_map.mp member
      exact (ready.2 originals rfl record included).2.2

/-- Initial Ready operands construct their own combined value and its original-class coverage. -/
theorem combine_covers (first second : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first) (secondReady : Ready before.constraints second) :
    ∃ combined,
      (SourceEqualityConstraintMemoAllocation.combine first second before).1 = .ok combined ∧
      let middle := (SourceEqualityConstraintMemoAllocation.combine first second before).2
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before middle ∧
      SourceCurrentEqualityOperationFixed.FixedPayload combined.payload ∧
      ∀ outputs, combined.payload = some outputs →
        Covers ((SourceEqualityInheritedPayload.classes first.payload).getD [] ++
          (SourceEqualityInheritedPayload.classes second.payload).getD []) (outputs.map Record.paths) := by
  obtain ⟨combined, actual, finalValid, combinedReady, growth, fixed⟩ :=
    SourceCurrentEqualityOperationFixed.combine first second before valid firstReady secondReady
  obtain ⟨other, otherActual, _, _, payload, _⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct first second before valid firstReady secondReady
  have same : other = combined := Except.ok.inj (otherActual.symm.trans actual)
  subst other
  refine ⟨combined, actual, finalValid, combinedReady, growth, fixed, ?_⟩
  intro outputs live
  have readback := read_classes _ (SourceEqualityGuardReadback.combine_cached _ _) _ payload
  rw [live] at readback
  cases first with
  | contradiction => cases second <;> cases readback
  | live firstIdentity firstRecords =>
      cases second with
      | contradiction => cases readback
      | live secondIdentity secondRecords =>
          have active : Active (firstRecords.map Record.paths ++ secondRecords.map Record.paths) := by
            intro paths member
            rcases List.mem_append.mp member with member | member
            · exact ready_active _ _ firstReady paths member
            · exact ready_active _ _ secondReady paths member
          exact combined_covers _ _ _ readback.symm active

private theorem covers_dependency (inputs : Constraints) (outputs : List Record)
    (covered : Covers inputs (outputs.map Record.paths))
    (consistent : isContradicting (outputs.map Record.paths) = false)
    (first second : Class) (firstMember : first ∈ inputs) (secondMember : second ∈ inputs)
    (dependent : Subsumes first second) :
    ∃ firstOutput ∈ outputs, ∃ secondOutput ∈ outputs,
      (∀ path ∈ first, path ∈ firstOutput.paths) ∧
      (∀ path ∈ second, path ∈ secondOutput.paths) ∧
      firstOutput ≠ secondOutput ∧ Subsumes firstOutput.paths secondOutput.paths := by
  obtain ⟨left, leftMember, firstIncluded⟩ := covered first firstMember
  obtain ⟨right, rightMember, secondIncluded⟩ := covered second secondMember
  obtain ⟨leftRecord, leftKnown, rfl⟩ := List.mem_map.mp leftMember
  obtain ⟨rightRecord, rightKnown, rfl⟩ := List.mem_map.mp rightMember
  have relation : Subsumes leftRecord.paths rightRecord.paths := by
    obtain ⟨base, baseMember, extension, extensionMember, prefix, different⟩ := dependent
    exact ⟨base, firstIncluded _ baseMember, extension, secondIncluded _ extensionMember, prefix, different⟩
  refine ⟨leftRecord, leftKnown, rightRecord, rightKnown, firstIncluded, secondIncluded, ?_, relation⟩
  intro same
  subst rightRecord
  exact consistent_subsumption_irreflexive _ consistent _
    (List.mem_map.mpr ⟨leftRecord, leftKnown, rfl⟩) relation

/-- Original dependencies survive actual combination and every retained indexed child request. -/
theorem combine_descend_dependencies (first second : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first) (secondReady : Ready before.constraints second) :
    ∃ combined,
      (SourceEqualityConstraintMemoAllocation.combine first second before).1 = .ok combined ∧
      let middle := (SourceEqualityConstraintMemoAllocation.combine first second before).2
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before middle ∧
      ∀ outputs, combined.payload = some outputs →
      ∀ left ∈ ((SourceEqualityInheritedPayload.classes first.payload).getD [] ++
        (SourceEqualityInheritedPayload.classes second.payload).getD []),
      ∀ right ∈ ((SourceEqualityInheritedPayload.classes first.payload).getD [] ++
        (SourceEqualityInheritedPayload.classes second.payload).getD []),
      Subsumes left right →
      ∃ leftRecord ∈ outputs, ∃ rightRecord ∈ outputs,
        (∀ path ∈ left, path ∈ leftRecord.paths) ∧
        (∀ path ∈ right, path ∈ rightRecord.paths) ∧
        leftRecord ≠ rightRecord ∧ Subsumes leftRecord.paths rightRecord.paths ∧
        ∀ index leftChild, record index leftRecord = some leftChild →
          let descended := SourceEqualityConstraintMemoAllocation.descend combined index middle
          SourceEqualityConstraintMemoAllocation.Valid descended.2 ∧
          Ready descended.2.constraints descended.1 ∧
          SourceEqualityConstraintMemoAllocation.Grows middle descended.2 ∧
          SourceCurrentEqualityOperationFixed.FixedPayload descended.1.payload ∧
          descended.1.payload = some (records index outputs) ∧
          leftChild ∈ records index outputs ∧
          ∃ rightChild ∈ records index outputs,
            record index rightRecord = some rightChild ∧
            leftChild ≠ rightChild ∧ Subsumes leftChild.paths rightChild.paths := by
  obtain ⟨combined, actual, finalValid, combinedReady, growth, fixed, covered⟩ :=
    combine_covers first second before valid firstReady secondReady
  refine ⟨combined, actual, finalValid, combinedReady, growth, ?_⟩
  intro outputs live left leftMember right rightMember dependent
  have wellFormed : WellFormed (some outputs) := live ▸ combinedReady.2
  have outputFixed := fixed outputs live
  obtain ⟨leftRecord, leftKnown, rightRecord, rightKnown, leftIncluded, rightIncluded, different, relation⟩ :=
    covers_dependency _ outputs (covered outputs live) (invariants _ outputFixed).2.1
      left right leftMember rightMember dependent
  refine ⟨leftRecord, leftKnown, rightRecord, rightKnown, leftIncluded, rightIncluded, different, relation, ?_⟩
  intro index leftChild leftRead
  have checked := SourceCurrentEqualityOperationFixed.descend combined index _ finalValid combinedReady fixed
  have payload := (SourceEqualityConstraintMemoAllocation.descend_correct combined index _ finalValid combinedReady).2.2.1
  have exactPayload : (SourceEqualityConstraintMemoAllocation.descend combined index
      (SourceEqualityConstraintMemoAllocation.combine first second before).2).1.payload = some (records index outputs) := by
    rw [payload, live]
    cases outputs <;> rfl
  obtain ⟨rightChild, rightRead, rightPresent, childRelation⟩ :=
    SourceCurrentEqualityDependencyDescent.retained outputs wellFormed outputFixed index leftRecord rightRecord
      leftKnown rightKnown relation leftChild leftRead
  have childDifferent : leftChild ≠ rightChild := by
    intro same
    subst rightChild
    have childConsistent := SourceCurrentEqualityDescendFixed.records_consistent outputs wellFormed
      (invariants _ outputFixed).2.1 index
    exact consistent_subsumption_irreflexive _ childConsistent _
      (List.mem_map.mpr ⟨leftChild, rightPresent, rfl⟩) childRelation
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2, exactPayload,
    (records_perm index outputs).mem_iff.mpr (List.mem_filterMap.mpr ⟨leftRecord, leftKnown, leftRead⟩),
    rightChild, rightPresent, rightRead, childDifferent, childRelation⟩

end MicroCFTA.SourceCurrentOuterOriginDependencies
