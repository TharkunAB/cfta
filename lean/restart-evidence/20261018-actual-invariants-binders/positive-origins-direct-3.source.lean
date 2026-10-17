import MicroCFTA.SourceCurrentOwnClassOrigin
import MicroCFTA.SourceEqualityGuardAllocation

/-!
# Raw positive-guard classes through actual staged normalization

The source parser emits each positive Same pair before normalization.
Actual staged normalization retains every emitted pair in one live output
component, or returns contradiction. Actual demand retains that coverage.
-/
namespace MicroCFTA.SourceCurrentPositiveClassOrigins
open EqualityNormalize SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Guard" => SourceGuards.Guard FullSyntax.Formula
local notation "Field" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

/-- Live combination retains every class from both active input lists. -/
theorem combine_covers (first second output : Constraints)
    (firstActive : Active first) (secondActive : Active second)
    (actual : SourceCompactGuards.combineEqualities (some first) (some second) = some output) :
    Covers (first ++ second) output := by
  have active : Active (first ++ second) := by
    intro paths member
    rcases List.mem_append.mp member with member | member
    · exact firstActive paths member
    · exact secondActive paths member
  cases first with
  | nil =>
    cases second with
    | nil =>
      cases actual
      intro paths impossible
      cases impossible
    | cons head rest => exact SourceCurrentOuterOriginDependencies.normalize_covers _ _ actual active
  | cons head rest =>
    cases second <;> exact SourceCurrentOuterOriginDependencies.normalize_covers _ _ actual active

private theorem covers_append (first second left right : Constraints)
    (head : Covers first left) (tail : Covers second right) :
    Covers (first ++ second) (left ++ right) := by
  intro paths member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨component,present,included⟩ := head paths member
    exact ⟨component,List.mem_append_left _ present,included⟩
  · obtain ⟨component,present,included⟩ := tail paths member
    exact ⟨component,List.mem_append_right _ present,included⟩

mutual
/-- Actual positive guard normalization covers every pair from its raw syntax traversal. -/
theorem normalized_guard (guard : Guard) (raw : Constraints)
    (extracted : SourceCompactGuards.positive guard = some raw) (output : Constraints)
    (actual : SourceCompactGuards.positiveNormalized guard = some (some output)) :
    Covers raw output := by
  cases guard with
  | top =>
    have same : raw = [] := by simpa only [SourceCompactGuards.positive,Option.some.injEq] using extracted.symm
    subst raw
    intro paths impossible
    cases impossible
  | same left right =>
    simp only [SourceCompactGuards.positive] at extracted
    split at extracted
    · rename_i different
      have same := Option.some.inj extracted
      subst raw
      have finished : SourceCompactGuards.normalize [[left,right]] = some output := by
        simpa only [SourceCompactGuards.positiveNormalized,ite_eq_left different,Option.some.injEq] using actual
      exact SourceCurrentOuterOriginDependencies.normalize_covers _ _ finished
        (SourceCompactGuards.positive_active (.same left right : Guard) _
          (by simp only [SourceCompactGuards.positive,ite_eq_left different]))
    · cases extracted
  | and parts => exact normalized_list parts raw extracted output actual
  | bottom | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ | not _ | or _ => cases extracted

/-- The literal positive right fold retains raw origins through every intermediate normalization. -/
theorem normalized_list (guards : List Guard) (raw : Constraints)
    (extracted : SourceCompactGuards.positiveList guards = some raw) (output : Constraints)
    (actual : SourceCompactGuards.positiveNormalizedList guards = some (some output)) :
    Covers raw output := by
  cases guards with
  | nil =>
    have same : raw = [] := by simpa only [SourceCompactGuards.positiveList,Option.some.injEq] using extracted.symm
    subst raw
    intro paths impossible
    cases impossible
  | cons first rest =>
    simp only [SourceCompactGuards.positiveList,Bind.bind,Pure.pure,
      Option.bind_eq_some_iff,Option.some.injEq] at extracted
    obtain ⟨head,headDone,tail,tailDone,rfl⟩ := extracted
    obtain ⟨left,leftDone,leftActive,_⟩ := SourceCompactGuards.positiveNormalized_exact
      (Symbol := Unit) first head headDone
    obtain ⟨right,rightDone,rightActive,_⟩ := SourceCompactGuards.positiveNormalizedList_exact
      (Symbol := Unit) rest tail tailDone
    have combined : SourceCompactGuards.combineEqualities left right = some output := by
      simpa [SourceCompactGuards.positiveNormalizedList,leftDone,rightDone] using actual
    cases left with
    | none => cases right <;> cases combined
    | some left =>
      cases right with
      | none => cases combined
      | some right =>
        exact covers_trans _ _ _
          (covers_append head tail left right
            (normalized_guard first head headDone left leftDone)
            (normalized_list rest tail tailDone right rightDone))
          (combine_covers left right output (leftActive left rfl) (rightActive right rfl) combined)
end

/-- A live full-field accessor covers all raw classes emitted by its positive guard. -/
theorem source_guard (original : Field)
    (stored : SourceCompactGuards.ActiveOption original.equalities)
    (raw : Constraints) (extracted : SourceCompactGuards.positive original.guard = some raw)
    (output : Constraints) (actual : SourceCompactGuards.sourceEqualities original = some output) :
    Covers raw output := by
  obtain ⟨added,found,active,_⟩ := SourceCompactGuards.positiveNormalized_exact
    (Symbol := Unit) original.guard raw extracted
  cases added with
  | none =>
    cases cached : original.equalities <;>
      simp [SourceCompactGuards.sourceEqualities,found,cached,SourceCompactGuards.combineEqualities] at actual
  | some added =>
    have covered := normalized_guard original.guard raw extracted added found
    cases added with
    | nil =>
      intro paths member
      obtain ⟨component,impossible,_⟩ := covered paths member
      cases impossible
    | cons head rest =>
      have combined : SourceCompactGuards.combineEqualities original.equalities (some (head :: rest)) = some output := by
        simpa only [SourceCompactGuards.sourceEqualities,found] using actual
      cases cached : original.equalities with
      | none => rw [cached] at combined; cases combined
      | some own =>
        have retained := combine_covers own (head :: rest) output (stored own cached)
          (active (head :: rest) rfl) (by simpa only [cached] using combined)
        exact covers_trans _ _ _ covered
          (fun paths member => retained paths (List.mem_append_right _ member))

/-- Initial valid operations construct demanded positive classes and their raw origin coverage. -/
theorem demand (guard : Guard) (raw : Constraints)
    (extracted : SourceCompactGuards.positive guard = some raw) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before) :
    ∃ value,
      (SourceEqualityGuardAllocation.demandPositive guard before).1 = .ok (some value) ∧
      SourceEqualityConstraintMemoAllocation.Valid (SourceEqualityGuardAllocation.demandPositive guard before).2 ∧
      Ready (SourceEqualityGuardAllocation.demandPositive guard before).2.constraints value ∧
      SourceEqualityConstraintMemoAllocation.Grows before (SourceEqualityGuardAllocation.demandPositive guard before).2 ∧
      ∀ records, value.payload = some records → Covers raw (records.map Record.paths) := by
  obtain ⟨added,positive,_,_⟩ := SourceCompactGuards.positiveNormalized_exact
    (Symbol := Unit) guard raw extracted
  obtain ⟨result,done,afterValid,ready,classes,growth⟩ :=
    SourceEqualityGuardAllocation.positive_correct guard before valid
  cases result with
  | none => rw [positive] at classes; cases classes
  | some value =>
    refine ⟨value,done,afterValid,ready value rfl,growth,?_⟩
    intro records live
    apply normalized_guard guard raw extracted (records.map Record.paths)
    rw [← classes,Option.map_some,live]
    rfl

private theorem contradiction_prefix (original : Field) (input : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (contradictory : SourceCompactGuards.sourceEqualities original = none) :
    (SourceCurrentAllocatedInheritedPrefix.run original input before).1 = .ok (some .contradiction) := by
  cases input with
  | contradiction => rfl
  | live identity records =>
    obtain ⟨own,loaded,_,_,classes,_,_⟩ :=
      SourceCurrentConjunctionEquality.accessor_correct original before valid field
    have same : own = .contradiction := by
      cases own with
      | contradiction => rfl
      | live identity records =>
        simp only [SourceEqualityInheritedPayload.classes,Value.payload,Option.map_some] at classes
        rw [contradictory] at classes
        cases classes
    subst own
    rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before .contradiction loaded]
    rfl

/-- Initial positive syntax constructs a nonempty indexed child obligation without final class membership. -/
theorem field_split (original : Field) (input : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : Ready before.constraints input)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (raw : Constraints) (extracted : SourceCompactGuards.positive original.guard = some raw)
    (paths : Class) (selected : paths ∈ raw)
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right) :
    ∃ combined,
      (SourceCurrentAllocatedInheritedPrefix.run original input before).1 = .ok (some combined) ∧
      let middle := (SourceCurrentAllocatedInheritedPrefix.run original input before).2
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before middle ∧
      let child := SourceEqualityConstraintMemoAllocation.descend combined index middle
      SourceEqualityConstraintMemoAllocation.Valid child.2 ∧ Ready child.2.constraints child.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows middle child.2 ∧ child.1.payload ≠ some [] := by
  by_cases contradictory : SourceCompactGuards.sourceEqualities original = none
  · obtain ⟨combined,actual,middleValid,combinedReady,growth,childValid,childReady,childGrowth,_⟩ :=
      SourceCurrentEqualityOperationFixed.prefix_descend original input index before valid ready field
    have same : combined = .contradiction :=
      Option.some.inj (Except.ok.inj (actual.symm.trans (contradiction_prefix original input before valid field contradictory)))
    subst combined
    exact ⟨.contradiction,actual,middleValid,combinedReady,growth,childValid,childReady,childGrowth,
      by simp [SourceEqualityConstraintMemoAllocation.descend,Value.payload]⟩
  · obtain ⟨output,found⟩ := Option.ne_none_iff_exists.mp contradictory
    have actual := found.symm
    have covered := source_guard original (SourceEqualityGuardReadback.active field.1) raw extracted output actual
    obtain ⟨component,member,included⟩ := covered paths selected
    exact SourceCurrentInheritedOwnerProgress.selected_split original input before valid ready field component
      (by simpa only [actual,Option.getD_some] using member) index left right
      (included _ first) (included _ second) different

/-- Raw positive pairs separate their computed child obligation from every initially ready Top node key. -/
theorem key_ne_top (original : Field) (input : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : Ready before.constraints input)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (raw : Constraints) (extracted : SourceCompactGuards.positive original.guard = some raw)
    (paths : Class) (selected : paths ∈ raw)
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right)
    (identity : Nat) (top : Ready before.constraints (.live identity []))
    (value owner : InternedConstructorTemplates.Value (SourceObservations.Label FullSyntax.Formula) Field) :
    ∃ combined,
      (SourceCurrentAllocatedInheritedPrefix.run original input before).1 = .ok (some combined) ∧
      let middle := (SourceCurrentAllocatedInheritedPrefix.run original input before).2
      let child := SourceEqualityConstraintMemoAllocation.descend combined index middle
      (SourceCurrentAllocatedPartialState.NodeRequest.mk child.1 value).key ≠
        (SourceCurrentAllocatedPartialState.NodeRequest.mk (.live identity []) owner).key := by
  obtain ⟨combined,actual,_,_,prefixGrowth,childValid,childReady,childGrowth,nonempty⟩ :=
    field_split original input before valid ready field raw extracted paths selected
      index left right first second different
  exact ⟨combined,actual,SourceCurrentInheritedOwnerProgress.node_key_ne_top _ _ childValid
    (SourceCurrentConjunctionEquality.grows_trans prefixGrowth childGrowth) _ childReady nonempty
    identity top value owner⟩

end MicroCFTA.SourceCurrentPositiveClassOrigins
