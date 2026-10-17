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
        simpa only [SourceCompactGuards.positiveNormalized,if_pos different,Option.some.injEq] using actual
      exact SourceCurrentOuterOriginDependencies.normalize_covers _ _ finished
        (SourceCompactGuards.positive_active (.same left right : Guard) _
          (by simp only [SourceCompactGuards.positive,if_pos different]))
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
      simpa only [SourceCompactGuards.positiveNormalizedList,leftDone,rightDone,
        Option.bind_some,Option.some.injEq] using actual
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
    simp only [SourceCompactGuards.sourceEqualities,found,SourceCompactGuards.combineEqualities] at actual
    cases original.equalities <;> cases actual
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
      cases own : original.equalities with
      | none => rw [own] at combined; cases combined
      | some own =>
        have retained := combine_covers own (head :: rest) output (stored own own)
          (active (head :: rest) rfl) (by simpa only [own] using combined)
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

end MicroCFTA.SourceCurrentPositiveClassOrigins
