import MicroCFTA.SourceEqualityClassOrder

/-!
# Source equality-reduction guards before class ordering

None represents EqContradiction. Some records represents the physical class
payload; its native interned identity is not read by these branches. The
existing terminating normalizer supplies actual finite combined constraints.
-/
namespace MicroCFTA.SourceEqualityPrecheck
open EqualityNormalize SourceEqualityClassOrder

/-- Source constraint payloads distinguish contradiction from a noncontradictory class list. -/
abbrev Constraint := Option (List Record)

/-- The EmptyConstraints pattern reads the class payload, before normalization. -/
def isEmpty : Constraint → Bool
  | some [] => true
  | _ => false

/-- Combine source constraints with contradiction absorption and the exact empty fast path. -/
def combine : Constraint → Constraint → RunResult
  | none, _ => .contradiction
  | _, none => .contradiction
  | some [], some [] => .normalized []
  | some first, some second =>
      let classes := first.map Record.paths ++ second.map Record.paths
      mkEqConstraints (EqualityTermination.normalizationBound classes) classes

/-- The source combined-contradiction test reads only the completed result tag. -/
def rejects : RunResult → Bool
  | .contradiction => true
  | _ => false

/-- A complete physical constraint payload denotes its path equalities; contradiction denotes no term. -/
def Sat (term : Language.Term Symbol) : Constraint → Prop
  | none => False
  | some records => Satisfies term (records.map Record.paths)

/-- Combined source normalization always completes; no successful normalization premise is supplied. -/
theorem combine_complete (first second : Constraint) : combine first second ≠ .timeout := by
  cases first with
  | none => simp [combine]
  | some first =>
      cases second with
      | none => simp [combine]
      | some second =>
          cases first <;> cases second <;>
            first | simp only [combine]; exact EqualityTermination.mkEqConstraints_terminates _ | simp [combine]

/-- The completed combined guard has exactly the conjunction of both source constraint meanings. -/
theorem combine_exact (first second : Constraint) (term : Language.Term Symbol) :
    RunSat term (combine first second) ↔ Sat term first ∧ Sat term second := by
  cases first with
  | none => simp [combine, Sat, RunSat]
  | some first =>
      cases second with
      | none => simp [combine, Sat, RunSat]
      | some second =>
          have normalized := EqualityTermination.mkEqConstraints_total_correct term (first.map Record.paths ++ second.map Record.paths)
          cases first <;> cases second
          · simp [combine, Sat, RunSat, Satisfies]
          all_goals simpa [combine, Sat, Satisfies, or_imp, forall_and, and_assoc] using normalized

/-- The checked counterpart of the source unsafe ordered-class accessor retains its exact failure. -/
def unsafeOrdered : Constraint → Except String (List Record)
  | none => .error "unsafeSubsumptionOrderedEclasses: unexpected EqContradiction"
  | some records => .ok (ordered records)

/-- The source guards either return immediately or provide the ordered physical classes for selection. -/
inductive Branch where
  | unchanged
  | emptyChildren
  | classes (records : List Record)

/-- Execute source empty and combined-contradiction guards before the unsafe ordering call. -/
def precheck (own inherited : Constraint) : Except String Branch :=
  if isEmpty own && isEmpty inherited then .ok .unchanged
  else if rejects (combine own inherited) then .ok .emptyChildren
  else (unsafeOrdered own).map Branch.classes

/-- Execute the actual source parent-array normalizer in the nontrivial combined-constraint branch. -/
def combineArray (work : Nat) : Constraint → Constraint → RunResult
  | none, _ => .contradiction
  | _, none => .contradiction
  | some [], some [] => .normalized []
  | some first, some second =>
      let classes := first.map Record.paths ++ second.map Record.paths
      EqualityIndex.normalizeArray (EqualityTermination.normalizationBound classes) work classes

/-- The actual finite source array schedule agrees with combined constraints at every sufficient work bound. -/
theorem combineArray_eventual (own inherited : Constraint) :
    ∃ bound, ∀ work, bound ≤ work → combineArray work own inherited = combine own inherited := by
  cases own with
  | none => exact ⟨0, by intros; rfl⟩
  | some first =>
      cases inherited with
      | none => exact ⟨0, by intros; rfl⟩
      | some second =>
          let classes := first.map Record.paths ++ second.map Record.paths
          obtain ⟨bound, agrees⟩ := EqualityIndex.normalizeArray_eventual (EqualityTermination.normalizationBound classes) classes
          refine ⟨bound, ?_⟩
          intro work enough
          cases first <;> cases second
          · rfl
          all_goals simpa only [combineArray, combine, classes] using agrees work enough

/-- Execute the source guards with the actual bounded parent-array normalization calls. -/
def precheckArray (work : Nat) (own inherited : Constraint) : Except String Branch :=
  if isEmpty own && isEmpty inherited then .ok .unchanged
  else if rejects (combineArray work own inherited) then .ok .emptyChildren
  else (unsafeOrdered own).map Branch.classes

/-- Sufficient actual array work gives the exact complete source branch, including ordering and errors. -/
theorem precheckArray_eventual (own inherited : Constraint) :
    ∃ bound, ∀ work, bound ≤ work → precheckArray work own inherited = precheck own inherited := by
  obtain ⟨bound, agrees⟩ := combineArray_eventual own inherited
  exact ⟨bound, fun work enough => by simp only [precheckArray, precheck, agrees work enough]⟩

/-- Every source precheck avoids the unsafe accessor failure. -/
theorem precheck_safe (own inherited : Constraint) : ∃ branch, precheck own inherited = .ok branch := by
  unfold precheck
  split
  · exact ⟨.unchanged, rfl⟩
  · split
    · exact ⟨.emptyChildren, rfl⟩
    · rename_i clear
      cases own with
      | none => simp [combine, rejects] at clear
      | some records => exact ⟨.classes (ordered records), rfl⟩

/-- Empty own and inherited source payloads return before normalization or sorting. -/
theorem empty_precheck : precheck (some []) (some []) = .ok .unchanged := rfl

/-- An originally contradictory own payload returns empty children before class ordering. -/
theorem local_contradiction (inherited : Constraint) : precheck none inherited = .ok .emptyChildren := by
  simp [precheck, isEmpty, combine, rejects]

/-- An originally contradictory inherited payload returns empty children before class ordering. -/
theorem inherited_contradiction (own : Constraint) : precheck own none = .ok .emptyChildren := by
  cases own with
  | none => rfl
  | some records => cases records <;> simp [precheck, isEmpty, combine, rejects]

/-- A live class-order branch reads exactly a noncontradictory original own payload. -/
theorem live_payload (own inherited : Constraint) (records : List Record)
    (live : precheck own inherited = .ok (.classes records)) :
    ∃ original, own = some original ∧ records = ordered original ∧ rejects (combine own inherited) = false := by
  unfold precheck at live
  split at live
  · cases live
  · split at live
    · cases live
    · rename_i clear
      cases own with
      | none => simp [combine, rejects] at clear
      | some original =>
          have same : ordered original = records := by simpa only [unsafeOrdered, Except.map, Except.ok.injEq, Branch.classes.injEq] using live
          exact ⟨original, rfl, same.symm, Bool.eq_false_iff.mpr clear⟩

end MicroCFTA.SourceEqualityPrecheck
